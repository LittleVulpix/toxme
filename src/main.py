#!/usr/bin/env python3
"""
* yuu.py
* Author: stal, stqism; April 2014
* Copyright (c) 2015 Project ToxMe
* Further licensing information: see LICENSE.
"""
import tornado.ioloop
import tornado.httpserver
import tornado.web
import tornado.log
import os
import json
import nacl.public as public
import nacl.signing as signing
import nacl.encoding
import nacl.exceptions
import database
import datetime
import time
import logging
import re
import pwd
import grp
import sys
import random
import hashlib
import urllib.parse as parse
from collections import Counter, defaultdict
import base64
import binascii

import error_codes
import barcode

tornado.log.enable_pretty_logging()
LOGGER = logging.getLogger("toxme")

ACTION_PUBLISH   = 1
ACTION_UNPUBLISH = 2
ACTION_LOOKUP    = 3
ACTION_STATUS    = 4
ACTION_RLOOKUP    = 5
ACTION_SEARCH     = 6
INVOKABLE_ACTIONS = {ACTION_PUBLISH, ACTION_UNPUBLISH, ACTION_LOOKUP,
                     ACTION_STATUS, ACTION_RLOOKUP, ACTION_SEARCH}
THROTTLE_THRESHOLD = 13

VALID_KEY = re.compile(r"^[A-Fa-f0-9]{64}$")
VALID_ID  = re.compile(r"^[A-Fa-f0-9]{76}$")
REMOVE_NEWLINES = re.compile("[\r\n]+")
DISALLOWED_CHARS = set(" @/:;()\"'")
DISALLOWED_NAMES = {}
NAME_LIMIT_HARD  = 63
BIO_LIMIT        = 1372 # fixme this should be configurable || hue hue

ENTRIES_PER_PAGE = 30
ENTRIES_PER_SEARCH = 30

SIGNSTATUS_GOOD      = 1
SIGNSTATUS_BAD       = 2
SIGNSTATUS_UNDECIDED = 3

SOURCE_LOCAL  = 1
SOURCE_REMOTE = 2

#pragma mark - crypto

SIGNATURE_ENC = nacl.encoding.Base64Encoder
KEY_ENC = nacl.encoding.HexEncoder
STORE_ENC = nacl.encoding.HexEncoder

SECURE_MODE = 1

class CryptoCore(object):
    def __init__(self):
        """Load or initialize crypto keys."""
        try:
            with open("key", "rb") as keys_file:
                keys = keys_file.read()
        except IOError:
            keys = None
        if keys:
            self.pkey = public.PrivateKey(keys, STORE_ENC)
            self.skey = signing.SigningKey(keys, STORE_ENC)
        else:
            kp = public.PrivateKey.generate()
            with open("key", "wb") as keys_file:
                keys_file.write(kp.encode(STORE_ENC))
            self.pkey = kp
            self.skey = signing.SigningKey(bytes(self.pkey),
                                           nacl.encoding.RawEncoder)

    def sign(self, uobj):
        e = nacl.encoding.HexEncoder
        pubkey = e.decode(uobj.public_key)
        pin = e.decode(uobj.pin) if uobj.pin else b""
        checksum = e.decode(uobj.checksum)
        name = uobj.name.encode("utf8")

        text = b"".join((name, pubkey, pin, checksum))
        return self.skey.sign(text, encoder=SIGNATURE_ENC).decode("utf8")

    @staticmethod
    def compute_checksum(data, iv=(0, 0)):
        e = nacl.encoding.HexEncoder
        checksum = list(iv)
        for ind, byte in enumerate(e.decode(data)):
            checksum[ind % 2] ^= byte
        return "".join(hex(byte)[2:].zfill(2) for byte in checksum).upper()

    @property
    def public_key(self):
        return self.pkey.public_key.encode(KEY_ENC).decode("utf8").upper()

    @property
    def verify_key(self):
        return self.skey.verify_key.encode(KEY_ENC).decode("utf8").upper()

    def dsrep_decode_name(self, client, nonce, pl):
        box = public.Box(self.pkey, public.PublicKey(client))
        by = box.decrypt(pl, nonce)
        return by

    def dsrec_encrypt_key(self, client, nonce, msg):
        box = public.Box(self.pkey, public.PublicKey(client))
        by = box.encrypt(msg, nonce)
        return by[24:]

#pragma mark - web

CONSONANTS = "bcdfghjklmnpqrstvwxyz"
VOWELS     = "aeiou"

def new_password():
    def sylfunc():
        rng = random.SystemRandom()
        return "".join([rng.choice(CONSONANTS), rng.choice(VOWELS),
                        rng.choice(CONSONANTS)])
    return "-".join(
        [sylfunc() for x in range(random.randint(4, 6))]
    )

class HTTPSPolicyEnforcer(tornado.web.RequestHandler):
    def _fail(self):
        self.set_status(400)
        self.write_secure(error_codes.ERROR_NOTSECURE)
        return ""

    post = get = _fail


SIGNED_RANDOM_LENGTH = 64

class BaseAPIHandler(tornado.web.RequestHandler):

    def handle_envelope_hash(self, envelope):
        self.signed_hash = None
        if "memorabilia" in envelope and isinstance(envelope["memorabilia"], str):
            try:
                decoded = base64.b64decode(envelope["memorabilia"].encode('ascii'))
                LOGGER.info(len(decoded))
                if len(decoded) == SIGNED_RANDOM_LENGTH:
                    self.signed_hash = self.settings["crypto_core"].skey.sign(decoded)
                    LOGGER.info(self.signed_hash)
            except (ValueError, TypeError, KeyError, binascii.Error, nacl.exceptions.CryptoError):
                LOGGER.info("did fail request because random data was bad")

    def write_secure(self, chunk):
        new_chunk = chunk
        try:
            if isinstance(chunk, dict):
                new_chunk = chunk.copy()
                if self.signed_hash is not None:
                    new_chunk["signed_memorabilia"] = str(base64.b64encode(self.signed_hash), 'ascii')
                    self.signed_hash = None
        except AttributeError:
            LOGGER.info("did fail request because data was even worse")
        
        self.write(new_chunk)

class APIHandler(BaseAPIHandler):
    RETURNS_JSON = 1

    @staticmethod
    def _typecheck_dict(envelope, expect):
        for key, value in expect.items():
            if not isinstance(envelope.get(key), value):
                LOGGER.warn("typecheck failed on json")
                return 0
        return 1

    def _encrypted_payload_prologue(self, envelope):
        if not self._typecheck_dict(envelope, {"public_key": str, "nonce": str,
                                               "encrypted": str}):
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Unable to read payload")
            return
        try:
            other_key = public.PublicKey(envelope["public_key"], KEY_ENC)
        except nacl.exceptions.CryptoError:
            LOGGER.warn("did fail req because other pk was bad")
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            return

        box = public.Box(self.settings["crypto_core"].pkey, other_key)

        try:
            nonce = nacl.encoding.Base64Encoder.decode(envelope["nonce"])
            ciphertext = nacl.encoding.Base64Encoder.decode(envelope["encrypted"])
            clear = box.decrypt(ciphertext, nonce, nacl.encoding.RawEncoder)
        except (ValueError, TypeError, nacl.exceptions.CryptoError):
            LOGGER.warn("did fail req because a base64 value was bad")
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            return

        try:
            clear = json.loads(clear.decode("utf8"))
        except (UnicodeDecodeError, TypeError):
            LOGGER.warn("did fail req because inner json decode failed")
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            return
        return clear

    def json_payload(self, payload):
        if self.RETURNS_JSON:
            self.write_secure(payload)
        else:
            self.render("api_error_pretty.html", payload=payload,
                        f=error_codes.DESCRIPTIONS[payload["c"]])

    def update_db_entry(self, auth, name, pub, bio, check, privacy, pin=None,
                        password=None):
        dbc = self.settings["local_store"]
        with dbc.lock:
            session, owner_of_cid = dbc.get_by_id_ig(pub)
            if owner_of_cid and owner_of_cid.name != name:
                session.close()
                self.set_status(400)
                self.json_payload(error_codes.ERROR_DUPE_ID)
                return 0

            session, mus = dbc.get_ig(name, session)
            if not mus:
                mus = database.User()
            elif mus.public_key != auth:
                session.close()
                self.set_status(400)
                self.json_payload(error_codes.ERROR_NAME_TAKEN)
                return 0

            mus.name = name
            mus.public_key = pub
            mus.checksum = check
            mus.privacy = privacy
            mus.timestamp = datetime.datetime.now()
            mus.sig = self.settings["crypto_core"].sign(mus)
            mus.bio = bio
            mus.pin = pin
            if password:
                mus.password = password
            ok = dbc.update_atomic(mus, session)
            if not ok:
                session.close()
                self.set_status(400)
                self.json_payload(error_codes.ERROR_DUPE_ID)
                return 0
            session.close()
        return 1

class APIUpdateName(APIHandler):
    def initialize(self, envelope):
        self.envelope = envelope
        self.handle_envelope_hash(envelope)

    def post(self):
        if self.settings["address_ctr"]:
            ctr = self.settings["address_ctr"][ACTION_PUBLISH]
            if ctr["clear_date"][self.request.remote_ip] < time.time():
                del ctr["counter"][self.request.remote_ip]
                del ctr["clear_date"][self.request.remote_ip]
            ctr["counter"][self.request.remote_ip] += 1
            # Clears in one hour
            ctr["clear_date"][self.request.remote_ip] = time.time() + 3600

            if ctr["counter"][self.request.remote_ip] > THROTTLE_THRESHOLD:
                self.set_status(400)
                self.write_secure(error_codes.ERROR_RATE_LIMIT)
                return

        clear = self._encrypted_payload_prologue(self.envelope)
        if not clear:
            return

        if not self._typecheck_dict(clear, {"tox_id": str, "name": str,
                                            "timestamp": int, "privacy": int,
                                            "bio": str}):
            self.set_status(400)
            self.write_secure(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("encrypted payload incorrect")
            return

        auth = self.envelope["public_key"].upper()
        id_ = clear["tox_id"].upper()
        name = clear["name"].lower()
        bio = REMOVE_NEWLINES.sub(" ", clear["bio"].strip())
        ctime = int(time.time())

        input_error = 0

        if (not VALID_ID.match(id_)
            or abs(ctime - clear["timestamp"]) > 300
            or len(name) > NAME_LIMIT_HARD
            or len(bio) > BIO_LIMIT):
            input_error = error_codes.ERROR_BAD_PAYLOAD
            LOGGER.warn("Size limit reached")

        if not set(name).isdisjoint(DISALLOWED_CHARS):
            input_error = error_codes.ERROR_INVALID_CHAR

        if name in DISALLOWED_NAMES:
            input_error = error_codes.ERROR_INVALID_NAME

        if input_error:
            self.set_status(400)
            self.json_payload(input_error)
            return

        pub, pin, check = id_[:64], id_[64:72], id_[72:]

        old_rec = self.settings["local_store"].get(name)
        if not old_rec:
            salt = os.urandom(16)
            password = new_password()
            hash_ = salt + hashlib.sha512(salt + password.encode("ascii")).digest()
        else:
            password = None
            hash_ = None

        if self.update_db_entry(auth, name, pub, bio, check,
                                max(clear["privacy"], 0), pin, hash_):
            ok = error_codes.ERROR_OK.copy()
            ok["password"] = password
            self.json_payload(ok)
        return

class APIReleaseName(APIHandler):
    def initialize(self, envelope):
        self.envelope = envelope
        self.handle_envelope_hash(envelope)

    def post(self):
        clear = self._encrypted_payload_prologue(self.envelope)
        if not clear:
            return

        ctime = int(time.time())
        pk = clear.get("public_key", "").upper()
        if (not VALID_KEY.match(pk)
            or abs(ctime - clear.get("timestamp", 0)) > 300):
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Invalid timestamp")
            return

        rec = self.settings["local_store"].get_by_id_ig(pk)[1]
        old = database.StaleUser(rec)
        self.settings["local_store"].delete_pk(pk)
        self.json_payload(error_codes.ERROR_OK)
        return

class APILookupID(BaseAPIHandler):
    def initialize(self, envelope):
        self.envelope = envelope
        self.handle_envelope_hash(envelope)

    def _results(self, result):
        self.set_status(200 if result["c"] == 0 else 400)
        self.write_secure(result)
        self.finish()

    def _build_local_result(self, name):
        rec = self.settings["local_store"].get(name)
        if not rec:
            return error_codes.ERROR_NO_USER
        base_ret = {
            "c": 0,
            "name": rec.name,
            "regdomain": self.settings["home"],
            "tox_id": rec.tox_id(),
            "url": "tox:{0}@{1}".format(rec.name, self.settings["home"]),
            "verify": {
                "status": SIGNSTATUS_GOOD,
                "detail": "Good (signed by local authority)",
            },
            "source": SOURCE_LOCAL,
            "version": "Tox V3 (local)"
        }
        return base_ret

    @tornado.web.asynchronous
    def post(self):
        name = self.envelope.get("name").lower()
        if not name or name.endswith("@") or name.startswith("@"):
            self.set_status(400)
            self.write_secure(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Name invalid")
            self.finish()
            return
        if "@" not in name:
            name = "@".join((name, self.settings["home"]))
        user, domain = name.rsplit("@", 1)
        if domain == self.settings["home"]:
            self._results(self._build_local_result(user))
            return
        else:
            LOGGER.warn("What (a) Terrible (dns-related) Failure")

class APILookupName(BaseAPIHandler):
    def initialize(self, envelope):
        self.envelope = envelope
        self.handle_envelope_hash(envelope)

    def _results(self, result):
        self.set_status(200 if result["c"] == 0 else 400)
        self.write_secure(result)
        self.finish()

    def _build_local_result(self, id):
        rec = self.settings["local_store"].get_by_id(id)
        if not rec:
            return error_codes.ERROR_NO_USER
        base_ret = {
            "c": 0,
            "name": rec.name,
        }
        return base_ret

    @tornado.web.asynchronous
    def post(self):
        id = self.envelope.get("id").lower()
        if not id:
            self.set_status(400)
            self.write_secure(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("ID unknown")
            self.finish()
            return
        else:
            if len(id) != 64:
                self.set_status(400)
                self.write_secure(error_codes.ERROR_INVALID_ID)
                LOGGER.warn("ID unknown")
                self.finish()
                return
            self._results(self._build_local_result(id))
            return

class APISearch(BaseAPIHandler):
    def initialize(self, envelope):
        self.envelope = envelope
        self.handle_envelope_hash(envelope)

    def _results(self, result):
        self.set_status(200 if result["c"] == 0 else 400)
        self.write_secure(result)
        self.finish()

    def _build_local_result(self, name, page):
        users = self.settings["local_store"].search_users(name, ENTRIES_PER_SEARCH, page)
        base_ret = {
            "c": 0,
            "users": [{"name": user.name, "bio": user.bio} for user in users],
        }
        return base_ret

    @tornado.web.asynchronous
    def post(self):
        name = self.envelope.get("name").lower()
        page = self.envelope.get("page")

        if (type(page) is not int) or page < 0:
            self.set_status(400)
            self.write_secure(error_codes.ERROR_INVALID_CHAR)
            LOGGER.warn("Invalid page")
            self.finish()
            return

        if not name:
            self.set_status(400)
            self.write_secure(error_codes.ERROR_INVALID_NAME)
            LOGGER.warn("No name given")
            self.finish()
            return
        else:
            if len(name) > NAME_LIMIT_HARD:
                self.set_status(400)
                self.write_secure(error_codes.ERROR_INVALID_NAME)
                LOGGER.warn("Name too long")
                self.finish()
            self._results(self._build_local_result(name, page))
            return

class APIStatus(BaseAPIHandler):
    def initialize(self, envelope):
        self.envelope = envelope
        self.handle_envelope_hash(envelope)

    def _results(self, result):
        self.set_status(200 if result["c"] == 0 else 400)
        self.write_secure(result)
        self.finish()

    @staticmethod
    def fuzz(n):
        # rounds to hundreds after munging the count a bit
        n += random.randint(-100, 100)
        return max(0, n if not n % 100 else n + 100 - n % 100)

    @tornado.web.asynchronous
    def post(self):
        self._results({
            "c": 0,
            "ut": int(time.time()) - self.settings["app_startup"],
            "rs": self.fuzz(self.settings["local_store"].requests_serviced),
            "uc": self.fuzz(self.settings["local_store"].count_users()),
        })

class APIFailure(APIHandler):
    def get(self):
        self.set_status(400)
        self.json_payload(error_codes.ERROR_METHOD_UNSUPPORTED)
        return

    def post(self):
        self.set_status(400)
        self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
        return

def _make_handler_for_api_method(application, request, **kwargs):
    if SECURE_MODE:
        if request.protocol != "https":
            return HTTPSPolicyEnforcer(application, request, **kwargs)

    if request.method != "POST":
        return APIFailure(application, request, **kwargs)

    try:
        envelope = request.body.decode("utf8")
        envelope = json.loads(envelope)
        if envelope.get("action", -1) not in INVOKABLE_ACTIONS:
            raise TypeError("blah blah blah exceptions are flow control")
    except (UnicodeDecodeError, TypeError, ValueError):
        LOGGER.warn("failing request because of an invalid first payload")
        return APIFailure(application, request, **kwargs)

    action = envelope.get("action")
    if action == ACTION_PUBLISH:
        return APIUpdateName(application, request, envelope=envelope)
    elif action == ACTION_UNPUBLISH:
        return APIReleaseName(application, request, envelope=envelope)
    elif action == ACTION_LOOKUP:
        return APILookupID(application, request, envelope=envelope)
    elif action == ACTION_STATUS:
        return APIStatus(application, request, envelope=envelope)
    elif action == ACTION_RLOOKUP:
        return APILookupName(application, request, envelope=envelope)
    elif action == ACTION_SEARCH:
        return APISearch(application, request, envelope=envelope)

class PublicKey(BaseAPIHandler):
    def get(self):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.write_secure(error_codes.ERROR_NOTSECURE)
            else:
                self.write_secure({
                    "c": 0,
                    "key": self.settings["crypto_core"].public_key
                })
        else:
            self.write_secure({
                "c": 0,
                "key": self.settings["crypto_core"].public_key
            })


class CreateQR(BaseAPIHandler):
    def _fail(self):
        self.set_status(404)
        return

    def get(self, path_id):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.write_secure(error_codes.ERROR_NOTSECURE)
                return
        name = (parse.unquote(path_id) if path_id else "").lower()
        if not name or not set(name).isdisjoint(DISALLOWED_CHARS):
            return self._fail()
        rec = self.settings["local_store"].get(name)
        if not rec:
            return self._fail()

        self.set_header("Cache-Control", "public; max-age=86400")
        self.set_header("Content-Type", "image/svg+xml; charset=utf-8")
        self.write_secure(barcode.QRImage.get(self.settings["local_store"].get(name).tox_id()))
        return

class LookupAndOpenUser(BaseAPIHandler):
    def _user_id(self):
        spl = self.request.host.rsplit(".", 1)[0]
        if spl == self.request.host:
            return None
        else:
            return spl

    def _render_open_user(self, name):
        if not name or not set(name).isdisjoint(DISALLOWED_CHARS):
            self.set_status(404)
            self.render("fourohfour.html", record=name,
                        realm=self.settings["home"])
            return

        rec = self.settings["local_store"].get(name)
        if not rec:
            self.set_status(404)
            self.render("fourohfour.html", record=name,
                        realm=self.settings["home"])
            return

        self.render("onemomentplease.html", record=rec,
                    realm=self.settings["home"])

    def _lookup_home(self):
        self.render("lookup_home.html")

    def get(self, path_id=None):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.write_secure(error_codes.ERROR_NOTSECURE)
                return
        name = (parse.unquote(path_id) if path_id else "").lower()
        if name:
            return self._render_open_user(name)
        else:
            return self._lookup_home()

class FindFriends(BaseAPIHandler):
    def _render_page(self, num):
        num = int(num)
        results = self.settings["local_store"].get_page(num,
                                                        ENTRIES_PER_PAGE)
        if not results:
            self.set_status(404)
            self.render("fourohfour.html", record="",
                        realm=self.settings["home"])
            return
        self.render("public_userlist.html", results_set=results,
                    realm=self.settings["home"],
                    next_page=(None if len(results) < ENTRIES_PER_PAGE
                                    else num + 1),
                    previous_page=(num - 1) if num > 0 else None)

    def get(self, page):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.write_secure(error_codes.ERROR_NOTSECURE)
                return

        return self._render_page(page)

class EditKeyWeb(APIHandler):
    RETURNS_JSON = 0

    def get(self):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.json_payload(error_codes.ERROR_NOTSECURE)
                return
        self.render("edit_ui.html")

    def post(self):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.json_payload(error_codes.ERROR_NOTSECURE)
                return

        if self.settings["address_ctr"]:
            ctr = self.settings["address_ctr"][ACTION_PUBLISH]
            if ctr["clear_date"][self.request.remote_ip] < time.time():
                del ctr["counter"][self.request.remote_ip]
                del ctr["clear_date"][self.request.remote_ip]
            ctr["counter"][self.request.remote_ip] += 1
            # Clears in one hour
            ctr["clear_date"][self.request.remote_ip] = time.time() + 3600

            if ctr["counter"][self.request.remote_ip] > THROTTLE_THRESHOLD:
                self.set_status(400)
                self.json_payload(error_codes.ERROR_RATE_LIMIT)
                return

        name = self.get_body_argument("name", "").lower()
        password = self.get_body_argument("password", "").lower()
        rec = self.settings["local_store"].get(name)
        if not (rec and rec.is_password_matching(password)):
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PASSWORD)
            return

        action = self.get_body_argument("edit_action", "")
        if action not in {"Delete", "Update"}:
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Invalid action")
            return
        elif action == "Delete":
            self.settings["local_store"].delete_pk(rec.public_key)
            self.redirect("/friends/0")
            return

        bio = self.get_body_argument("bio", "") or rec.bio
        if len(bio) > BIO_LIMIT:
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("bio size over limit")
            return
        toxid = (self.get_body_argument("tox_id", "") or rec.tox_id()).upper()
        if not VALID_ID.match(toxid):
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Invalid checksum")
            return
        privacy = 0 if self.get_body_argument("privacy", "off") == "on" else 1
        lock = 1 if self.get_body_argument("lock", "off") == "on" else 0

        pkey = toxid[:64]
        pin = toxid[64:72]
        check = toxid[72:]
        if CryptoCore.compute_checksum("".join((pkey, pin))) != check:
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Invalid checksum")
            return

        if self.update_db_entry(rec.public_key, name, pkey, bio, check, privacy, pin):
            self.redirect("/friends/0")
        return

class AddKeyWeb(APIHandler):
    RETURNS_JSON = 0

    def get(self):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.json_payload(error_codes.ERROR_NOTSECURE)
                return
        self.render("add_ui.html")

    def post(self):
        if SECURE_MODE:
            if self.request.protocol != "https":
                self.json_payload(error_codes.ERROR_NOTSECURE)
                return

        if self.settings["address_ctr"]:
            ctr = self.settings["address_ctr"][ACTION_PUBLISH]
            if ctr["clear_date"][self.request.remote_ip] < time.time():
                del ctr["counter"][self.request.remote_ip]
                del ctr["clear_date"][self.request.remote_ip]
            ctr["counter"][self.request.remote_ip] += 1
            # Clears in one hour
            ctr["clear_date"][self.request.remote_ip] = time.time() + 3600

            if ctr["counter"][self.request.remote_ip] > THROTTLE_THRESHOLD:
                self.set_status(400)
                return

        name = self.get_body_argument("name", "").lower()
        if (not DISALLOWED_CHARS.isdisjoint(set(name))
            or name in DISALLOWED_NAMES):
            self.set_status(400)
            self.json_payload(error_codes.ERROR_INVALID_CHAR)
            return

        bio = self.get_body_argument("bio", "")
        if len(bio) > BIO_LIMIT:
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Missing bio")
            return

        toxid = self.get_body_argument("tox_id", "").upper()
        if not VALID_ID.match(toxid):
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("invalid Tox ID")
            return

        privacy = 0 if self.get_body_argument("privacy", "off") == "on" else 1
        lock = 1 if self.get_body_argument("lock", "off") == "on" else 0

        pkey = toxid[:64]
        pin = toxid[64:72]
        check = toxid[72:]
        if CryptoCore.compute_checksum("".join((pkey, pin))) != check:
            self.set_status(400)
            self.json_payload(error_codes.ERROR_BAD_PAYLOAD)
            LOGGER.warn("Checksum error")
            return

        old_rec = self.settings["local_store"].get(name)
        if not old_rec:
            if lock == 0:
                salt = os.urandom(16)
                password = new_password()
                hash_ = salt + hashlib.sha512(salt + password.encode("utf8")).digest()
            else:
                password = "None set"
                hash_ = None
        else:
            self.set_status(400)
            self.json_payload(error_codes.ERROR_NAME_TAKEN)
            return

        if self.update_db_entry(None, name, pkey, bio, check, privacy, pin,
                                hash_):
            self.render("addkeyweb_success.html", n=name, p=password,
                        regdomain=self.settings["home"])
        return

def main():
    global SECURE_MODE

    with open("config.json", "r") as config_file:
        cfg = json.load(config_file)

    try:
        SECURE_MODE = cfg["secure_mode"]
    except:
        SECURE_MODE = 1

    ioloop = tornado.ioloop.IOLoop.instance()
    crypto_core = CryptoCore()
    local_store = database.Database(cfg["database_url"])

    # an interesting object structure
    if cfg["sandbox"] == 0:
        address_ctr = {ACTION_PUBLISH: {"counter": Counter(),
                                        "clear_date": defaultdict(lambda: 0)}}
    else:
        LOGGER.info("Running in sandbox mode, limits are disabled.")
        address_ctr = None

    LOGGER.info("API public key: {0}".format(crypto_core.public_key))
    LOGGER.info("Record sign key: {0}".format(crypto_core.verify_key))

    templates_dir = "../templates/" + cfg["templates"]
    robots_path=os.path.join(os.path.dirname(__file__), "../static")
    handlers = [
        ("/api", _make_handler_for_api_method),
        ("/pk", PublicKey),
        (r"/barcode/(.+)\.svg$", CreateQR),
        (r"/u/(.+)?$", LookupAndOpenUser),
        (r"^/$", LookupAndOpenUser),
        (r"/add_ui", AddKeyWeb),
        (r"/edit_ui", EditKeyWeb),
        (r'/robots.txt', tornado.web.StaticFileHandler, {'path': robots_path})
    ]
    if cfg["findfriends_enabled"]:
        handlers.append((r"/friends/([0-9]+)$", FindFriends))
    app = tornado.web.Application(
        handlers,
        template_path=os.path.join(os.path.dirname(__file__), templates_dir),
        static_path=os.path.join(os.path.dirname(__file__), "../static"),
        crypto_core=crypto_core,
        local_store=local_store,
        address_ctr=address_ctr,
        hooks_state=None,
        app_startup=int(time.time()),
        home=cfg["registration_domain"],
    )
    server = tornado.httpserver.HTTPServer(app, **{
        "ssl_options": cfg.get("ssl_options"),
        "xheaders": cfg.get("is_proxied")
    })
    server.listen(cfg["server_port"], cfg["server_addr"])

    if "suid" in cfg:
        LOGGER.info("Descending...")
        if os.getuid() == 0:
            if ":" not in cfg["suid"]:
                user = cfg["suid"]
                group = None
            else:
                user, group = cfg["suid"].split(":", 1)
            uid = pwd.getpwnam(user).pw_uid
            if group:
                gid = grp.getgrnam(group).gr_gid
            else:
                gid = pwd.getpwnam(user).pw_gid
            os.setgid(gid)
            os.setuid(uid)
            LOGGER.info("Continuing.")
        else:
            LOGGER.info("suid key exists in config, but not running as root. "
                        "Exiting.")
            sys.exit()

    if "secure" in cfg:
        opt = cfg['secure']

        if type(opt) != int:
            LOGGER.info("Invalid secure mode option")
            sys.exit()
        else:
            SECURE_MODE = opt
    LOGGER.info("secure mode is " + str(SECURE_MODE))

    local_store.late_init()

    if "pid_file" in cfg:
        with open(cfg["pid_file"], "w") as pid:
            pid.write(str(os.getpid()))
    LOGGER.info("Notice: listening on {0}:{1}".format(
        cfg["server_addr"], cfg["server_port"]
    ))

    try:
        ioloop.start()
    finally:
        os.remove(cfg["pid_file"])

if __name__ == "__main__":
    main()
