#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check finite syntax/output pins for the independently reviewed E3 argument.

This gate neither proves the arbitrary-derivation induction nor runs ProVerif.
The maintained guide states the exact C2/C3 transfer and its observation scope.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "pin_origin_terms", HERE / "registration-provenance-theory.py"
)
THEORY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(THEORY)

TOKEN_SHA256 = {
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
    "fs-registration-binding.pvl": "50b006405e0a98006e2f1ebabe854b466569beed15b7338d656557bf573a679c",
    "fs-records-b2s.pvl": "7fc2a35fefe9cfa0aa0e93a641b73523e8d1d2345baa55edf717772ad1bdaf3a",
    "fs-records-b2s-sends.pvl": "bdab11d7acec74c06cec4acf91cc0645f1d098a75725b2563cdc105cbf372a98",
    "fs-records-b2s-sends-chosen.pvl": "2c89ae654ea2a0ddf186a3538ae03688d707193661376bdd02e3daa8f0fb99aa",
    "fs-records-b2s-receive.pvl": "804737cf522cf20cb7f68f50f7680ba99357c87581e3d1f47f44ccb2cd6224d0",
    "fs-records-b2s-window.pvl": "b67656982edb0f39a44efa3c1697727004979ae6d110aee3c54ebde8af222fd5",
    "fs-records-b2s-kr3.pvl": "c7b3a5f09fcd1df8edf93cbf84b6822cfaedb5b27b3736dc52c61e2a176c3530",
    "fs-records-b2s-kr3-failstop.pvl": "6e45283247235adae143c77afe05a1d143a5c7fbdafee2c3a4f60f532372155b",
    "fs-records-b2s-c2.pv": "fa1f2ee79c252a2c8212889bd4a241ee24b34365c51c256d41a426a7f89bb4de",
    "fs-records-b2s-c3.pv": "513ac2d6a59822060c8bc9a3bca963a7ae952059e15d0548c5e2e1ef1c830564",
}

# These constructors have no data projections. Other declared functions may
# have projections, which the separate occurrence proof follows explicitly.
OPAQUE = {
    "hkdf_sha512_no_salt",
    "hkdf_first_32",
    "hkdf_second_32",
    "hkdf_final_12",
    "aead_cipher",
    "aead_tag",
    "blake2b512",
    "ed_public",
    "x25519_public",
    "sign",
    "ratchet_key_nonce",
}
NO_CREATED_RHS = {
    "hkdf_sha512_no_salt",
    "hkdf_first_32",
    "hkdf_second_32",
    "hkdf_final_12",
    "aead_cipher",
    "blake2b512",
}


def uncommented(text):
    return re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)


def digest(text):
    # Preserve identifiers, strings and compound operators as tokens; merely
    # removing whitespace would conflate identifiers or quoted payloads.
    pattern = r'"(?:\\.|[^"\\])*"|\(\*.*?\*\)|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|==>|<=>|<>|<=|>=|&&|\|\||<-|->|[^\s]'
    tokens = [
        match[0]
        for match in re.finditer(pattern, text, re.S)
        if not match[0].startswith("(*")
    ]
    return hashlib.sha256(
        json.dumps(tokens, separators=(",", ":")).encode()
    ).hexdigest()


def audit(directory=HERE):
    # The shared parser rejects equations and unsupported reduction syntax,
    # audits protected-variable flow and implicit data projections, and rejects
    # signing-producing rules. Run on exactly this proof's loaded theory.
    before = THEORY.FILES
    try:
        THEORY.FILES = tuple(TOKEN_SHA256)
        result = THEORY.audit(directory)
    finally:
        THEORY.FILES = before
    if len(result["reductions"]) != 28:
        raise ValueError("review changed E3 reduction inventory")
    declarations = {}
    for name in TOKEN_SHA256:
        text = uncommented((directory / name).read_text())
        for decl in re.finditer(
            r"\bfun\s+(\w+)\s*\(([^()]*)\)\s*:\s*(\w+)(?:\s*\[([^\]]*)\])?\.?",
            text,
        ):
            if decl[1] in declarations:
                raise ValueError("duplicate function declaration: " + decl[1])
            declarations[decl[1]] = set(re.findall(r"\w+", decl[4] or ""))
        for rule in re.finditer(r"\breduc\s+(.*?)\.", text, flags=re.S):
            rhs = rule[1].split("=", 1)[1]
            if THEORY.symbols(THEORY.term(rhs)) & NO_CREATED_RHS:
                raise ValueError("a rule creates an E3 KDF/cipher/commitment term")
    if not OPAQUE <= declarations.keys():
        raise ValueError("missing E3 opaque constructor")
    if any("data" in declarations[name] for name in OPAQUE):
        raise ValueError("an E3 opaque constructor has a data projection")
    if "private" not in declarations.get("x25519_shared", set()):
        raise ValueError("the DH shared constructor must remain private")
    if "data" not in declarations.get("ctx_preimage", set()):
        raise ValueError("review changed explicit commitment-preimage projection")
    return result


def validate(directory=HERE):
    for name, wanted in TOKEN_SHA256.items():
        if digest((directory / name).read_text()) != wanted:
            raise ValueError("review changed E3 process/theory/query: " + name)
    return audit(directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.parse_args()
    result = validate()
    print(
        "Pin-origin argument inputs: 14 files, 28 reductions, "
        f"{len(result['data_constructors'])} data constructors; "
        "scoped paper C2/C3 transfer, no new solver verdict."
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError, OSError) as error:
        print("pin-origin check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
