#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject changes to the finite premises of the separate E3 paper argument."""

import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "pin_origin_checker", Path(__file__).with_name("pin-origin-theory.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class PinOriginChecks(unittest.TestCase):
    def mutate(self, filename, old, new, *, syntax_only=False):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for name in CHECKER.TOKEN_SHA256:
                target = directory / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE / name, target)
            path = directory / filename
            text = path.read_text()
            self.assertEqual(text.count(old), 1)
            path.write_text(text.replace(old, new, 1))
            # Syntax-only cases bypass the hash pins and exercise the parser.
            with self.assertRaises(ValueError):
                (CHECKER.audit if syntax_only else CHECKER.validate)(directory)

    def test_exact_input_and_rule_inventory(self):
        result = CHECKER.validate()
        self.assertEqual(len(result["files"]), 14)
        self.assertEqual(len(result["reductions"]), 28)
        self.assertEqual(len(result["data_constructors"]), 36)

    def test_comments_and_spacing_do_not_change_tokens(self):
        self.assertEqual(
            CHECKER.digest("fun f()."), CHECKER.digest("(* note *) fun  f ( ) .")
        )

    def test_identifier_and_literal_tokens_remain_distinct(self):
        for left, right in (
            ("fun name", "funname"),
            ('"a b"', '"ab"'),
            ('"(* a *)"', '""'),
            ("x ==> y", "x = = > y"),
        ):
            self.assertNotEqual(CHECKER.digest(left), CHECKER.digest(right))

    def test_every_process_query_and_theory_is_pinned(self):
        for name in CHECKER.TOKEN_SHA256:
            with self.subTest(file=name):
                with tempfile.TemporaryDirectory() as scratch:
                    directory = Path(scratch)
                    for source in CHECKER.TOKEN_SHA256:
                        target = directory / source
                        target.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy(CHECKER.HERE / source, target)
                    with (directory / name).open("a") as stream:
                        stream.write("\nout(public_channel, extra_secret)\n")
                    with self.assertRaisesRegex(
                        ValueError, "review changed E3 process/theory/query"
                    ):
                        CHECKER.validate(directory)

    def test_each_opaque_constructor_rejects_data_projection(self):
        import re

        for name in sorted(CHECKER.OPAQUE):
            matches = []
            for source in CHECKER.TOKEN_SHA256:
                text = (CHECKER.HERE / source).read_text()
                match = re.search(r"fun " + name + r"\([^()]*\): \w+\.", text)
                if match:
                    matches.append((source, match[0]))
            self.assertEqual(len(matches), 1, name)
            source, declaration = matches[0]
            with self.subTest(constructor=name):
                self.mutate(
                    source, declaration, declaration[:-1] + " [data].", syntax_only=True
                )

    def test_shared_constructor_must_remain_private(self):
        self.mutate(
            "crypto.pvl",
            "fun x25519_shared(bitstring, bitstring): bitstring [private].",
            "fun x25519_shared(bitstring, bitstring): bitstring.",
            syntax_only=True,
        )

    def test_commitment_preimage_projection_is_explicit(self):
        self.mutate(
            "production-transcript-interface.pvl",
            "fun ctx_preimage(\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring\n): bitstring [data].",
            "fun ctx_preimage(\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring,\n  bitstring\n): bitstring.",
            syntax_only=True,
        )

    def test_existing_rule_cannot_create_cipher_hash_or_kdf(self):
        # Replacing an existing RHS keeps the count at 28, so the actual
        # constructor-creation check must reject the change.
        for rhs in (
            "aead_cipher(key,key,key,key)",
            "blake2b512(key)",
            "hkdf_first_32(key)",
        ):
            with self.subTest(rhs=rhs):
                self.mutate(
                    "crypto.pvl",
                    "material_key(ratchet_key_nonce(key, nonce)) = key.",
                    "material_key(ratchet_key_nonce(key, nonce)) = " + rhs + ".",
                    syntax_only=True,
                )

    def test_equations_require_independent_analysis(self):
        self.mutate(
            "crypto.pvl",
            "fun ed_public(bitstring): bitstring.",
            "fun ed_public(bitstring): bitstring.\nequation forall k: bitstring; ed_public(k) = k.",
            syntax_only=True,
        )

    def test_protected_seed_cannot_be_projected(self):
        self.mutate(
            "crypto.pvl",
            "fun ed_public(bitstring): bitstring.",
            "fun ed_public(bitstring): bitstring.\nreduc forall k: bitstring; reveal(ed_public(k)) = k.",
            syntax_only=True,
        )

    def test_shared_parser_file_set_is_restored(self):
        before = CHECKER.THEORY.FILES
        CHECKER.validate()
        self.assertEqual(CHECKER.THEORY.FILES, before)


if __name__ == "__main__":
    unittest.main()
