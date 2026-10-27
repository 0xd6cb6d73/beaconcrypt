#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject drift in the exact E20 restriction/continuation premises."""

import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "name_order", Path(__file__).with_name("symbolic-name-order.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class NameOrderChecks(unittest.TestCase):
    def test_reviewed_complete_continuations(self):
        results = CHECKER.validate()
        self.assertEqual(set(results), set(CHECKER.MACROS))
        for name, result in results.items():
            text = (CHECKER.HERE / name).read_text()
            late = text.replace("new ephemeral_secret: bitstring;", "", 1).replace(
                "new kem_coins: bitstring;", "", 1
            )
            late = late.replace(
                "let (dh1: bitstring,",
                "new ephemeral_secret: bitstring; new kem_coins: bitstring; let (dh1: bitstring,",
                1,
            )
            parts = CHECKER.tokens(late)
            declaration = CHECKER.tokens(
                f"let {CHECKER.MACROS[name]}(obj: bitstring) ="
            )
            start = CHECKER.locate(parts, declaration) + len(declaration)
            self.assertEqual(result["late"], parts[start : parts.index(".", start)])
            self.assertGreater(len(result["continuation"]), 280)
            self.assertNotEqual(result["early_sha256"], result["late_sha256"])

    def test_classical_projection_scope_cannot_be_removed(self):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            (directory / "production-transcript-interface.pvl").write_text(
                "(* unreviewed full ML-DSA claim *)"
            )
            with self.assertRaisesRegex(ValueError, "classical-projection scope"):
                CHECKER.validate(directory=directory)

    def test_no_early_secret_use_or_shadowing(self):
        for name, macro in CHECKER.MACROS.items():
            text = (CHECKER.HERE / name).read_text()
            for needle, replacement in (
                ("in(c, bundle:", "in(ephemeral_secret, bundle:"),
                ("bundle: bitstring) [precise]", "kem_coins: bitstring) [precise]"),
                ("registration_id(init)", "registration_id(kem_coins)"),
            ):
                bad = text.replace(needle, replacement, 1)
                self.assertNotEqual(bad, text)
                with self.assertRaises(ValueError):
                    CHECKER.compare(bad, macro)

    def test_no_prefix_effect_or_extra_attempt(self):
        for name, macro in CHECKER.MACROS.items():
            text = (CHECKER.HERE / name).read_text()
            for inserted in (
                "out(c, ephemeral_secret);",
                "event Probe(kem_coins);",
                "out(c, bundle);",
                "new extra: bitstring;",
                "in(c, retry: bitstring);",
                "if bundle = bundle then",
            ):
                bad = text.replace(
                    "let signed_init_kex(", inserted + " let signed_init_kex(", 1
                )
                with self.assertRaises(ValueError):
                    CHECKER.compare(bad, macro)

    def test_local_unique_draws_and_source_order(self):
        for name, macro in CHECKER.MACROS.items():
            text = (CHECKER.HERE / name).read_text()
            for bad in (
                text.replace("new ephemeral_secret: bitstring;", "", 1),
                text.replace(
                    "new kem_coins: bitstring;", "new ephemeral_secret: bitstring;", 1
                ),
                text.replace(
                    "new kem_coins: bitstring;",
                    "new kem_coins: bitstring; new kem_coins: bitstring;",
                    1,
                ),
                text.replace(
                    "new ephemeral_secret: bitstring;", "new temporary: bitstring;", 1
                ),
            ):
                with self.assertRaises(ValueError):
                    CHECKER.compare(bad, macro)

    def test_whole_continuation_and_theory_changes_require_review(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name in CHECKER.TOKEN_SHA256:
                (directory / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE / name, directory / name)
            for name, before, after in (
                (
                    "extraction/lib.pvl",
                    "registration_identifier(identity, one_time)",
                    "registration_identifier(one_time, identity)",
                ),
                ("fs-records-s2b.pvl", "FsS2bTaskings(", "OmittedTail("),
                (
                    "fs-records-b2s.pvl",
                    "event FsServerCommitted(",
                    "event ChangedCommit(",
                ),
                ("crypto.pvl", "fun sign(", "fun changed_sign("),
            ):
                path = directory / name
                original = path.read_text()
                modified = original.replace(before, after, 1)
                self.assertTrue(
                    modified != original, "mutation did not match the expected source"
                )
                path.write_text(modified)
                with self.assertRaises(ValueError):
                    CHECKER.validate(directory)
                path.write_text(original)

    def test_source_generator_changes_require_review(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in CHECKER.SOURCE_SHA256:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((CHECKER.HERE.parents[2] / name).read_bytes())
            path = root / "beaconcrypt/src/pqxdh.rs"
            text = path.read_text()
            changed = text.replace(
                "server_ephemeral = crypto_kx::KeyPair::generate_with_rng(rng).ok();",
                "server_ephemeral = changed_generator();",
                1,
            )
            self.assertNotEqual(changed, text)
            path.write_text(changed)
            with self.assertRaises(ValueError):
                CHECKER.validate(source_root=root)

    def test_comments_do_not_change_the_checked_process(self):
        for name, macro in CHECKER.MACROS.items():
            text = (CHECKER.HERE / name).read_text()
            annotated = "(* Early names are symbolic only. *)\n" + text
            self.assertEqual(
                CHECKER.digest(CHECKER.tokens(text)),
                CHECKER.digest(CHECKER.tokens(annotated)),
            )
            self.assertEqual(
                CHECKER.compare(text, macro), CHECKER.compare(annotated, macro)
            )


if __name__ == "__main__":
    unittest.main()
