#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the two-part plaintext source specialization."""

from pathlib import Path
import tempfile
import unittest

import prepare_adapter_seal_join as preparation

ROOT = Path(__file__).resolve().parents[1]


class SealJoinPreparation(unittest.TestCase):
    def test_original_prefix_and_literal_two_order(self):
        source = (ROOT / preparation.SOURCE).read_text()
        prepared, proof = preparation.transform(source)
        self.assertEqual(prepared, source + "\n" + proof["helper"])
        self.assertEqual(proof["fold_order"], [0, 1])
        self.assertEqual(proof["part_count"], 2)
        helper = proof["helper"]
        self.assertEqual(helper.count(".checked_add("), 2)
        self.assertEqual(helper.count(".try_reserve_exact("), 1)
        self.assertEqual(helper.count(".extend_from_slice("), 2)
        self.assertLess(helper.index("parts[0].len()"), helper.index("parts[1].len()"))
        self.assertLess(
            helper.index("try_reserve_exact"), helper.index("extend_from_slice")
        )
        self.assertLess(
            helper.index("extend_from_slice(parts[0])"),
            helper.index("extend_from_slice(parts[1])"),
        )

    def test_reject_original_source_drift(self):
        source = (ROOT / preparation.SOURCE).read_text()
        for before, after in (
            ("length.checked_add(part.len())", "length.wrapping_add(part.len())"),
            ("output.try_reserve_exact(length)", "output.try_reserve(length)"),
            ("output.extend_from_slice(part)", "output.clear()"),
        ):
            with self.subTest(before=before):
                changed = source.replace(before, after, 1)
                self.assertNotEqual(source, changed)
                with self.assertRaises(ValueError):
                    preparation.transform(changed)

    def test_reject_duplicate_original_declaration(self):
        source = (ROOT / preparation.SOURCE).read_text()
        with self.assertRaises(ValueError):
            preparation.transform(source + "\n" + preparation.MARKER)

    def test_certificate_preserves_entire_original_seal_dispatcher(self):
        proof = preparation.certificate(ROOT)
        changed = proof["source_changes"][preparation.SOURCE]
        self.assertEqual(
            changed["source_sha256"],
            preparation.digest((ROOT / preparation.SOURCE).read_bytes()),
        )
        helper = changed["helper"]
        self.assertNotIn("execute_seal_request", helper)
        self.assertNotIn("encrypt_detached", helper)
        self.assertNotIn("Zeroizing", helper)

    def test_certificate_preserves_generated_cbor(self):
        proof = preparation.certificate(ROOT)
        generated = [
            name
            for name in proof["unchanged_sha256"]
            if name.startswith("beaconcrypt-parse/src/generated/")
            and name.endswith(".rs")
        ]
        self.assertTrue(generated)
        for name in generated:
            self.assertEqual(
                proof["unchanged_sha256"][name],
                preparation.digest((ROOT / name).read_bytes()),
            )

    def fixture(self, mutate=None):
        with tempfile.TemporaryDirectory(prefix="bc-seal-join-control-") as directory:
            fixture = Path(directory) / "source"
            proof = preparation.prepare(ROOT, fixture)
            preparation.check_fixture(ROOT, fixture, proof)
            if mutate:
                mutate(fixture, proof)
                with self.assertRaises(ValueError):
                    preparation.check_fixture(ROOT, fixture, proof)

    def test_full_fixture(self):
        self.fixture()

    def test_reject_helper_order_drift(self):
        def mutate(fixture, _):
            path = fixture / preparation.SOURCE
            path.write_text(
                path.read_text().replace(
                    "output.extend_from_slice(parts[0]);",
                    "output.extend_from_slice(parts[1]);",
                    1,
                )
            )

        self.fixture(mutate)

    def test_reject_changed_original_seal_dispatcher_in_fixture(self):
        def mutate(fixture, _):
            path = fixture / preparation.SOURCE
            path.write_text(
                path.read_text().replace(
                    "pub(crate) fn execute_seal_request(",
                    "pub(crate) fn changed_seal_request(",
                    1,
                )
            )

        self.fixture(mutate)

    def test_reject_extra_fixture_file(self):
        self.fixture(lambda fixture, _: (fixture / "extra.rs").write_text(""))

    def test_reject_tampered_certificate(self):
        def mutate(_, proof):
            proof["source_changes"][preparation.SOURCE]["fold_order"] = [1, 0]

        self.fixture(mutate)

    def test_reject_existing_and_internal_fixtures(self):
        for destination in (ROOT, ROOT.parent, ROOT / "var/forbidden-seal-join"):
            with self.assertRaises(ValueError):
                preparation.prepare(ROOT, destination)
        with tempfile.TemporaryDirectory(prefix="bc-seal-existing-") as directory:
            destination = Path(directory)
            marker = destination / "preserve"
            marker.write_bytes(b"sentinel")
            with self.assertRaises(ValueError):
                preparation.prepare(ROOT, destination)
            self.assertEqual(marker.read_bytes(), b"sentinel")
            self.assertEqual(list(destination.iterdir()), [marker])

    def test_reject_symbolic_fixture(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-symlink-") as directory:
            root = Path(directory)
            link = root / "link"
            link.symlink_to(root / "missing", target_is_directory=True)
            with self.assertRaises(ValueError):
                preparation.prepare(ROOT, link)
            self.assertFalse((root / "missing").exists())


if __name__ == "__main__":
    unittest.main()
