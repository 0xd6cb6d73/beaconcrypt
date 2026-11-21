#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the isolated exact-three source preparation."""

from pathlib import Path
import tempfile
import unittest

import prepare_adapter_record_helpers as preparation

ROOT = Path(__file__).resolve().parents[1]


class FixedThreePreparation(unittest.TestCase):
    def test_exact_original_prefix_and_three_ordered_operations(self):
        for index, name in enumerate(preparation.SOURCES):
            original = (ROOT / name).read_text()
            result, proof = preparation.transform(original, index)
            self.assertEqual(result, original + "\n" + proof["helper"])
            self.assertEqual(proof["fold_order"], [0, 1, 2])
            helper = proof["helper"]
            self.assertEqual(helper.count(".checked_add("), 3)
            self.assertEqual(helper.count(".try_reserve_exact("), int(index == 0))
            self.assertLess(
                helper.index("parts[0].len()"), helper.index("parts[1].len()")
            )
            self.assertLess(
                helper.index("parts[1].len()"), helper.index("parts[2].len()")
            )
            if index == 0:
                for part in range(3):
                    self.assertEqual(
                        helper.count(f"output.extend_from_slice(parts[{part}]);"), 1
                    )
            else:
                self.assertIn(
                    "encode_frame_parts(sequence, sender, &parts, output)", helper
                )

    def test_reject_changed_original_body(self):
        mutations = (
            (0, "length.checked_add(part.len())", "length.wrapping_add(part.len())"),
            (0, "output.extend_from_slice(part)", "output.clear()"),
            (0, "output.try_reserve_exact(length)", "output.try_reserve(length)"),
            (
                1,
                "encode_frame_parts(sequence, sender, parts, output)",
                "encode_frame_parts(sender, sequence, parts, output)",
            ),
        )
        for index, before, after in mutations:
            with self.subTest(before=before):
                source = (ROOT / preparation.SOURCES[index]).read_text()
                changed = source.replace(before, after, 1)
                self.assertNotEqual(source, changed)
                with self.assertRaises(ValueError):
                    preparation.transform(changed, index)

    def test_certificate_covers_original_generated_rust(self):
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

    def fixture(self, change=None):
        with tempfile.TemporaryDirectory(
            prefix="bc-helper-preparation-control-"
        ) as directory:
            destination = Path(directory) / "source"
            proof = preparation.prepare(ROOT, destination)
            preparation.check_fixture(ROOT, destination, proof)
            if change:
                change(destination, proof)
                with self.assertRaises(ValueError):
                    preparation.check_fixture(ROOT, destination, proof)

    def test_complete_preparation(self):
        self.fixture()

    def test_reject_extra_fixture_file(self):
        self.fixture(lambda destination, _: (destination / "extra.rs").write_text(""))

    def test_reject_modified_generated_rust(self):
        def change(destination, proof):
            name = next(
                name
                for name in proof["unchanged_sha256"]
                if name.startswith("beaconcrypt-parse/src/generated/")
                and name.endswith(".rs")
            )
            (destination / name).write_text("// edited generated parser\n")

        self.fixture(change)

    def test_reject_changed_helper_order(self):
        def change(destination, _):
            path = destination / preparation.SOURCES[0]
            path.write_text(
                path.read_text().replace(
                    "output.extend_from_slice(parts[0]);",
                    "output.extend_from_slice(parts[2]);",
                    1,
                )
            )

        self.fixture(change)

    def test_reject_tampered_certificate(self):
        def change(_, proof):
            proof["source_changes"][preparation.SOURCES[0]]["fold_order"] = [2, 1, 0]

        self.fixture(change)

    def test_reject_existing_fixture_without_mutating(self):
        with tempfile.TemporaryDirectory(prefix="bc-helper-existing-") as directory:
            destination = Path(directory)
            marker = destination / "preserve"
            marker.write_bytes(b"original")
            with self.assertRaises(ValueError):
                preparation.prepare(ROOT, destination)
            self.assertEqual(marker.read_bytes(), b"original")
            self.assertEqual(list(destination.iterdir()), [marker])

    def test_reject_repo_and_ancestor_destinations(self):
        for destination in (ROOT, ROOT / "var/forbidden-helper-source", ROOT.parent):
            with self.assertRaises(ValueError):
                preparation.prepare(ROOT, destination)

    def test_reject_symbolic_fixture(self):
        with tempfile.TemporaryDirectory(prefix="bc-helper-symlink-") as directory:
            root = Path(directory)
            link = root / "link"
            link.symlink_to(root / "missing", target_is_directory=True)
            with self.assertRaises(ValueError):
                preparation.prepare(ROOT, link)
            self.assertFalse((root / "missing").exists())

    def test_reject_symbolic_source(self):
        with tempfile.TemporaryDirectory(prefix="bc-helper-source-link-") as directory:
            root = Path(directory)
            (root / "Cargo.toml").symlink_to(ROOT / "Cargo.toml")
            with self.assertRaises(ValueError):
                preparation.source_files(root)


if __name__ == "__main__":
    unittest.main()
