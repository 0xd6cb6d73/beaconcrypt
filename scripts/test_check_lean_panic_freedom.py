#!/usr/bin/env python3
"""Regression checks for omissions at the extracted panic-freedom boundary."""

from pathlib import Path
import shutil
import tempfile
import unittest

import check_lean_panic_freedom as checker


class PanicBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.source = "def f (x : Nat) : RustM Nat := ok x\n"
        self.certificate = {
            "f": {"module": "Proof", "theorem": "Proof.f_total", "form": "exists"}
        }

    def test_ideal_model_changes_are_rejected(self):
        source = Path(__file__).resolve().parents[1] / "beaconcrypt-core/proofs/lean"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "BeaconcryptCore/Model"
            shutil.copytree(source / "BeaconcryptCore/Model", target)
            checker.check_models(root)
            added = target / "Unreviewed.lean"
            added.write_text("-- new ideal model\n")
            with self.assertRaisesRegex(
                ValueError, "ideal PQXDH/ratchet model files changed"
            ):
                checker.check_models(root)
            added.unlink()
            existing = next(target.rglob("*.lean"))
            existing.write_text(existing.read_text() + "\n-- changed model\n")
            with self.assertRaisesRegex(
                ValueError, "ideal PQXDH/ratchet model files changed"
            ):
                checker.check_models(root)

    def test_added_operation_requires_certificate(self):
        source = self.source + "def new_operation : RustM Unit := ok ()\n"
        with self.assertRaisesRegex(ValueError, "missing=.*new_operation"):
            checker.render(checker.declarations(source), self.certificate)

    def test_deleted_operation_rejects_stale_certificate(self):
        with self.assertRaisesRegex(ValueError, "extra=.*f"):
            checker.render({}, self.certificate)

    def test_signature_change_changes_checked_proposition(self):
        before = checker.render(checker.declarations(self.source), self.certificate)
        source = "def f {T : Type} (x y : T) : RustM T := ok x\n"
        after = checker.render(checker.declarations(source), self.certificate)
        self.assertNotEqual(before, after)
        self.assertIn("theorem operation_000 {T : Type} (x y : T)", after)
        self.assertIn("∃ result, f (T := T) x y = ok result", after)

    def test_source_loop_names_remain_in_boundary(self):
        declarations = checker.declarations(
            "def application_loop : RustM Unit := ok ()\n"
            "@[rust_loop] def generated_loop : RustM Unit := ok ()\n"
            "@[rust_loop_body]\ndef generated_loop_body : RustM Unit := ok ()\n"
            "def example.closure.Insts.Fn.call : RustM Unit := ok ()\n"
            "def example.closure_1.Insts.Fn.call : RustM Unit := ok ()\n"
            "def ordinary_closure : RustM Unit := ok ()\n"
        )
        self.assertEqual(
            {
                name
                for name, item in declarations.items()
                if item["kind"] == "operation"
            },
            {"application_loop", "ordinary_closure"},
        )

    def test_unknown_declaration_format_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unparsed generated definition"):
            checker.declarations(
                self.source + "private def hidden : RustM Unit := ok ()\n"
            )

    def test_unsupported_binder_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unsupported binder"):
            checker.declarations("def f [Inhabited Nat] : RustM Nat := ok 0\n")

    def test_manifest_cannot_supply_its_own_proposition(self):
        self.certificate["f"]["proposition"] = "True"
        with self.assertRaisesRegex(ValueError, "invalid certificate fields"):
            checker.render(checker.declarations(self.source), self.certificate)

    def test_manifest_cannot_inject_a_tactic(self):
        self.certificate["f"]["theorem"] = "Proof.f_total\n  trivial"
        with self.assertRaisesRegex(ValueError, "invalid certificate name"):
            checker.render(checker.declarations(self.source), self.certificate)


if __name__ == "__main__":
    unittest.main()
