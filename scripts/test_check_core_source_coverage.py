#!/usr/bin/env python3
"""Regression and omission controls for the source-to-extraction coverage gate."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_core_source_coverage as checker


class RustScannerTests(unittest.TestCase):
    def scan(self, source):
        return checker.Scanner(source, "beaconcrypt-core/src/lib.rs").scan()[0]

    def test_includes_private_impl_and_feature_functions(self):
        source = """
fn private() {}
pub struct T;
impl T { pub const fn method(&self) {} }
#[cfg(any(test, feature = "test-utils"))]
pub fn feature_function() {}
#[cfg(test)]
mod tests { unsupported_test_macro!(); fn test_only() {} }
"""
        self.assertEqual(
            [f.name for f in self.scan(source)],
            ["private", "method", "feature_function"],
        )

    def test_comments_literals_and_nested_comments_do_not_invent_code(self):
        source = """
/* fn fake() {} /* fn another() {} */ */
fn real() { let a = r###"fn fake() { #[cfg(hidden)] }"###; let b = "\\\" } fn fake() {}"; let c = '}'; }
// fn fake() {}
"""
        self.assertEqual([f.name for f in self.scan(source)], ["real"])

    def test_nested_function_is_included(self):
        self.assertEqual(
            [f.name for f in self.scan("fn outer() { fn inner() {} }")],
            ["outer", "inner"],
        )

    def test_unknown_cfg_fails_in_every_scope(self):
        for source in (
            "#[cfg(not(hax_compilation))] fn hidden() {}",
            '#[cfg(feature = "unproved")] fn hidden() {}',
            "struct S { #[cfg(not(hax_compilation))] hidden: u64 }",
            "enum E { #[cfg(not(hax_compilation))] Hidden }",
            "fn f(#[cfg(not(hax_compilation))] x: u64) {}",
            "fn f() { #[cfg(not(hax_compilation))] hidden(); }",
            '#[cfg_attr(hax_compilation, path = "replacement.rs")] mod substituted;',
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.scan(source)

    def test_proverif_annotation_cannot_hide_additional_attributes(self):
        for annotation in (
            "hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))",
            'hax_lib::proverif::replace("symbolic replacement")',
        ):
            self.scan(f'#[cfg_attr(feature = "proverif", {annotation})] fn f() {{}}')
            for extra in (
                "cfg(not(hax_compilation))",
                'path = "hidden.rs"',
                "derive(Debug)",
            ):
                source = f'#[cfg_attr(feature = "proverif", {annotation}, {extra})] fn f() {{}}'
                with (
                    self.subTest(annotation=annotation, extra=extra),
                    self.assertRaisesRegex(ValueError, "unreviewed Rust attribute"),
                ):
                    self.scan(source)

    def test_unreviewed_macros_and_item_formats_fail(self):
        for source in (
            'include!("hidden.rs");',
            "macro_rules! hidden { () => {} }",
            "fn f() { hidden!(); }",
            "fn f() { r#hidden!(); }",
            "type T = hidden!();",
            "trait Hidden { fn f() {} }",
            'extern "C" { fn hidden(); }',
            "fn f() { let hidden = cfg!(hax_compilation); }",
            'fn f() { #[cfg(feature = "proverif")] hidden!(); }',
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.scan(source)

    def test_external_reexports_and_exported_function_pointers_need_review(self):
        for source in (
            "pub use foreign_crate::unproved_function;",
            "use foreign_crate as hidden; pub use crate::hidden::unproved_function;",
            "extern crate foreign_crate; pub use crate::foreign_crate::unproved_function;",
            "pub const UNPROVED: fn() = foreign_crate::unproved_function;",
            "pub static UNPROVED: fn() = foreign_crate::unproved_function;",
            "pub use super::external_alias;",
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.scan(source)
        self.scan("mod internal; pub use internal::proved; pub use crate::proved;")

    def test_alias_cannot_hide_an_exported_external_function_pointer(self):
        for source in (
            "type Callback = fn(); pub const UNPROVED: Callback = foreign_crate::unproved_function;",
            "type Callback = fn(); type Alias = Callback; pub static UNPROVED: Alias = foreign_crate::unproved_function;",
            'pub type Callback = unsafe extern "C" fn();',
        ):
            with (
                self.subTest(source=source),
                self.assertRaisesRegex(ValueError, "function-pointer type alias"),
            ):
                self.scan(source)

    def test_unbalanced_and_unterminated_code_fails(self):
        for source in (
            "fn f() {",
            'fn f() { let a = "oops; }',
            "/* oops",
            'fn f() { let a = r##"oops"#; }',
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.scan(source)

    def test_charon_columns_expand_hard_tabs(self):
        source = "\tfn f() {}\n"
        self.assertEqual(checker.source_offset(source, {"line": 1, "col": 4}), 1)
        self.assertEqual(checker.source_offset(source, {"line": 1, "col": 13}), 10)
        with self.assertRaisesRegex(ValueError, "inside a tab"):
            checker.source_offset(source, {"line": 1, "col": 2})


class CoverageReceiptTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.source_path = self.root / "beaconcrypt-core/src/lib.rs"
        self.source_path.parent.mkdir(parents=True)
        self.source = "pub fn f() {}\n"
        self.source_path.write_text(self.source)
        self.proof_root = self.root / "beaconcrypt-core/proofs/lean"
        extraction = self.proof_root / "BeaconcryptCore/Extraction"
        extraction.mkdir(parents=True)
        (self.proof_root / "BeaconcryptCore/Extraction.lean").write_text(
            "import BeaconcryptCore.Extraction.Funs\n"
        )
        (extraction / "Types.lean").write_text("-- extracted types\n")
        self.funs = extraction / "Funs.lean"
        self.funs.write_text(
            "/-- Source: 'beaconcrypt-core/src/lib.rs', lines 1:0-1:13 -/\ndef f : RustM Unit := ok ()\n"
        )
        self.llbc = {
            "charon_version": "0.1.247",
            "has_errors": False,
            "translated": {
                "crate_name": "beaconcrypt_core",
                "options": deepcopy(checker.EXPECTED_OPTIONS),
                "files": [
                    {
                        "id": 0,
                        "name": {"Local": "beaconcrypt-core/src/lib.rs"},
                        "crate_name": "beaconcrypt_core",
                        "contents": self.source,
                    }
                ],
                "fun_decls": [
                    {
                        "item_meta": {
                            "is_local": True,
                            "opacity": "Transparent",
                            "name": [
                                {"Ident": ["beaconcrypt_core", 0]},
                                {"Ident": ["f", 0]},
                            ],
                            "span": {
                                "data": {
                                    "file_id": 0,
                                    "beg": {"line": 1, "col": 0},
                                    "end": {"line": 1, "col": 13},
                                }
                            },
                        },
                        "body": {"Structured": {}},
                    }
                ],
            },
        }
        boundary = patch.object(checker, "NATIVE_BOUNDARY", {})
        boundary.start()
        self.addCleanup(boundary.stop)

    def receipt(self):
        result = checker.build_receipt(self.root, self.llbc)
        (self.proof_root / "source-coverage.json").write_text(json.dumps(result))
        return result

    def test_default_check_needs_no_llbc_after_validated_receipt(self):
        self.receipt()
        self.assertEqual(checker.check(self.root), 1)

    def test_new_source_body_or_file_rejects_stale_receipt(self):
        self.receipt()
        for source in ("pub fn f() { panic!(); }\n", self.source + "fn omitted() {}\n"):
            self.source_path.write_text(source)
            with self.assertRaises(ValueError):
                checker.check(self.root)
        self.source_path.write_text(self.source)
        (self.source_path.parent / "untracked.rs").write_text("fn omitted() {}\n")
        with self.assertRaisesRegex(ValueError, "core source changed"):
            checker.check(self.root)

    def test_changed_lean_artifact_rejects_stale_receipt(self):
        self.receipt()
        self.funs.write_text(self.funs.read_text() + "\n-- drift\n")
        with self.assertRaisesRegex(ValueError, "Lean extraction changed"):
            checker.check(self.root)

    def test_source_hashes_preserve_exact_line_endings(self):
        self.receipt()
        self.source_path.write_bytes(self.source.replace("\n", "\r\n").encode())
        with self.assertRaisesRegex(ValueError, "core source changed"):
            checker.check(self.root)

    def test_write_rejects_incomplete_or_stale_llbc_sources(self):
        for edit in ("missing", "stale"):
            llbc = deepcopy(self.llbc)
            if edit == "missing":
                llbc["translated"]["files"] = []
            else:
                llbc["translated"]["files"][0]["contents"] += "// drift\n"
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                checker.build_receipt(self.root, llbc)

    def test_write_rejects_omitted_opaque_or_wrong_function(self):
        for edit in ("missing", "opaque", "wrong-name", "wrong-end"):
            llbc = deepcopy(self.llbc)
            declaration = llbc["translated"]["fun_decls"][0]
            if edit == "missing":
                llbc["translated"]["fun_decls"] = []
            elif edit == "opaque":
                declaration["body"] = "Opaque"
            elif edit == "wrong-name":
                declaration["item_meta"]["name"][-1] = {"Ident": ["other", 0]}
            else:
                declaration["item_meta"]["span"]["data"]["end"]["col"] -= 1
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                checker.build_receipt(self.root, llbc)

    def test_write_rejects_lean_omission(self):
        self.funs.write_text("def unrelated : RustM Unit := ok ()\n")
        with self.assertRaisesRegex(ValueError, "absent from Lean"):
            checker.build_receipt(self.root, self.llbc)

    def test_orphaned_or_commented_lean_metadata_cannot_supply_coverage(self):
        comment = "/-- Source: 'beaconcrypt-core/src/lib.rs', lines 1:0-1:13 -/"
        for source in (
            comment + "\n",
            comment + "\ndef unrelated : RustM Unit := ok ()\n",
            "/-\n" + comment + "\ndef f : RustM Unit := ok ()\n-/\n",
            comment
            + "\n-- a misleading intervening comment\ndef f : RustM Unit := ok ()\n",
        ):
            self.funs.write_text(source)
            with (
                self.subTest(source=source),
                self.assertRaisesRegex(ValueError, "absent from Lean"),
            ):
                checker.build_receipt(self.root, self.llbc)

    def test_normal_check_revalidates_receipt_option_evidence(self):
        receipt = self.receipt()
        receipt["extraction_options"]["exclude"] = ["crate::hidden"]
        (self.proof_root / "source-coverage.json").write_text(json.dumps(receipt))
        with self.assertRaisesRegex(ValueError, "unreviewed LLBC extraction options"):
            checker.check(self.root)

    def test_every_extraction_option_is_pinned(self):
        for key, value in checker.EXPECTED_OPTIONS.items():
            mutated = deepcopy(checker.EXPECTED_OPTIONS)
            mutated[key] = "changed" if value != "changed" else "another value"
            with (
                self.subTest(option=key),
                self.assertRaisesRegex(
                    ValueError, "unreviewed LLBC extraction options"
                ),
            ):
                checker.check_options(mutated)
        mutated = deepcopy(checker.EXPECTED_OPTIONS)
        mutated["unreviewed_new_option"] = True
        with self.assertRaisesRegex(ValueError, "unreviewed LLBC extraction options"):
            checker.check_options(mutated)

    def test_write_rejects_restricted_or_bypassed_extraction(self):
        mutations = [
            (key, ["crate::hidden"])
            for key in (
                "include",
                "exclude",
                "opaque",
                "targets",
                "start_from_attribute",
                "start_from_if_exists",
            )
        ]
        mutations += [
            (key, True)
            for key in (
                "start_from_pub",
                "skip_borrowck",
                "no_typecheck",
                "no_normalize",
            )
        ]
        mutations += [
            ("start_from", ["crate::f"]),
            ("rustc_args", ["--cfg=hax_compilation", "--cfg=hide_me"]),
        ]
        for key, value in mutations:
            llbc = deepcopy(self.llbc)
            llbc["translated"]["options"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                checker.build_receipt(self.root, llbc)
        llbc = deepcopy(self.llbc)
        llbc["has_errors"] = True
        with self.assertRaisesRegex(ValueError, "extraction has errors"):
            checker.build_receipt(self.root, llbc)

    def test_native_derive_changes_require_explicit_boundary_review(self):
        self.source_path.write_text(
            "#[cfg_attr(not(hax_compilation), derive(Debug))]\npub struct S { bytes: [u8; 32] }\n"
        )
        with self.assertRaisesRegex(
            ValueError, "native generated trait/import boundary changed"
        ):
            checker.sources_and_functions(self.root)


if __name__ == "__main__":
    unittest.main()
