#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Focused regressions for the adapter extraction's review boundary."""

from pathlib import Path
import contextlib
import io
import json
from types import SimpleNamespace
import tempfile
import unittest
from unittest import mock

import extract_adapter_record as extraction

DRIVER = (
    "import BeaconcryptCore.AdapterRecordExtraction.FunsExternal\n"
    "namespace beaconcrypt\n\n"
    "def ratchet.execute_record_receive (pending : Nat) : Nat := pending\n"
    "end beaconcrypt\n"
).encode()
FUNCTION_TEMPLATE = "".join(
    f"axiom {name} : {signature}\n"
    for name, signature in extraction.EXTERNAL_SIGNATURES.items()
).encode()
TYPE_TEMPLATE = b"-- no foreign type declarations\n"


def make_source_fixture(parent: Path):
    root = parent / "checkout"
    for name in extraction.SOURCE_FILES:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"source\n")
    (root / "hax.toml").write_bytes((extraction.ROOT / "hax.toml").read_bytes())
    core_source = root / "beaconcrypt-core/src/lib.rs"
    core_source.parent.mkdir(parents=True)
    core_source.write_bytes(b"// core source\n")
    destination = root / "beaconcrypt-core/proofs/lean" / extraction.SUBDIRECTORY
    destination.mkdir(parents=True)
    models = {
        name: b"set_option warningAsError true\n-- maintained model\n"
        for name in extraction.MODELS
    }
    for name, contents in models.items():
        (destination / name).write_bytes(contents)
    proof = destination.parent / "Refinement/AdapterRecordReceive.lean"
    proof.parent.mkdir()
    proof.write_bytes(b"set_option warningAsError true\n-- handwritten proof\n")
    generated = parent / "work/generated" / extraction.SUBDIRECTORY
    generated.mkdir(parents=True)
    raw = {
        "Funs.lean": DRIVER,
        "Types.lean": b"-- generated types\n",
        "FunsExternal_Template.lean": FUNCTION_TEMPLATE,
        "TypesExternal_Template.lean": TYPE_TEMPLATE,
    }
    for name, contents in raw.items():
        (generated / name).write_bytes(contents)
    tools = {}
    for name in extraction.PINNED_TOOLS:
        tool = parent / name
        tool.write_bytes(name.encode())
        tools[name] = tool
    snapshot = extraction.snapshot_inputs(root, destination, tools)
    contents = extraction.assemble(generated, models)
    provenance = extraction.build_provenance(generated, snapshot, contents)
    for name, value in contents.items():
        (destination / name).write_bytes(value)
    write_provenance(destination, provenance)
    return root, destination, generated, tools, provenance


def write_provenance(destination: Path, provenance: dict):
    (destination / "provenance.json").write_text(json.dumps(provenance))


class AdapterExtractionTests(unittest.TestCase):
    def test_binder_is_the_only_generated_body_change(self):
        bound = extraction.bind_operations(DRIVER)
        insertion = ("\n" + extraction.BINDER).encode()
        self.assertEqual(bound.count(insertion), 1)
        self.assertEqual(bound.replace(insertion, b"", 1), DRIVER)
        self.assertEqual(extraction.unbind_operations(bound), DRIVER)

    def test_missing_or_duplicate_binder_is_rejected(self):
        bound = extraction.bind_operations(DRIVER)
        for source in (DRIVER, bound + extraction.BINDER.encode()):
            with (
                self.subTest(source=source),
                self.assertRaisesRegex(ValueError, "binder"),
            ):
                extraction.unbind_operations(source)

    def test_missing_or_duplicate_namespace_fails_closed(self):
        for source in (
            DRIVER.replace(b"namespace beaconcrypt\n", b"namespace other\n"),
            DRIVER + b"namespace beaconcrypt\n",
        ):
            with (
                self.subTest(source=source),
                self.assertRaisesRegex(ValueError, "namespace"),
            ):
                extraction.bind_operations(source)

    def test_already_transformed_output_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unmodified"):
            extraction.bind_operations(extraction.bind_operations(DRIVER))

    def test_missing_or_duplicate_driver_is_rejected(self):
        for source in (
            DRIVER.replace(b"ratchet.execute_record_receive", b"ratchet.other"),
            DRIVER + b"def ratchet.execute_record_receive : Nat := 0\n",
        ):
            with (
                self.subTest(source=source),
                self.assertRaisesRegex(ValueError, "exactly one"),
            ):
                extraction.bind_operations(source)

    def test_unchecked_obligations_are_rejected(self):
        for token in (b"sorry", b"admit", b"axiom", b"sorryAx", b"opaque", b"#check"):
            with (
                self.subTest(token=token),
                self.assertRaisesRegex(ValueError, "obligation"),
            ):
                extraction.require_model(b"def bad := " + token, "model")

    def test_changed_tool_or_library_pins_are_rejected(self):
        configuration = {
            "tools": dict(extraction.PINNED_TOOLS),
            "versions": dict(extraction.PINNED_VERSIONS),
        }
        extraction.validate_configuration(configuration)
        for field in ("tools", "versions"):
            changed = {name: dict(value) for name, value in configuration.items()}
            changed[field][next(iter(changed[field]))] = "unreviewed"
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "pins"):
                extraction.validate_configuration(changed)

    def test_scratch_cannot_alias_source_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for path in (root, root / "nested", root.parent):
                with (
                    self.subTest(path=path),
                    self.assertRaisesRegex(ValueError, "outside"),
                ):
                    extraction.isolated_work_directory(path, root)

    def test_scratch_symlink_cannot_alias_source_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            root = parent / "checkout"
            root.mkdir()
            alias = parent / "alias"
            alias.symlink_to(root, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "outside"):
                extraction.isolated_work_directory(alias / "nested", root)

    def test_output_directory_links_cannot_escape_scratch(self):
        for name in ("generated", "target"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                parent = Path(directory)
                work = parent / "scratch"
                outside = parent / "checkout"
                work.mkdir()
                outside.mkdir()
                sentinel = outside / "Types.lean"
                sentinel.write_bytes(b"preserve this source")
                (work / name).symlink_to(outside, target_is_directory=True)
                with mock.patch.object(extraction.subprocess, "run") as run:
                    with self.assertRaisesRegex(ValueError, "symbolic link|escapes"):
                        extraction.run_pipeline(
                            Path("charon"), Path("aeneas"), work, {}
                        )
                    run.assert_not_called()
                self.assertEqual(sentinel.read_bytes(), b"preserve this source")

    def test_nested_target_directory_link_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            work = parent / "scratch"
            (work / "target").mkdir(parents=True)
            outside = parent / "checkout"
            outside.mkdir()
            (work / "target/debug").symlink_to(outside, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "symbolic link"):
                extraction.validate_work_paths(work)

    def test_log_and_generated_file_links_cannot_escape_scratch(self):
        for name in (
            "charon.log",
            "generated/" + extraction.SUBDIRECTORY + "/Types.lean",
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                parent = Path(directory)
                work = parent / "scratch"
                candidate = work / name
                candidate.parent.mkdir(parents=True)
                outside = parent / "source"
                outside.write_bytes(b"preserve this source")
                candidate.symlink_to(outside)
                with self.assertRaisesRegex(ValueError, "escapes"):
                    extraction.validate_work_paths(work)
                self.assertEqual(outside.read_bytes(), b"preserve this source")

    def test_encoded_rustflags_cannot_override_reviewed_cfg(self):
        inherited = {"CARGO_ENCODED_RUSTFLAGS": "--cfg\x1fwrong", "RUSTFLAGS": "old"}
        environment = extraction.extraction_environment(Path("/scratch"), inherited)
        self.assertNotIn("CARGO_ENCODED_RUSTFLAGS", environment)
        self.assertEqual(environment["RUSTFLAGS"], extraction.RUSTFLAGS)
        self.assertEqual(environment["CARGO_TARGET_DIR"], "/scratch/target")
        self.assertIn("CARGO_ENCODED_RUSTFLAGS", inherited)

    def test_stale_llbc_cannot_reach_aeneas_after_empty_success(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            stale = work / "beaconcrypt.llbc"
            stale.write_bytes(b"old compilation")

            def no_output(command, **kwargs):
                self.assertEqual(command[0], "charon")
                self.assertFalse(stale.exists())
                return SimpleNamespace(returncode=0)

            with mock.patch.object(
                extraction.subprocess, "run", side_effect=no_output
            ) as run:
                with self.assertRaisesRegex(RuntimeError, "fresh nonempty LLBC"):
                    extraction.run_pipeline(Path("charon"), Path("aeneas"), work, {})
                self.assertEqual(run.call_count, 1)

    def test_new_llbc_and_generated_directory_reach_aeneas(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            llbc = work / "beaconcrypt.llbc"
            llbc.write_bytes(b"stale")

            def compiler(command, **kwargs):
                if command[0] == "charon":
                    self.assertFalse(llbc.exists())
                    llbc.write_bytes(b"new compilation")
                else:
                    self.assertEqual(command[0], "aeneas")
                    self.assertEqual(llbc.read_bytes(), b"new compilation")
                    self.assertTrue((work / "generated").is_dir())
                return SimpleNamespace(returncode=0)

            with mock.patch.object(
                extraction.subprocess, "run", side_effect=compiler
            ) as run:
                generated = extraction.run_pipeline(
                    Path("charon"), Path("aeneas"), work, {}
                )
                self.assertTrue(generated.is_dir())
                self.assertEqual(run.call_count, 2)

    def test_empty_llbc_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)

            def empty_output(command, **kwargs):
                (work / "beaconcrypt.llbc").touch()
                return SimpleNamespace(returncode=0)

            with mock.patch.object(
                extraction.subprocess, "run", side_effect=empty_output
            ) as run:
                with self.assertRaisesRegex(RuntimeError, "fresh nonempty LLBC"):
                    extraction.run_pipeline(Path("charon"), Path("aeneas"), work, {})
                self.assertEqual(run.call_count, 1)

    def test_new_or_changed_signatures_need_explicit_write_review(self):
        for baseline in (None, b"previous signatures"):
            for write in (False, True):
                with self.subTest(baseline=baseline, write=write):
                    with self.assertRaisesRegex(
                        ValueError, "review-external-signatures"
                    ):
                        extraction.require_reviewed_signatures(
                            b"new signatures", baseline, write=write, review=False
                        )
            extraction.require_reviewed_signatures(
                b"new signatures", baseline, write=True, review=True
            )

    def test_matching_signatures_need_no_new_review(self):
        for write in (False, True):
            extraction.require_reviewed_signatures(
                b"same signatures", b"same signatures", write=write, review=False
            )

    def test_check_mode_never_accepts_signature_review_flag(self):
        with (
            mock.patch.object(
                extraction.sys,
                "argv",
                [
                    "extract",
                    "--check",
                    "--review-external-signatures",
                    "--work-dir",
                    "/scratch",
                ],
            ),
            mock.patch.object(extraction.subprocess, "run") as run,
        ):
            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as exited:
                    extraction.main()
            self.assertEqual(exited.exception.code, 2)
            run.assert_not_called()

    def test_source_check_requires_neither_work_directory_nor_tools(self):
        with (
            mock.patch.object(extraction.sys, "argv", ["extract", "--check-source"]),
            mock.patch.object(extraction, "check_source") as check,
            mock.patch.object(extraction.subprocess, "run") as run,
        ):
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(extraction.main(), 0)
            check.assert_called_once_with()
            run.assert_not_called()

    def test_source_check_is_mutually_exclusive_with_extraction(self):
        with (
            mock.patch.object(
                extraction.sys, "argv", ["extract", "--check-source", "--check"]
            ),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            with self.assertRaises(SystemExit) as exited:
                extraction.main()
            self.assertEqual(exited.exception.code, 2)

    def test_driver_selection_does_not_expand_to_whole_crate(self):
        charon, aeneas = extraction.commands(
            Path("charon"), Path("aeneas"), Path("/scratch")
        )
        self.assertIn("--start-from=" + extraction.START_FROM, charon)
        self.assertIn("--opaque=beaconcrypt_core", charon)
        self.assertNotIn("--include=beaconcrypt_core", charon)
        self.assertIn("--no-default-features", charon)
        self.assertIn("--features=beacon,pqxdh", charon)
        self.assertEqual(aeneas[aeneas.index("-subdir") + 1], extraction.SUBDIRECTORY)

    def test_raw_external_templates_are_evidence_only(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = Path(directory)
            for name in extraction.GENERATED:
                source = DRIVER if name == "Funs.lean" else b"-- generated types\n"
                if name == "FunsExternal_Template.lean":
                    source = FUNCTION_TEMPLATE
                elif name == "TypesExternal_Template.lean":
                    source = TYPE_TEMPLATE
                (generated / name).write_bytes(source)
            models = {name: b"-- maintained model\n" for name in extraction.MODELS}
            contents = extraction.assemble(generated, models)
            self.assertEqual(
                set(contents), {"Funs.lean", "Types.lean", "external-signatures.json"}
            )
            self.assertIn(b"ratchet.ratchet_hkdf", contents["external-signatures.json"])
            self.assertNotIn(b"axiom", contents["Funs.lean"])

    def test_external_model_roster_and_signatures_are_exact(self):
        valid = {
            "FunsExternal_Template.lean": FUNCTION_TEMPLATE,
            "TypesExternal_Template.lean": TYPE_TEMPLATE,
        }
        extraction.validate_external_templates(valid)
        for name, source in (
            ("FunsExternal_Template.lean", FUNCTION_TEMPLATE + b"axiom extra : Bool\n"),
            (
                "FunsExternal_Template.lean",
                FUNCTION_TEMPLATE.replace(b"64#usize", b"32#usize"),
            ),
            ("TypesExternal_Template.lean", b"axiom ForeignType : Type\n"),
        ):
            with self.subTest(name=name, source=source):
                changed = dict(valid)
                changed[name] = source
                with self.assertRaisesRegex(ValueError, "external"):
                    extraction.validate_external_templates(changed)

    def test_source_evidence_validation_needs_no_cached_binaries(self):
        with tempfile.TemporaryDirectory() as directory:
            root, destination, _, tools, _ = make_source_fixture(Path(directory))
            for path in tools.values():
                path.unlink()
            extraction.check_source(root, destination)

    def test_warning_policy_cannot_be_disabled_or_local_only(self):
        enabled = b"set_option warningAsError true\n"
        for source in (
            b"-- missing persistent warning policy\n",
            b"set_option warningAsError false\n",
            enabled + enabled,
            b"set_option warningAsError true in\nexample : True := by trivial\n",
            enabled
            + b"set_option warningAsError false in\nexample : True := by trivial\n",
        ):
            with (
                self.subTest(source=source),
                self.assertRaisesRegex(ValueError, "warningAsError true exactly once"),
            ):
                extraction.require_handwritten_warning_policy(source, "handwritten")

    def test_local_deprecation_and_other_warning_suppression_are_rejected(self):
        for option in (
            "linter",
            "linter.deprecated",
            "linter.deprecated.module",
            "linter.unusedVariables",
        ):
            source = (
                "set_option warningAsError true\n"
                f"set_option {option} false in\nexample : True := by trivial\n"
            ).encode()
            with (
                self.subTest(option=option),
                self.assertRaisesRegex(
                    ValueError, "disables handwritten Lean warnings"
                ),
            ):
                extraction.require_handwritten_warning_policy(source, "handwritten")

    def test_warning_policy_ignores_comments_and_quoted_text(self):
        harmless = (
            b"set_option warningAsError true\n"
            b"/- outer /- nested -/\nset_option warningAsError false\n-/\n"
            b' def message := "set_option linter.deprecated false"\n'
            b"-- set_option warningAsError true\n"
        )
        extraction.require_handwritten_warning_policy(harmless, "handwritten")
        for fake in (
            b"/- outer /- nested -/\nset_option warningAsError true\n-/\n",
            b'def message := "\nset_option warningAsError true\n"\n',
        ):
            with (
                self.subTest(fake=fake),
                self.assertRaisesRegex(ValueError, "exactly once"),
            ):
                extraction.require_handwritten_warning_policy(fake, "handwritten")

    def test_source_check_enforces_all_three_handwritten_warning_policies(self):
        for name in (
            "TypesExternal.lean",
            "FunsExternal.lean",
            "../Refinement/AdapterRecordReceive.lean",
        ):
            for suppressed in (
                b"-- removed persistent warning policy\n",
                b"set_option warningAsError false\n",
                b"set_option warningAsError true\nset_option linter.deprecated.module false in\n",
            ):
                with (
                    self.subTest(name=name, suppressed=suppressed),
                    tempfile.TemporaryDirectory() as directory,
                ):
                    root, destination, _, _, provenance = make_source_fixture(
                        Path(directory)
                    )
                    path = destination / name
                    path.write_bytes(suppressed)
                    if name in extraction.MODELS:
                        provenance["model_sha256"][name] = extraction.digest(suppressed)
                        write_provenance(destination, provenance)
                    with self.assertRaisesRegex(
                        ValueError, "warningAsError|disables handwritten"
                    ):
                        extraction.check_source(root, destination)

    def test_generated_warning_options_remain_unmodified_and_outside_policy(self):
        with tempfile.TemporaryDirectory() as directory:
            root, destination, generated, tools, _ = make_source_fixture(
                Path(directory)
            )
            raw = generated / "Funs.lean"
            raw.write_bytes(
                b"set_option linter.unusedVariables false\n" + raw.read_bytes()
            )
            models = {
                name: (destination / name).read_bytes() for name in extraction.MODELS
            }
            contents = extraction.assemble(generated, models)
            for name, value in contents.items():
                (destination / name).write_bytes(value)
            snapshot = extraction.snapshot_inputs(root, destination, tools)
            write_provenance(
                destination, extraction.build_provenance(generated, snapshot, contents)
            )
            extraction.check_source(root, destination)
            self.assertEqual(
                extraction.unbind_operations(contents["Funs.lean"]), raw.read_bytes()
            )

    def test_source_model_and_installed_drift_are_rejected(self):
        for relative, expected in (
            ("beaconcrypt/src/ratchet.rs", "source_sha256 drift"),
            (
                "beaconcrypt-core/proofs/lean/"
                + extraction.SUBDIRECTORY
                + "/FunsExternal.lean",
                "model_sha256 drift",
            ),
            (
                "beaconcrypt-core/proofs/lean/"
                + extraction.SUBDIRECTORY
                + "/Types.lean",
                "installed_sha256 drift",
            ),
        ):
            with (
                self.subTest(relative=relative),
                tempfile.TemporaryDirectory() as directory,
            ):
                root, destination, _, _, _ = make_source_fixture(Path(directory))
                path = root / relative
                path.write_bytes(path.read_bytes() + b"changed\n")
                with self.assertRaisesRegex(ValueError, expected):
                    extraction.check_source(root, destination)

    def test_added_core_source_cannot_disappear_from_provenance(self):
        with tempfile.TemporaryDirectory() as directory:
            root, destination, _, _, _ = make_source_fixture(Path(directory))
            (root / "beaconcrypt-core/src/new.rs").write_bytes(b"// added\n")
            with self.assertRaisesRegex(ValueError, "source_sha256 roster"):
                extraction.check_source(root, destination)

    def test_snapshot_detects_source_model_and_tool_changes(self):
        for kind in ("source", "model", "tool", "added source"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root, destination, _, tools, _ = make_source_fixture(Path(directory))
                before = extraction.snapshot_inputs(root, destination, tools)
                if kind == "source":
                    path = root / "beaconcrypt/src/ratchet.rs"
                elif kind == "model":
                    path = destination / "FunsExternal.lean"
                elif kind == "tool":
                    path = tools["charon"]
                else:
                    path = root / "beaconcrypt-core/src/new.rs"
                path.write_bytes(b"changed")
                after = extraction.snapshot_inputs(root, destination, tools)
                with self.assertRaisesRegex(ValueError, "inputs changed"):
                    extraction.require_unchanged_inputs(before, after)

    def test_source_check_rejects_missing_rosters_and_bad_metadata(self):
        for field in (
            "source_sha256",
            "installed_sha256",
            "model_sha256",
            "tool_sha256",
            "raw_generated_sha256",
            "tools",
        ):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                root, destination, _, _, provenance = make_source_fixture(
                    Path(directory)
                )
                provenance[field] = {}
                write_provenance(destination, provenance)
                with self.assertRaisesRegex(ValueError, "roster|provenance"):
                    extraction.check_source(root, destination)

    def test_installed_hash_update_cannot_hide_driver_body_change(self):
        with tempfile.TemporaryDirectory() as directory:
            root, destination, _, _, provenance = make_source_fixture(Path(directory))
            path = destination / "Funs.lean"
            path.write_bytes(path.read_bytes().replace(b":= pending", b":= 0"))
            provenance["installed_sha256"]["Funs.lean"] = extraction.digest(
                path.read_bytes()
            )
            write_provenance(destination, provenance)
            with self.assertRaisesRegex(ValueError, "raw driver body"):
                extraction.check_source(root, destination)

    def test_consistent_hashes_cannot_expand_the_external_model_roster(self):
        with tempfile.TemporaryDirectory() as directory:
            root, destination, _, _, provenance = make_source_fixture(Path(directory))
            path = destination / "external-signatures.json"
            evidence = json.loads(path.read_bytes())
            name = "FunsExternal_Template.lean"
            evidence[name]["source"] += "axiom extra : Bool\n"
            evidence[name]["sha256"] = extraction.digest(
                evidence[name]["source"].encode()
            )
            path.write_text(json.dumps(evidence))
            provenance["installed_sha256"][path.name] = extraction.digest(
                path.read_bytes()
            )
            provenance["raw_generated_sha256"][name] = evidence[name]["sha256"]
            write_provenance(destination, provenance)
            with self.assertRaisesRegex(
                ValueError, "external function declaration roster"
            ):
                extraction.check_source(root, destination)

    def test_external_evidence_hash_and_shape_are_checked(self):
        for change in ("wrong digest", "wrong shape", "wrong source type"):
            with (
                self.subTest(change=change),
                tempfile.TemporaryDirectory() as directory,
            ):
                root, destination, _, _, provenance = make_source_fixture(
                    Path(directory)
                )
                path = destination / "external-signatures.json"
                evidence = json.loads(path.read_bytes())
                name = "FunsExternal_Template.lean"
                if change == "wrong digest":
                    evidence[name]["sha256"] = "0" * 64
                elif change == "wrong shape":
                    evidence[name]["unchecked"] = True
                else:
                    evidence[name]["source"] = []
                path.write_text(json.dumps(evidence))
                provenance["installed_sha256"][path.name] = extraction.digest(
                    path.read_bytes()
                )
                write_provenance(destination, provenance)
                with self.assertRaisesRegex(ValueError, "external-signature"):
                    extraction.check_source(root, destination)


if __name__ == "__main__":
    unittest.main()
