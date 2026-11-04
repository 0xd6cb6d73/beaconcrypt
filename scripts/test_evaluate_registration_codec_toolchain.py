#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Candidate identity, mode separation and unchanged fail-closed controls."""

from contextlib import ExitStack, redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_registration_codec_extraction as checkpoint
import evaluate_registration_codec_toolchain as candidate
import prepare_registration_codec_aeneas as prepare
from test_check_registration_codec_extraction import RegistrationCodecCheckpointTests


class CandidateCodecToolchainTests(unittest.TestCase):
    def test_all_mir_pipelines_preserve_source_cohort_and_body_controls(self):
        tools = {name: Path("/tools") / name for name in ("charon", "aeneas")}
        for cohort in checkpoint.COHORTS:
            original = checkpoint.commands(tools, Path("/work"), cohort, False)
            before = tuple(list(command) for command in original)
            for mode in candidate.MIR_PIPELINES:
                charon, aeneas = candidate.pipeline_commands(original, mode)
                self.assertEqual(aeneas, original[1])
                self.assertEqual(
                    [arg for arg in charon if arg.startswith("--opaque=")],
                    ["--opaque=beaconcrypt_core"],
                )
                self.assertEqual(
                    [arg for arg in charon if arg.startswith("--start-from=")],
                    [arg for arg in original[0] if arg.startswith("--start-from=")],
                )
                self.assertEqual(original, before)

    def test_unknown_mir_pipeline_is_rejected(self):
        with self.assertRaises(ValueError):
            candidate.pipeline_commands(
                (["charon", "cargo"], ["aeneas"]), "arbitrary-flags"
            )

    def test_candidate_selection_is_explicit(self):
        with (
            patch("sys.argv", ["candidate", "--work-dir", "/tmp/unused-candidate"]),
            redirect_stderr(io.StringIO()),
            self.assertRaises(SystemExit) as error,
        ):
            candidate.main()
        self.assertEqual(error.exception.code, 2)

    def test_interrupted_candidate_already_has_a_blocked_report(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory)
            stack.enter_context(
                patch(
                    "sys.argv",
                    [
                        "candidate",
                        "--candidate",
                        candidate.CANDIDATE,
                        "--work-dir",
                        str(root),
                    ],
                )
            )
            stack.enter_context(patch.object(checkpoint, "configuration"))
            stack.enter_context(
                patch.object(
                    candidate,
                    "candidate_tools",
                    return_value=({}, {"mode": candidate.CANDIDATE}),
                )
            )
            stack.enter_context(
                patch.object(checkpoint, "run", side_effect=KeyboardInterrupt)
            )
            stack.enter_context(
                patch.object(checkpoint, "TOOLS", dict(checkpoint.TOOLS))
            )
            stack.enter_context(
                patch.object(checkpoint, "VERSIONS", dict(checkpoint.VERSIONS))
            )
            original = (checkpoint.TOOLS, checkpoint.VERSIONS, checkpoint.commands)
            with self.assertRaises(KeyboardInterrupt):
                candidate.main()
            self.assertIs(checkpoint.TOOLS, original[0])
            self.assertIs(checkpoint.VERSIONS, original[1])
            self.assertIs(checkpoint.commands, original[2])
            paths = list(root.glob("*/report.json"))
            self.assertEqual(len(paths), 1)
            report = json.loads(paths[0].read_text())
            self.assertEqual(report["status"], "blocked")
            self.assertFalse(report["current_pin_acceptance"])
            self.assertFalse(report["source_correspondence_proved"])

    def test_postrun_provenance_failure_cannot_leave_success_report(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root = Path(directory)
            stack.enter_context(
                patch(
                    "sys.argv",
                    [
                        "candidate",
                        "--candidate",
                        candidate.CANDIDATE,
                        "--work-dir",
                        str(root),
                    ],
                )
            )
            stack.enter_context(patch.object(checkpoint, "configuration"))
            stack.enter_context(
                patch.object(
                    candidate,
                    "candidate_tools",
                    side_effect=[
                        ({}, {"mode": candidate.CANDIDATE}),
                        ValueError("tool changed"),
                    ],
                )
            )
            stack.enter_context(
                patch.object(
                    checkpoint,
                    "run",
                    return_value={"status": "extracted-without-external-obligations"},
                )
            )
            stack.enter_context(
                patch.object(checkpoint, "TOOLS", dict(checkpoint.TOOLS))
            )
            stack.enter_context(
                patch.object(checkpoint, "VERSIONS", dict(checkpoint.VERSIONS))
            )
            original = (checkpoint.TOOLS, checkpoint.VERSIONS, checkpoint.commands)
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                self.assertEqual(candidate.main(), 1)
            self.assertIs(checkpoint.TOOLS, original[0])
            self.assertIs(checkpoint.VERSIONS, original[1])
            self.assertIs(checkpoint.commands, original[2])
            report = json.loads(next(root.glob("*/report.json")).read_text())
            self.assertEqual(report["status"], "blocked")
            self.assertEqual(report["error"], "tool changed")

    def test_custom_patch_requires_exact_occurrence_count(self):
        for source in ("if join then", "if join then " * 4):
            with self.subTest(source=source), self.assertRaises(ValueError):
                prepare.replace_exact(
                    source, "if join then", "if false && join then", 3
                )

    def test_custom_preparation_preserves_existing_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sentinel = root / "precious"
            sentinel.write_text("preserve")
            with self.assertRaises(ValueError):
                prepare.prepare(Path("/no-source-needed"), root)
            self.assertEqual(sentinel.read_text(), "preserve")

    def test_custom_preparation_cannot_write_inside_checkout(self):
        with self.assertRaises(ValueError):
            prepare.prepare(
                Path("/no-source-needed"), checkpoint.ROOT / "var/candidate-forbidden"
            )

    def fixture(self, directory: Path) -> tuple[Path, Path, Path, dict]:
        root = directory / "tools"
        hashes = {}
        for name in ("charon", "charon-driver", "rust-toolchain", "aeneas"):
            tool = "aeneas" if name == "aeneas" else "charon"
            path = root / tool / candidate.TOOLS[tool] / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(name)
            path.chmod(0o700)
            hashes[name] = checkpoint.digest(path.read_bytes())
        custom = directory / "custom-aeneas"
        custom.write_text("custom compiler")
        custom.chmod(0o700)
        source = directory / "source"
        (source / "src").mkdir(parents=True)
        (source / "src/main.ml").write_text("let x = 1")
        (source / "flake.nix").write_text("{ outputs = {}; }")
        (source / "flake.lock").write_text("{}")
        return root, custom, source, hashes

    def fixture_identities(
        self, stack: ExitStack, custom: Path, source: Path, hashes: dict
    ):
        stack.enter_context(patch.dict(candidate.HASHES, hashes))
        stack.enter_context(
            patch.object(
                candidate, "CUSTOM_HASH", checkpoint.digest(custom.read_bytes())
            )
        )
        stack.enter_context(
            patch.object(candidate, "CUSTOM_SOURCE_HASH", candidate.source_hash(source))
        )

    def test_candidate_mode_cannot_inherit_custom_paths(self):
        for executable, source in (
            (Path("/x"), None),
            (None, Path("/s")),
            (Path("/x"), Path("/s")),
        ):
            with (
                self.subTest(executable=executable, source=source),
                self.assertRaises(ValueError),
            ):
                candidate.candidate_tools(
                    candidate.CANDIDATE, Path("/tools"), executable, source
                )

    def test_custom_mode_requires_executable_and_source(self):
        for executable, source in (
            (None, None),
            (Path("/x"), None),
            (None, Path("/s")),
        ):
            for mode in (candidate.CUSTOM, candidate.RECOVER):
                with (
                    self.subTest(mode=mode, executable=executable, source=source),
                    self.assertRaises(ValueError),
                ):
                    candidate.candidate_tools(mode, Path("/tools"), executable, source)

    def test_custom_variants_cannot_share_the_wrong_source_identity(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root, custom, source, hashes = self.fixture(Path(directory))
            self.fixture_identities(stack, custom, source, hashes)
            stack.enter_context(
                patch.object(
                    candidate, "RECOVER_HASH", checkpoint.digest(custom.read_bytes())
                )
            )
            candidate.candidate_tools(candidate.CUSTOM, root, custom, source)
            with self.assertRaises(ValueError):
                candidate.candidate_tools(candidate.RECOVER, root, custom, source)

    def test_unknown_candidate_fails_before_tool_lookup(self):
        with self.assertRaises(ValueError):
            candidate.candidate_tools("arbitrary", Path("/tools"), None, None)

    def test_binary_or_driver_substitution_fails(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root, custom, source, hashes = self.fixture(Path(directory))
            self.fixture_identities(stack, custom, source, hashes)
            tools, _ = candidate.candidate_tools(candidate.CANDIDATE, root, None, None)
            for path in (
                tools["charon"],
                tools["charon"].parent / "charon-driver",
                tools["aeneas"],
            ):
                original = path.read_bytes()
                path.write_bytes(original + b" changed")
                with self.subTest(path=path), self.assertRaises(ValueError):
                    candidate.candidate_tools(candidate.CANDIDATE, root, None, None)
                path.write_bytes(original)

    def test_custom_source_mutation_or_addition_fails(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root, custom, source, hashes = self.fixture(Path(directory))
            self.fixture_identities(stack, custom, source, hashes)
            candidate.candidate_tools(candidate.CUSTOM, root, custom, source)
            implementation = source / "src/main.ml"
            implementation.write_text("let x = 2")
            with self.assertRaises(ValueError):
                candidate.candidate_tools(candidate.CUSTOM, root, custom, source)
            implementation.write_text("let x = 1")
            (source / "src/extra.ml").write_text("let x = 3")
            with self.assertRaises(ValueError):
                candidate.candidate_tools(candidate.CUSTOM, root, custom, source)

    def test_custom_source_symlink_cannot_escape_snapshot(self):
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            root, custom, source, hashes = self.fixture(Path(directory))
            self.fixture_identities(stack, custom, source, hashes)
            (source / "src/other.ml").symlink_to(custom)
            with self.assertRaises(ValueError):
                candidate.candidate_tools(candidate.CUSTOM, root, custom, source)

    def test_candidate_success_never_counts_as_current_pin_acceptance(self):
        report = {
            "status": "extracted-without-external-obligations",
            "source_correspondence_proved": True,
        }
        candidate.label_report(report, {"mode": candidate.CANDIDATE})
        self.assertEqual(
            report["status"], "candidate-extraction-without-external-obligations"
        )
        self.assertFalse(report["current_pin_acceptance"])
        self.assertFalse(report["source_correspondence_proved"])
        self.assertFalse(report["installs_output"])

    def test_candidate_failure_stays_blocked_and_pinned_defaults_stay_unchanged(self):
        original_tools, original_versions = dict(checkpoint.TOOLS), dict(
            checkpoint.VERSIONS
        )
        report = {"status": "blocked", "error": "body rejected"}
        candidate.label_report(report, {"mode": candidate.CUSTOM})
        self.assertEqual(report["status"], "blocked")
        self.assertEqual(report["error"], "body rejected")
        self.assertEqual(checkpoint.TOOLS, original_tools)
        self.assertEqual(checkpoint.VERSIONS, original_versions)


if __name__ == "__main__":
    # Importing the original suite deliberately reruns all compiler rejection,
    # body/external roster and incomplete-output controls in candidate reviews.
    unittest.main()
