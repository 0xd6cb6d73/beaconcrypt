#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Exercise the joint-session evidence gate without running ProVerif."""

import importlib.util
from pathlib import Path
import re
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "mldsa_joint_checker", HERE / "check-mldsa-joint-session.py"
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def output(queries=None, verdicts=None):
    queries = CHECKER.PRIMARY if queries is None else queries
    verdicts = CHECKER.VERDICTS if verdicts is None else verdicts
    lines = [q + " is " + v + "." for q, v in zip(queries, verdicts, strict=True)]
    primary = []
    for line, verdict in zip(lines, verdicts, strict=True):
        if verdict == "false":
            primary.append("A trace has been found.")
        primary.append("RESULT " + line)
    return "\n".join(
        [*primary, "Verification summary:", *("Query " + line for line in lines)]
    )


def copy_inputs(directory):
    for name in CHECKER.MODEL_FILES:
        target = directory / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text((HERE / name).read_text())


class ExactJointSessionGate(unittest.TestCase):
    def setUp(self):
        self.text = output()

    def check(self, text):
        CHECKER.check_output(
            text, CHECKER.PRIMARY, CHECKER.VERDICTS, CHECKER.VERDICTS.count("false")
        )

    def test_complete_paired_evidence(self):
        self.check(self.text)

    def test_security_witness_and_actual_control_rosters_are_complete(self):
        self.assertEqual(len(CHECKER.PRIMARY), 14)
        self.assertEqual(CHECKER.VERDICTS, ("true",) * 8 + ("false",) * 6)
        self.assertEqual(
            [(name, position) for name, _, position, _, _ in CHECKER.CONTROLS],
            [
                ("without-init-verifier-origin", 0),
                ("without-response-verifier-origin", 1),
                ("without-response-verifier-session", 2),
                ("without-init-verifier-secrecy", 5),
                ("without-response-verifier-secrecy", 7),
            ],
        )

    def test_bound_variable_alpha_suffixes_preserve_formula(self):
        renamed = CHECKER.VARIABLE.sub(lambda match: match.group() + "_937", self.text)
        self.check(renamed)

    def test_repeated_variable_cannot_split(self):
        variables = [
            match.group() for match in CHECKER.VARIABLE.finditer(CHECKER.PRIMARY[0])
        ]
        repeated = next(name for name in variables if variables.count(name) > 1)
        changed = self.text.replace(repeated, repeated + "_3", 1)
        with self.assertRaises(ValueError):
            self.check(changed)

    def test_distinct_variables_cannot_merge(self):
        variables = list(
            dict.fromkeys(
                match.group() for match in CHECKER.VARIABLE.finditer(CHECKER.PRIMARY[0])
            )
        )
        self.assertGreaterEqual(len(variables), 2)
        with self.assertRaises(ValueError):
            self.check(
                re.sub(r"\b" + re.escape(variables[1]) + r"\b", variables[0], self.text)
            )

    def test_event_or_transcript_cannot_change(self):
        event = re.search(r"event\((\w+)\(", CHECKER.PRIMARY[0]).group(1)
        variable = CHECKER.VARIABLE.search(CHECKER.PRIMARY[0]).group()
        for changed in [
            self.text.replace(event, "UnreviewedEvent"),
            re.sub(r"\b" + variable + r"\b", "unbound_value", self.text),
        ]:
            with self.subTest(changed=changed[:150]), self.assertRaises(ValueError):
                self.check(changed)

    def test_missing_duplicate_extra_and_reordered_primary_are_rejected(self):
        lines = self.text.splitlines()
        first, second = [
            index for index, line in enumerate(lines) if line.startswith("RESULT ")
        ][:2]
        reordered = lines.copy()
        reordered[first], reordered[second] = reordered[second], reordered[first]
        for changed in [
            "\n".join(lines[:first] + lines[first + 1 :]),
            lines[first] + "\n" + self.text,
            "RESULT not event(UnreviewedEvent) is true.\n" + self.text,
            "\n".join(reordered),
        ]:
            with self.subTest(changed=changed[:150]), self.assertRaises(ValueError):
                self.check(changed)

    def test_summary_is_required_unique_complete_and_ordered(self):
        before, after = self.text.split("Verification summary:")
        lines = after.splitlines()
        queries = [line for line in lines if line.startswith("Query ")]
        for changed in [
            self.text.replace("Verification summary:", ""),
            self.text + "\nVerification summary:",
            before + "Verification summary:\n" + "\n".join(queries[1:]),
            self.text + "\n" + queries[0],
            before + "Verification summary:\n" + "\n".join(reversed(queries)),
        ]:
            with self.subTest(changed=changed[-150:]), self.assertRaises(ValueError):
                self.check(changed)

    def test_summary_and_primary_must_both_have_exact_verdicts(self):
        before, after = self.text.split("Verification summary:")
        for changed in [
            before.replace(" is true.", " is false.", 1)
            + "Verification summary:"
            + after,
            before
            + "Verification summary:"
            + after.replace(" is true.", " is false.", 1),
            self.text.replace(" is false.", " is true."),
        ]:
            with self.subTest(changed=changed[:150]), self.assertRaises(ValueError):
                self.check(changed)

    def test_unknown_and_hypothesized_attacks_are_not_evidence(self):
        for changed in [
            self.text.replace(" is true.", " cannot be proved.", 1),
            self.text.replace(" is true.", " is unknown.", 1),
            self.text.replace(
                "A trace has been found.",
                "A trace has been found, assuming a hypothesis:",
                1,
            ),
            self.text + "\nASSUMING A HYPOTHESIS",
        ]:
            with self.subTest(changed=changed[-150:]), self.assertRaises(ValueError):
                self.check(changed)

    def test_each_witness_requires_its_own_reconstructed_trace(self):
        witness = CHECKER.PRIMARY[CHECKER.VERDICTS.index("false")]
        text = output((CHECKER.PRIMARY[0], witness), ("true", "false"))
        # The same total trace count before a different query must not pass.
        moved = "A trace has been found.\n" + text.replace(
            "A trace has been found.\n", "", 1
        )
        for changed in [
            text.replace("A trace has been found.\n", "", 1),
            "A trace has been found.\n" + text,
            moved,
            text.replace("A trace has been found.\n", "", 1)
            + "\nA trace has been found.",
        ]:
            with self.subTest(changed=changed[:150]), self.assertRaises(ValueError):
                CHECKER.check_output(
                    changed, (CHECKER.PRIMARY[0], witness), ("true", "false"), 1
                )

    def test_primary_and_summary_phases_cannot_mix(self):
        first = "RESULT " + CHECKER.PRIMARY[0] + " is true."
        for changed in [
            self.text + "\n" + first,
            "Query " + CHECKER.PRIMARY[0] + " is true.\n" + self.text,
        ]:
            with self.subTest(changed=changed[:150]), self.assertRaises(ValueError):
                self.check(changed)

    def test_indented_or_malformed_result_records_cannot_hide_extras(self):
        for changed in [
            self.text + "\n  RESULT not event(UnreviewedEvent) is true.",
            self.text + "\n\tQuery not event(UnreviewedEvent) is true.",
            self.text.replace("RESULT ", " RESULT ", 1),
            self.text.replace("Query ", "Query\t", 1),
        ]:
            with self.subTest(changed=changed[-150:]), self.assertRaises(ValueError):
                self.check(changed)

    def test_warning_error_fatal_or_timeout_is_not_evidence(self):
        for notice in [
            "Warning: modified theory",
            "  warning: modified theory",
            "Error: bad model",
            "\tFatal: failure",
            "Timeout: expired",
        ]:
            with self.subTest(notice=notice), self.assertRaises(ValueError):
                self.check(notice + "\n" + self.text)

    def test_invalid_expectation_roster_is_rejected(self):
        for queries, verdicts, traces in [
            ((), (), 0),
            ((CHECKER.PRIMARY[0],), (), 0),
            ((CHECKER.PRIMARY[0],), ("unknown",), 0),
            ((CHECKER.PRIMARY[0],), ("false",), 0),
        ]:
            with self.subTest(verdicts=verdicts), self.assertRaises(ValueError):
                CHECKER.check_output(self.text, queries, verdicts, traces)

    def test_control_requires_exact_false_formula_and_trace(self):
        for _, _, position, _, _ in CHECKER.CONTROLS:
            query = (CHECKER.PRIMARY[position],)
            text = output(query, ("false",))
            CHECKER.check_output(text, query, ("false",), 1)
            for changed in [
                text.replace(" is false.", " is true."),
                text.replace("A trace has been found.", ""),
            ]:
                with self.subTest(position=position), self.assertRaises(ValueError):
                    CHECKER.check_output(changed, query, ("false",), 1)

    def test_every_executed_library_and_model_is_reviewed(self):
        self.assertEqual(set(CHECKER.MODEL_SHA256), set(CHECKER.MODEL_FILES))
        self.assertEqual(
            set(CHECKER.MODEL_FILES),
            set(CHECKER.LIBRARIES)
            | {"mldsa-joint-session.pvl", "mldsa-joint-session.pv"},
        )
        self.assertIn("quantum-capabilities.pvl", CHECKER.LIBRARIES)
        CHECKER.validate_models()

    def test_changed_tokens_in_any_input_require_review(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            copy_inputs(directory)
            for name in CHECKER.MODEL_FILES:
                path = directory / name
                original = path.read_text()
                path.write_text(original + "\nfun unreviewed_change(): bitstring.\n")
                with self.subTest(name=name), self.assertRaises(ValueError):
                    CHECKER.validate_models(directory)
                path.write_text(original)
            CHECKER.validate_models(directory)

    def test_review_roster_cannot_omit_an_executed_library(self):
        hashes = CHECKER.MODEL_SHA256.copy()
        del hashes[CHECKER.LIBRARIES[0]]
        with (
            mock.patch.object(CHECKER, "MODEL_SHA256", hashes),
            self.assertRaisesRegex(ValueError, "incomplete"),
        ):
            CHECKER.validate_models()

    def test_removed_verifiers_and_ad_hashes_require_review(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            copy_inputs(directory)
            for _, filename, _, old, new in CHECKER.CONTROLS:
                path = directory / filename
                original = path.read_text()
                path.write_text(CHECKER.exact_replace(original, old, new))
                with self.subTest(filename=filename), self.assertRaises(ValueError):
                    CHECKER.validate_models(directory)
                path.write_text(original)
            auth = directory / "mldsa-auth.pvl"
            original = auth.read_text()
            for principal in ("server_ml", "agent_ml"):
                auth.write_text(
                    CHECKER.exact_replace(
                        original, "blake2b512(" + principal + ")", "mldsa_zero()"
                    )
                )
                with self.subTest(principal=principal), self.assertRaises(ValueError):
                    CHECKER.validate_models(directory)
            auth.write_text(original)

    def test_prose_and_spacing_do_not_change_semantic_pins(self):
        text = "fun example(bitstring): bitstring."
        self.assertEqual(
            CHECKER.digest(text), CHECKER.digest("(* prose *)\n" + text + "\n")
        )

    def test_control_anchor_must_be_unique(self):
        for text in ["absent", "anchor anchor"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                CHECKER.exact_replace(text, "anchor", "replacement")

    def test_each_control_changes_only_its_reviewed_anchor(self):
        for _, filename, position, old, new in CHECKER.CONTROLS:
            original = (HERE / filename).read_text()
            changed = CHECKER.exact_replace(original, old, new)
            self.assertNotEqual(original, changed)
            self.assertEqual(CHECKER.VERDICTS[position], "true")
            for _, other_file, _, other_anchor, _ in CHECKER.CONTROLS:
                if other_file == filename and other_anchor != old:
                    self.assertEqual(changed.count(other_anchor), 1)

    def test_query_isolation_preserves_the_exact_process(self):
        source = (HERE / "mldsa-joint-session.pv").read_text()
        declarations, process = CHECKER.query_declarations(source)
        self.assertEqual(len(declarations), len(CHECKER.PRIMARY))
        self.assertIn("Joint", process)
        for _, _, position, _, _ in CHECKER.CONTROLS:
            self.assertTrue(declarations[position].strip().endswith("."))
        for changed in [re.sub(r"\bprocess\b", "", source), source + "\nprocess\n"]:
            with self.assertRaises(ValueError):
                CHECKER.query_declarations(changed)


class VerifierExecution(unittest.TestCase):
    def test_exact_pinned_inputs_are_passed_to_the_verifier(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            copy_inputs(directory)
            model = directory / "mldsa-joint-session.pvl"
            queries = directory / "mldsa-joint-session.pv"
            log = directory / "verifier.log"
            evidence = output()
            completed = SimpleNamespace(returncode=0, stdout=evidence)
            with (
                mock.patch.object(CHECKER, "HERE", directory),
                mock.patch.object(
                    CHECKER.subprocess, "run", return_value=completed
                ) as run,
            ):
                self.assertEqual(
                    CHECKER.run("pinned-proverif", model, queries, log, 17), evidence
                )
            command = ["pinned-proverif"]
            for name in CHECKER.LIBRARIES:
                command.extend(["-lib", str(directory / name)])
            command.extend(["-lib", str(model), str(queries)])
            self.assertEqual(run.call_args.args[0], command)
            self.assertEqual(run.call_args.kwargs["timeout"], 17)
            self.assertEqual(log.read_text(), evidence)

    def test_timeout_nonzero_exit_and_runtime_input_changes_are_fatal(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            copy_inputs(directory)
            model = directory / "mldsa-joint-session.pvl"
            queries = directory / "mldsa-joint-session.pv"
            log = directory / "failure.log"
            for evidence in [b"partial evidence", "partial evidence"]:
                with (
                    mock.patch.object(CHECKER, "HERE", directory),
                    mock.patch.object(
                        CHECKER.subprocess,
                        "run",
                        side_effect=subprocess.TimeoutExpired(
                            "proverif", 1, output=evidence
                        ),
                    ),
                    self.assertRaisesRegex(ValueError, "timeout"),
                ):
                    CHECKER.run("proverif", model, queries, log, 1)
                self.assertEqual(log.read_bytes(), b"partial evidence")
            with (
                mock.patch.object(CHECKER, "HERE", directory),
                mock.patch.object(
                    CHECKER.subprocess,
                    "run",
                    return_value=SimpleNamespace(returncode=1, stdout="failure"),
                ),
                self.assertRaisesRegex(ValueError, "failure"),
            ):
                CHECKER.run("proverif", model, queries, log, 1)

            for name in CHECKER.MODEL_FILES:
                target = directory / name
                original = target.read_text()

                def changed(*args, **kwargs):
                    target.write_text(original + "(* edited during verification *)")
                    return SimpleNamespace(returncode=0, stdout=output())

                with (
                    self.subTest(name=name),
                    mock.patch.object(CHECKER, "HERE", directory),
                    mock.patch.object(CHECKER.subprocess, "run", side_effect=changed),
                    self.assertRaisesRegex(ValueError, "changed while"),
                ):
                    CHECKER.run("proverif", model, queries, log, 1)
                target.write_text(original)

    def test_unreviewed_library_override_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unreviewed library"):
            CHECKER.run(
                "proverif",
                Path("model"),
                Path("queries"),
                Path("log"),
                1,
                library_overrides={"unreviewed.pvl": Path("changed")},
            )


if __name__ == "__main__":
    unittest.main()
