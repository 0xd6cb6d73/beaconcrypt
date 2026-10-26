#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Independent failure controls for the KEM-free authentication proof gate."""

import importlib.util
from pathlib import Path
import re
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "kem_controller_gate", HERE / "check-kem-controller-auth.py"
)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
GENERATOR = GATE.GENERATOR


def fixture(mode):
    results = GATE.EXPECTED[mode]
    primary = "\n".join(results)
    secondary = ""
    if mode == "exposed":
        secondary = "\n".join(
            result.replace("RESULT ", "RESULT (even ").replace("inj-event", "event")[
                :-1
            ]
            + ".)"
            for result in results
        )
    traces = "A trace has been found.\n" * (
        0 if mode == "authentication" else len(results)
    )
    summary = "\n".join(result.replace("RESULT ", "Query ", 1) for result in results)
    return f"{primary}\n{secondary}\n{traces}Verification summary:\n{summary}\n"


class KemControllerGateTests(unittest.TestCase):
    def test_result_gate_rejects_wrong_events_fields_polarities_and_missing_evidence(
        self,
    ):
        for mode in GATE.EXPECTED:
            valid = fixture(mode)
            GATE.check_output(mode, valid)
            lines = valid.splitlines()
            invalid = [
                "\n".join(lines[1:]),
                (
                    valid.replace(" is true.", " cannot be proved.")
                    if mode == "authentication"
                    else valid.replace(" is false.", " is true.")
                ),
                valid.replace("RESULT ", "RESULT ", 1)
                + "RESULT unrecognized is true.\n",
                valid.replace("Verification summary:", "Summary omitted:"),
                valid + "Verification summary:\n",
                valid.replace("Query ", "SubstitutedQuery ", 1),
                valid.replace("RESULT ", "RESULT duplicate_", 1),
            ]
            for output in invalid:
                with (
                    self.subTest(mode=mode, output=output[:80]),
                    self.assertRaises(ValueError),
                ):
                    GATE.check_output(mode, output)
            if mode != "authentication":
                for output in (
                    valid.replace("A trace has been found.", "No trace.", 1),
                    valid + "I could not confirm this trace.\n",
                ):
                    with self.assertRaises(ValueError):
                        GATE.check_output(mode, output)
        for before, after in (
            ("main_claimed", "main_server_assigned"),
            ("sender,receiver", "receiver,sender"),
            ("first_sequence", "next_sequence(first_sequence)"),
        ):
            with self.assertRaises(ValueError):
                GATE.check_output(
                    "authentication", fixture("authentication").replace(before, after)
                )

    def test_weaker_result_and_summary_cannot_mask_changed_primary(self):
        valid = fixture("exposed")
        with self.assertRaises(ValueError):
            GATE.check_output(
                "exposed",
                valid.replace("RESULT (even event(", "RESULT (even inj-event(", 1),
            )
        with self.assertRaises(ValueError):
            GATE.check_output(
                "exposed", valid.replace("RESULT (even ", "Ignored secondary ", 1)
            )
        with self.assertRaises(ValueError):
            GATE.check_output("exposed", valid.replace(" is false.", " is true.", 1))

    def test_unchanged_authentication_queries_retain_all_nine_complete_bodies(self):
        original = (HERE / "queries.pvl").read_text()
        queries = re.findall(
            r"\bquery\b.*?\.", GENERATOR.without_comments(original), flags=re.S
        )
        selected = GENERATOR.authentication_queries(original)
        self.assertEqual(
            re.findall(r"\bquery\b.*?\.", selected, flags=re.S), queries[5:]
        )
        for changed in (
            original.replace("query attacker(INITIAL_SECRET).", ""),
            original.replace("BeaconInitiated(", "WrongOrigin("),
            original + "\nquery attacker(EXTRA).\n",
        ):
            with self.assertRaises(ValueError):
                GENERATOR.authentication_queries(changed)

    def test_complete_original_events_and_non_kem_theory_are_preserved(self):
        original = (HERE / "environment.pvl").read_text()
        generated = GENERATOR.environment(original)
        events = lambda text: re.findall(
            r"\bevent\s+(?!KemController)\w+\s*\([^;]*?\)\s*(?:\[\])?\s*;", text
        )
        self.assertEqual(events(generated), events(original))
        self.assertEqual(generated.count("event KemControllerRequested("), 8)
        self.assertEqual(generated.count("event KemControllerReturned("), 8)
        self.assertEqual(generated.count("event KemControllerRejected("), 8)
        self.assertNotRegex(GENERATOR.without_comments(generated), r"\bmlkem_")
        for prefix in ("", "main_"):
            # The exact parsed ciphertext reaches the controller before the
            # original pin and all DHs; the original target events remain later.
            request = f"event KemControllerRequested(kem_decapsulation_request({prefix}beacon_kem_handle, {prefix}beacon_pq, {prefix}kem_ciphertext))"
            position = generated.index(request)
            pin = generated.index(
                f"if {prefix}response_server_identity = {prefix}server_identity then",
                position,
            )
            dh = generated.index(f"let {prefix}dh1 = x25519_beacon_dh(", pin)
            self.assertLess(position, pin)
            self.assertLess(pin, dh)
        original_crypto = (HERE / "crypto.pvl").read_text()
        generated_crypto = GENERATOR.crypto(original_crypto)
        self.assertEqual(
            original_crypto.split("(* ML-KEM encapsulation")[0],
            generated_crypto.split("(* No KEM algebra")[0],
        )
        anchor = "(* This constructor is referenced"
        self.assertEqual(
            original_crypto.split(anchor)[1], generated_crypto.split(anchor)[1]
        )
        self.assertNotRegex(GENERATOR.without_comments(generated_crypto), r"\bmlkem_")

    def test_unexpected_kem_site_or_equation_fails_closed(self):
        source = (HERE / "environment.pvl").read_text()
        changes = (
            source.replace(
                "mlkem_decapsulate(kem_ciphertext, beacon_pq_secret)",
                "mlkem_decapsulate(changed_ciphertext, beacon_pq_secret)",
            ),
            source.replace(
                "mlkem_shared_secret(beacon_pq, kem_coins)",
                "mlkem_shared_secret(beacon_pq, reused_coins)",
                1,
            ),
            source.replace(
                "let beacon_pq = mlkem_public(beacon_pq_secret)",
                "let beacon_pq = attacker_public_key",
                1,
            ),
            source + "\nlet Extra() = let value = mlkem_extra() in 0.\n",
        )
        for changed in changes:
            with self.assertRaises(ValueError):
                GENERATOR.environment(changed)
        theory = (HERE / "crypto.pvl").read_text()
        with self.assertRaises(ValueError):
            GENERATOR.crypto(
                theory.replace(
                    "mlkem_shared_secret(mlkem_public(secret_key), coins)", "coins"
                )
            )


if __name__ == "__main__":
    unittest.main()
