#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Independent fail-closed controls for the exhaustive registration proof gate."""

import importlib.util
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "general_admission_gate", HERE / "check-general-registration.py"
)
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)

ORIGIN_RESULT = (
    "RESULT inj-event(GeneralAdmissionCompleted(qga_agreement,next_sequence(next_sequence(first_sequence)),qga_payload,qga_frame,qga_response,qga_claimed))"
    " ==> inj-event(GeneralAdmissionSessionOrigin(qga_agreement,qga_assigned)) is true.\n"
)


class GeneralAdmissionGateTests(unittest.TestCase):
    def test_initial_plan_normalization_is_exact_at_each_literal_parameter(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        source_main = (HERE / "general-registration-admission.pv").read_text()
        call = "general_initial_plan(general_expected_sequence, server_to_beacon_chain(main_root))"
        for target in range(53):
            for flag in ["true", "false"]:
                main = source_main.replace(
                    "first_sequence(), true)", f"{GATE.sequence(target)}, {flag})"
                )
                expected = (
                    roles
                    if target in {0, 52}
                    else roles.replace(
                        call,
                        f"general_prefix_{target}(server_to_beacon_chain(main_root))",
                    )
                )
                self.assertEqual(
                    GATE.project_initial_plan(roles, main, target), expected
                )
        mutations = [
            (
                roles,
                source_main + "\nGeneralAdmissionBeacon(other, first_sequence(), true)",
            ),
            (
                roles,
                source_main.replace(
                    "first_sequence(), true)", "next_sequence(first_sequence()), true)"
                ),
            ),
            (
                roles.replace(
                    "if general_sequence = general_expected_sequence then",
                    "if true then",
                ),
                source_main,
            ),
            (
                roles.replace(
                    "if general_sequence =",
                    "let general_expected_sequence = next_sequence(first_sequence()) in if general_sequence =",
                ),
                source_main,
            ),
            (
                roles.replace(
                    "general_expected_sequence: sequence", "other_sequence: sequence"
                ),
                source_main,
            ),
            (
                roles + "\nGeneralAdmissionBeacon(other, first_sequence(), true)",
                source_main,
            ),
            (
                roles.replace(
                    "then general_prefix_51(chain).", "then general_prefix_50(chain)."
                ),
                source_main,
            ),
        ]
        for changed_roles, main in mutations:
            with self.assertRaises(ValueError):
                GATE.project_initial_plan(changed_roles, main, 1)

    def test_future_safety_preserves_context_and_excludes_witnesses(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        continuation = (HERE / "general-registration-continuation.pvl").read_text()
        environment = (HERE / "environment.pvl").read_text()
        _, extended = GATE.inline_owned_handoff(roles, continuation, environment)
        anchor = "let GeneralAdmissionContinueDirect("
        before, direct = extended.split(anchor)
        head = direct.split("    if mode = general_use_cached() then (\n")[0]
        expected = (
            before
            + anchor
            + head
            + "    GeneralAdmissionFuture(agreement, associated_data, counter, chain, cache, send_chain).\n"
        )
        for index in [11, 20]:
            self.assertEqual(GATE.project_future_safety(extended, index), expected)
        for index in [10, 12, 13, 14, 15, 23]:
            with self.assertRaises(ValueError):
                GATE.project_future_safety(extended, index)
        mutations = [
            extended.replace(
                "in(c, frame: bitstring);", "out(c, cache); in(c, frame: bitstring);", 1
            ),
            extended.replace(
                "ratchet_material(chain), associated_data,",
                "ratchet_material(send_chain), associated_data,",
                1,
            ),
            extended.replace(
                "counter, chain, remaining_cache, send_chain)",
                "counter, changed_chain, remaining_cache, send_chain)",
            ),
            extended.replace(
                "event GeneralReplayRejected(agreement, target);",
                "event GeneralReplayRejected(agreement, target); out(c, opened);",
            ),
        ]
        for changed in mutations:
            with self.assertRaises(ValueError):
                GATE.project_future_safety(changed, 11)

    def test_local_cache_range_is_universal_and_strictly_routed(self):
        queries = re.findall(
            r"(?ms)^query .*?\.$",
            (HERE / "general-registration-admission-queries.pvl").read_text(),
        )
        for target in range(1, 52):
            process, (name, polarity) = GATE.local_cached_range(queries[22], target)
            self.assertNotIn("new ", process)
            self.assertNotIn("<>", process)
            self.assertNotIn("GeneralCachedAccepted", process)
            self.assertNotIn("open_frame", process)
            self.assertEqual(process.count("in(c,"), 1)
            self.assertEqual(process.count("general_cache_pop("), 1)
            self.assertEqual(process.count("receive_cache_entry("), target - 1)
            cache = "receive_cache_empty()"
            for j in range(1, target):
                self.assertEqual(process.count(f"m{j}: bitstring"), 1)
                cache = f"receive_cache_entry({GATE.sequence(j)}, m{j}, {cache})"
            self.assertIn(f"general_cache_pop(selected, {cache})", process)
            self.assertEqual(polarity, "true")
            self.assertEqual(name.startswith("not "), target == 1)
        for target in [0, 52]:
            with self.assertRaises(ValueError):
                GATE.local_cached_range(queries[22], target)
        for changed in [
            queries[9],
            queries[22].replace("qga_payload, qga_frame))", "qga_frame, qga_payload))"),
        ]:
            with self.assertRaises(ValueError):
                GATE.local_cached_range(changed, 51)

    def test_cached_callsite_pins_the_source_prefix_and_sole_consumer(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        continuation = (HERE / "general-registration-continuation.pvl").read_text()
        environment = (HERE / "environment.pvl").read_text()
        GATE.check_cached_callsite(roles, continuation, environment)
        mutations = [
            (
                roles.replace(
                    "let main_opened_initial =",
                    "let general_cache = receive_cache_empty() in let main_opened_initial =",
                ),
                continuation,
            ),
            (
                roles.replace(
                    "receive_cache_empty()).", "general_expected_cache_1).", 1
                ),
                continuation,
            ),
            (
                roles.replace(
                    "previous_target, skipped)).",
                    "previous_target, receive_cache_empty())).",
                    1,
                ),
                continuation,
            ),
            (
                roles.replace(
                    "then general_prefix_51(chain).", "then general_prefix_50(chain)."
                ),
                continuation,
            ),
            (
                roles,
                continuation.replace(
                    "general_cache_pop(target, cache)",
                    "general_cache_pop(target, remaining_cache)",
                    1,
                ),
            ),
            (
                roles,
                continuation.replace(
                    "event GeneralCachedAccepted(agreement, target, opened, frame);",
                    "event GeneralCachedAccepted(agreement, counter, opened, frame);",
                ),
            ),
            (
                roles,
                continuation.replace(
                    "in(c, mode: bitstring);",
                    "in(c, cache: receive_cache); in(c, mode: bitstring);",
                ),
            ),
            (
                roles,
                continuation
                + "\nevent GeneralCachedAccepted(other, target, opened, frame);",
            ),
        ]
        for changed_roles, changed_continuation in mutations:
            with self.assertRaises(ValueError):
                GATE.check_cached_callsite(
                    changed_roles, changed_continuation, environment
                )

    def test_cached_target_guard_preserves_decode_and_remaining_body(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        continuation = (HERE / "general-registration-continuation.pvl").read_text()
        environment = (HERE / "environment.pvl").read_text()
        _, extended = GATE.inline_owned_handoff(roles, continuation, environment)
        anchor = "let GeneralAdmissionContinueDirect("
        before, body = extended.split(anchor)
        lookup = "      let general_cached_result(material, remaining_cache) = general_cache_pop(target, cache) in"
        for target in range(2, 52):
            for selected in range(1, target):
                projected = GATE.project_cached_target(extended, 10, target, selected)
                expected = body.replace(
                    lookup,
                    f"      if target = {GATE.sequence(selected)} then\n"
                    + lookup.replace(
                        "general_cache_pop(target,",
                        f"general_cache_pop({GATE.sequence(selected)},",
                    ),
                )
                self.assertEqual(projected, before + anchor + expected)
        for index, target, selected in [(11, 51, 1), (10, 51, 0), (10, 51, 51)]:
            with self.assertRaises(ValueError):
                GATE.project_cached_target(extended, index, target, selected)
        for changed in [
            extended.replace(
                "target, =SERVER_KEY_ID) = frame", "counter, =SERVER_KEY_ID) = frame"
            ),
            extended.replace(
                "event GeneralCachedAccepted(agreement, target, opened, frame);",
                "event GeneralCachedAccepted(agreement, counter, opened, frame);",
            ),
        ]:
            with self.assertRaises(ValueError):
                GATE.project_cached_target(changed, 10, 51, 1)

    def test_exact_query_output_is_required(self):
        bad_outputs = [
            "",
            ORIGIN_RESULT.replace("is true", "is false"),
            ORIGIN_RESULT.replace(
                "GeneralAdmissionSessionOrigin", "GeneralAdmissionPlanOrigin"
            ),
            ORIGIN_RESULT + ORIGIN_RESULT,
            ORIGIN_RESULT.replace("is true", "cannot be proved"),
        ]
        with tempfile.TemporaryDirectory() as temporary:
            log_dir = Path(temporary)
            for output in [ORIGIN_RESULT] + bad_outputs:
                with self.subTest(output=output):

                    def fake_run(*args, **kwargs):
                        kwargs["stdout"].write(output)

                    with patch.object(GATE.subprocess, "run", fake_run):
                        if output == ORIGIN_RESULT:
                            self.assertEqual(
                                GATE.check_case("unused", 1, 3, log_dir, [1]), (3, 1)
                            )
                        else:
                            with self.assertRaises(ValueError):
                                GATE.check_case("unused", 1, 3, log_dir, [1])

    def test_backend_failure_is_not_a_result(self):
        with tempfile.TemporaryDirectory() as temporary:
            for failure in [
                subprocess.CalledProcessError(1, "proverif"),
                subprocess.TimeoutExpired("proverif", 1),
            ]:
                with self.subTest(failure=failure):
                    with patch.object(GATE.subprocess, "run", side_effect=failure):
                        with self.assertRaises(type(failure)):
                            GATE.check_case("unused", 1, 3, Path(temporary), [1])

    def test_private_worker_retains_all_events_and_one_owner(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        self.assertEqual(GATE.validated_worker_roles(roles), roles)
        mutations = [
            roles.replace(
                "free general_send_states: channel [private].",
                "free general_send_states: channel.",
            ),
            roles.replace("next_sequence(target)", "target"),
            roles.replace(
                "ratchet_next(chain), prior_material, material",
                "chain, prior_material, material",
            ),
            roles.replace("out(c, frame);", "out(c, material);"),
            roles.replace(
                "out(c, main_response);", "out(c, main_response); out(c, main_root);"
            ),
            roles.replace(
                "event GeneralAdmissionPlanOrigin(", "event RemovedPlanOrigin(", 1
            ),
            roles + "\nout(general_send_states, copied).\n",
            roles + "\nin(general_send_states, copied).\n",
            roles.replace(
                "if general_sequence = general_expected_sequence then", "if true then"
            ),
        ]
        for changed in mutations:
            with self.subTest(mutation=changed[-80:]):
                with self.assertRaises(ValueError):
                    GATE.validated_worker_roles(changed)

    def test_single_owner_witness_pins_the_reference_components(self):
        main = (HERE / "general-registration-admission.pv").read_text()
        main = main.replace(
            "| !MaliciousServer()",
            "| !MaliciousServer() | !GeneralPublicAdmissionWitness(first_sequence())",
        )
        expected = main
        for role in [
            "GeneralAdmissionBeacon",
            "GeneralAdmissionServer",
            "GeneralPublicAdmissionWitness",
        ]:
            expected = expected.replace("!" + role + "(", role + "(")
        expected = expected.replace("!MaliciousBeacon()", "0").replace(
            "!MaliciousServer()", "0"
        )
        self.assertEqual(GATE.single_owner_witness_main(main), expected)
        for role in [
            "GeneralAdmissionBeacon",
            "GeneralAdmissionServer",
            "GeneralPublicAdmissionWitness",
            "MaliciousBeacon",
            "MaliciousServer",
        ]:
            marker = "!" + role + "("
            for changed in [
                main.replace(marker, "Changed("),
                main + "\n" + marker + ")",
            ]:
                with self.assertRaises(ValueError):
                    GATE.single_owner_witness_main(changed)

    def test_payload_specialization_is_only_existential(self):
        queries = GATE.re.findall(
            r"(?ms)^query .*?\.$",
            (HERE / "general-registration-admission-queries.pvl").read_text(),
        )
        for target in range(53):
            for index, query in enumerate(queries, 1):
                instantiated = GATE.instantiate_query(query, index, target)
                selected = GATE.selected_witness_payload(index, target)
                allowed = (index in {3, 13} and 1 <= target <= 51) or (
                    index == 7 and 2 <= target <= 51
                )
                self.assertEqual(selected is not None, allowed)
                if allowed:
                    self.assertIn(selected, instantiated)
                    self.assertNotIn("qga_payload", instantiated)
                    self.assertTrue(GATE.sender_projection_parameters(index, target)[3])
                    self.assertEqual(
                        "INITIAL_SECRET" in instantiated, index == 3 and target == 1
                    )
                elif "qga_payload" in query:
                    self.assertIn("qga_payload", instantiated)

    def test_cached_origin_decomposition_covers_every_source_sequence(self):
        self.assertEqual(GATE.SEQUENCE_GUARDS[10], 23)
        self.assertEqual(GATE.query_execution_order([10, 23]), [23, 10])
        full_order = GATE.query_execution_order(list(range(1, 24)))
        self.assertLess(full_order.index(23), full_order.index(10))
        with self.assertRaises(ValueError):
            GATE.query_execution_order([10])
        classified = 0
        for target in range(53):
            expected = (
                [j for j in range(1, 51) if j < target] if 2 <= target <= 51 else [None]
            )
            self.assertEqual(GATE.cached_query_cases(10, target), expected)
            classified += sum(
                len(GATE.cached_query_cases(index, target)) for index in range(1, 24)
            )
            for index in set(range(1, 24)) - {10}:
                witness_case = (
                    [1] if index in {12, 15} and 2 <= target <= 51 else [None]
                )
                self.assertEqual(GATE.cached_query_cases(index, target), witness_case)
                if witness_case == [1]:
                    self.assertTrue(
                        GATE.sender_projection_parameters(index, target, 1)[3]
                    )
            for selected in expected:
                if selected is None:
                    continue
                cutoff, records, plans, witness = GATE.sender_projection_parameters(
                    10, target, selected
                )
                self.assertEqual(
                    (cutoff, records, plans, witness),
                    (target, {selected}, set(), False),
                )
        self.assertEqual(classified, 2444)
        for index, target, selected in [
            (10, 51, 0),
            (10, 51, 51),
            (10, 1, 1),
            (11, 3, 1),
        ]:
            with self.assertRaises(ValueError):
                GATE.sender_projection_parameters(index, target, selected)

    def test_cached_coverage_keeps_the_complete_receiver_and_exact_marker(self):
        import re

        queries = re.findall(
            r"(?ms)^query .*?\.$",
            (HERE / "general-registration-admission-queries.pvl").read_text(),
        )
        self.assertEqual(len(queries), 23)
        for target in range(53):
            coverage = GATE.instantiate_query(queries[22], 23, target)
            self.assertNotIn("general_cached_sequence_coverage", coverage)
            if target in {0, 1, 52}:
                self.assertNotIn("==>", coverage)
            else:
                self.assertEqual(coverage.count("qga_seq ="), target - 1)
                self.assertNotIn("general_zero_sequence", coverage)
            for selected in GATE.cached_query_cases(10, target):
                if selected is None:
                    continue
                query = GATE.instantiate_query(queries[9], 10, target, selected)
                self.assertNotIn("qga_seq", query)
                body = query.split(";", 1)[1]
                self.assertEqual(body.count(GATE.sequence(selected)), 2)
        with self.assertRaises(ValueError):
            GATE.instantiate_query(
                queries[22].replace("general_cached_sequence_coverage", "unreviewed"),
                23,
                51,
            )
        for index, target, selected in [
            (10, 51, 0),
            (10, 51, 51),
            (10, 1, 1),
            (11, 3, 1),
        ]:
            with self.assertRaises(ValueError):
                GATE.instantiate_query(queries[index - 1], index, target, selected)

    def test_disclosure_cannot_be_a_reachability_witness(self):
        for target in range(53):
            for index in range(1, 24):
                cutoff, records, plans, witness = GATE.sender_projection_parameters(
                    index, target
                )
                allowed = (index in {3, 13} and 1 <= target <= 51) or (
                    index in {7, 12, 15} and 2 <= target <= 51
                )
                self.assertEqual(witness, allowed)
                self.assertTrue(1 <= cutoff <= 52)
                self.assertTrue(all(1 <= seq <= cutoff for seq in records | plans))
                if index == 10 and 2 <= target <= 51:
                    self.assertEqual(records, set(range(1, target)))
                if index == 11 and 1 <= target <= 51:
                    self.assertIn(target + 1, records)
                    self.assertEqual(cutoff, target + 1)
                if index == 9 and 1 <= target <= 51:
                    self.assertEqual(plans, {target})
        for index, target in [(0, 1), (24, 1), (1, -1), (1, 53)]:
            with self.assertRaises(ValueError):
                GATE.sender_projection_parameters(index, target)

    def test_projected_prefix_preserves_each_public_operation(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        main = (HERE / "general-registration-admission.pv").read_text()
        main = main.replace(
            "| !MaliciousServer()",
            "| !MaliciousServer() | !GeneralPublicAdmissionWitness(first_sequence())",
        )
        anchor = "      out(general_send_states, ("
        before = roles[: roles.index(anchor)]
        terminal = "beacon_to_server_chain(main_root)))"
        after = roles[roles.index(terminal, len(before)) + len(terminal) :]
        for target in range(53):
            for index in [2, 3, 7, 9, 10, 11, 13, 14]:
                projected, projected_main, witness, cutoff = GATE.project_sender_suffix(
                    roles, main, index, target
                )
                self.assertEqual(projected[: len(before)], before)
                self.assertTrue(projected.endswith(after))
                expected_main = main.replace("!GeneralAdmissionSend()", "0")
                if witness:
                    expected_main = GATE.single_owner_witness_main(expected_main)
                    if index == 3 and target == 1:
                        expected_main = expected_main.replace(
                            "GeneralPublicAdmissionWitness(first_sequence())", "0"
                        )
                    self.assertNotIn("!GeneralAdmission", projected_main)
                    self.assertNotIn("Malicious", projected_main)
                self.assertEqual(projected_main, expected_main)
                suffix = projected[len(before) : len(projected) - len(after)]
                previous = "ratchet_next(main_server_chain_1)"
                for i in range(2, cutoff + 1):
                    request = f"in(c, general_cutoff_application_{i}: bitstring);"
                    material = f"let general_cutoff_material_{i} = ratchet_material({previous}) in"
                    next_chain = (
                        f"let general_cutoff_next_{i} = ratchet_next({previous}) in"
                    )
                    seal = f"let general_cutoff_frame_{i} = seal_frame(general_cutoff_material_{i}, main_associated_data, {GATE.sequence(i)}, SERVER_KEY_ID, general_cutoff_application_{i}) in"
                    publication = f"out(c, general_cutoff_frame_{i});"
                    offsets = [
                        suffix.index(part)
                        for part in [request, material, next_chain, seal, publication]
                    ]
                    self.assertEqual(offsets, sorted(offsets))
                    self.assertTrue(
                        all(
                            suffix.count(part) == 1
                            for part in [
                                request,
                                material,
                                next_chain,
                                seal,
                                publication,
                            ]
                        )
                    )
                    previous = f"general_cutoff_next_{i}"
                self.assertEqual(suffix.count("in(c,"), cutoff - 1)
                self.assertEqual(suffix.count("seal_frame("), cutoff - 1)
                self.assertEqual(suffix.count("out(c,"), cutoff - 1 + (not witness))
                if witness:
                    self.assertTrue(suffix.rstrip().endswith("0"))
                else:
                    self.assertTrue(
                        suffix.rstrip().endswith(
                            f"out(c, ({previous}, {GATE.sequence(cutoff + 1)}, main_associated_data, main_assigned_key_id))"
                        )
                    )

    def test_owned_handoff_erasure_retains_the_full_body_and_arguments(self):
        roles = (HERE / "general-registration-admission.pvl").read_text()
        continuation = (HERE / "general-registration-continuation.pvl").read_text()
        environment = (HERE / "environment.pvl").read_text()
        projected, extended = GATE.inline_owned_handoff(
            roles, continuation, environment
        )
        self.assertTrue(extended.startswith(continuation))
        direct = extended[len(continuation) :]
        self.assertEqual(
            direct.split("  event GeneralContinuationStarted", 1)[1],
            continuation.split("  event GeneralContinuationStarted", 1)[1],
        )
        self.assertIn(
            "main_associated_data, main_assigned_key_id, general_sequence, general_next_chain,\n      general_cache, beacon_to_server_chain(main_root)",
            projected,
        )
        self.assertIn(
            "| if main_assigned_key_id = SERVER_KEY_ID then\n      event GeneralAdmissionRelabelled(general_sequence, main_opened_initial)",
            projected,
        )
        mutations = [
            (
                roles.replace("new main_registration_session: bitstring;", ""),
                continuation,
                environment,
            ),
            (
                roles.replace(
                    "new main_registration_session: bitstring;",
                    "new main_registration_session: bitstring; new main_registration_session: bitstring;",
                ),
                continuation,
                environment,
            ),
            (
                roles.replace(
                    "main_registration_session\n    ) in\n    event GeneralAdmissionCompleted",
                    "main_root\n    ) in\n    event GeneralAdmissionCompleted",
                ),
                continuation,
                environment,
            ),
            (
                roles.replace("out(general_admitted_states,", "out(other_states,"),
                continuation,
                environment,
            ),
            (
                roles + "\nout(general_admitted_states, copied)",
                continuation,
                environment,
            ),
            (
                roles.replace(
                    "main_associated_data, main_assigned_key_id,\n      receive_state",
                    "main_root, main_assigned_key_id,\n      receive_state",
                ),
                continuation,
                environment,
            ),
            (roles, continuation.replace("(=agreement,", "(agreement,"), environment),
            (
                roles,
                continuation + "\nin(general_admitted_states, copied);",
                environment,
            ),
            (
                roles,
                continuation,
                environment.replace("    mr_origin\n  ).", "    mr_root\n  )."),
            ),
            (
                roles,
                continuation,
                environment.replace(
                    "): authenticated_registration_session_t [data].",
                    "): authenticated_registration_session_t.",
                ),
            ),
        ]
        for changed in mutations:
            with self.assertRaises(ValueError):
                GATE.inline_owned_handoff(*changed)

    def test_causal_projection_rejects_new_effects_and_owners(self):
        continuation_name = "general-registration-continuation.pvl"
        roles_name = "general-registration-admission.pvl"
        continuation = (HERE / continuation_name).read_text()
        roles = (HERE / roles_name).read_text()
        mutations = [
            (continuation_name, continuation + "\nout(c, opened).\n"),
            (
                continuation_name,
                continuation.replace(
                    "if mode = general_use_cached() then (",
                    "if mode = general_use_cached() then",
                ),
            ),
            (continuation_name, continuation + "\ninsert shared(opened).\n"),
            (continuation_name, continuation + "\nMaliciousServer().\n"),
            (
                continuation_name,
                continuation.replace("in(c, mode", "in(other_private, mode"),
            ),
            (continuation_name, continuation.replace("(=agreement,", "(agreement,")),
            (
                roles_name,
                roles.replace(
                    "| (if general_continue then",
                    "; event Changed(); | (if general_continue then",
                ),
            ),
            (
                roles_name,
                roles
                + "\nGeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment))\n",
            ),
            (
                roles_name,
                roles.replace(
                    "| (if general_continue then GeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment)))",
                    "| if general_continue then GeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment))",
                ),
            ),
        ]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with patch.object(GATE, "HERE", root):
                for name, value in [(None, None)] + mutations:
                    (root / continuation_name).write_text(continuation)
                    (root / roles_name).write_text(roles)
                    if name is None:
                        GATE.check_causal_projection()
                    else:
                        with self.subTest(mutation=name, value=value[-100:]):
                            (root / name).write_text(value)
                            with self.assertRaises(ValueError):
                                GATE.check_causal_projection()


if __name__ == "__main__":
    unittest.main()
