#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check all target cases with exact query result names and polarities."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent


def sequence(n):
    return (
        "general_zero_sequence()"
        if n == 0
        else ("next_sequence(" * (n - 1) + "first_sequence()" + ")" * (n - 1))
    )


def check_causal_projection():
    """Deleting this output-free per-owner tail preserves admission event traces."""
    continuation = (HERE / "general-registration-continuation.pvl").read_text()
    code = re.sub(r"\(\*.*?\*\)", "", continuation, flags=re.S)
    if re.search(r"\b(out|insert|get|phase|new)\b", code):
        raise ValueError(
            "admission causal projection: continuation gained an observable or shared effect"
        )
    if re.findall(r"\blet (General\w+)\(", code) != [
        "GeneralAdmissionFuture",
        "GeneralAdmissionContinue",
    ]:
        raise ValueError(
            "admission causal projection: continuation macro inventory changed"
        )
    if any(
        channel not in {"c", "general_admitted_states"}
        for channel in re.findall(r"\bin\((\w+),", code)
    ):
        raise ValueError(
            "admission causal projection: continuation reads another private interface"
        )
    if code.count("in(general_admitted_states, (=agreement,") != 1:
        raise ValueError("admission causal projection: exact per-owner handoff changed")
    if (
        code.count("if mode = general_use_cached() then (") != 1
        or code.count(
            "    ) else\n      GeneralAdmissionFuture(agreement, associated_data, counter, chain, cache, send_chain)."
        )
        != 1
    ):
        raise ValueError(
            "cached branch lost the parentheses protecting direct future reception"
        )
    allowed_calls = {
        "GeneralAdmissionFuture",
        "GeneralAdmissionContinue",
        "GeneralCachedAccepted",
        "GeneralFutureAccepted",
        "GeneralReplayAccepted",
        "GeneralReplayRejected",
        "GeneralInitialTargetRetained",
        "GeneralContinuationStarted",
        "in",
        "general_use_cached",
        "general_check_initial",
        "general_cached_result",
        "general_cache_missing",
        "general_cache_pop",
        "crypto_frame",
        "receive_state",
        "next_sequence",
        "open_frame",
        "ratchet_material",
    }
    if (
        set(re.findall(r"\b([A-Za-z_]\w*)\s*\(", code)) - {"then", "else"}
    ) != allowed_calls:
        raise ValueError(
            "admission causal projection: unreviewed continuation call or event"
        )
    roles = (HERE / "general-registration-admission.pvl").read_text()
    if (
        roles.count(
            "GeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment))"
        )
        != 1
    ):
        raise ValueError(
            "admission causal projection: per-Beacon continuation ownership changed"
        )
    if (
        roles.count(
            "| (if general_continue then GeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment)))"
        )
        != 1
    ):
        raise ValueError("continuation guard captures an independent admission branch")
    start = roles.index("out(general_admitted_states,")
    depth = 0
    closing = None
    for offset in range(roles.index("(", start), len(roles)):
        if roles[offset] == "(":
            depth += 1
        elif roles[offset] == ")":
            depth -= 1
            if depth == 0:
                closing = offset + 1
                break
    if closing is None or not roles[closing:].lstrip().startswith(
        "| (if general_continue then"
    ):
        raise ValueError(
            "admission causal projection: handoff producer gained a sequential continuation"
        )


def check_public_witness():
    code = re.sub(
        r"\(\*.*?\*\)",
        "",
        (HERE / "general-registration-public-witness.pvl").read_text(),
        flags=re.S,
    )
    if re.search(
        r"\b(new|free|insert|get|phase)\b|SECRET|general_admitted_states|general_cache",
        code,
    ):
        raise ValueError("public witness gained a secret, oracle or shared-state hook")
    calls = set(re.findall(r"\b([A-Za-z_]\w*)\s*\(", code))
    if calls != {
        "GeneralPublicAdmissionWitness",
        "in",
        "out",
        "kex_response",
        "crypto_frame",
        "general_use_cached",
        "registration_payload",
        "general_nonempty",
        "sender_id_le64",
        "beaconcrypt_core__pqxdh__RegistrationKeyIdBinding",
    }:
        raise ValueError("public witness gained an unreviewed operation")
    if set(re.findall(r"\b(?:in|out)\((\w+),", code)) != {"c"}:
        raise ValueError("public witness uses a private channel")


INITIAL_SPECIALIZED = {1, 2, 3, 4, 5, 6, 8, 9, 16, 17}
FUTURE_SPECIALIZED = {11, 13}
SEQUENCE_GUARDS = {
    **{index: 18 for index in {1, 2, 3, 4, 5, 6, 8}},
    9: 19,
    10: 23,
    11: 20,
    13: 20,
    16: 21,
    17: 22,
}


PUBLIC_WITNESS_PAYLOAD = (
    "registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding("
    "sender_id_le64(SERVER_KEY_ID)),general_nonempty(sender_id_le64(SERVER_KEY_ID)))"
)


def selected_witness_payload(index, target):
    if index == 3 and target == 1:
        return (
            "registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding("
            "sender_id_le64(qga_claimed)),general_nonempty(INITIAL_SECRET))"
        )
    if index == 13 and target == 1:
        return PUBLIC_WITNESS_PAYLOAD
    return None


def query_execution_order(query_indices):
    order = sorted(query_indices)
    if 10 in order:
        if 23 not in order:
            raise ValueError(
                "cached origin requires its separately checked coverage guard"
            )
        order.remove(23)
        order.insert(order.index(10), 23)
    return order


def cached_query_cases(index, target):
    if index == 10 and 2 <= target <= 51:
        return list(range(1, target))
    if index in {12, 15} and 2 <= target <= 51:
        # One actual cached-1 trace witnesses existence; absence boundaries
        # retain the full process and an arbitrary target below.
        return [1]
    return [None]


def cached_coverage_conclusion(target, printed=False):
    if not 2 <= target <= 51:
        return None
    values = [sequence(j) for j in range(1, target)]
    if printed:
        values = [value.replace("()", "") for value in values]
    return " || ".join("qga_seq = " + value for value in values)


def local_cached_range(query, target):
    """Check public instances of the material-parametric destructor obligation."""
    expected = """query qga_agreement: authenticated_registration_session_t,
      qga_seq: sequence, qga_payload: bitstring, qga_frame: bitstring;
      event(GeneralCachedAccepted(qga_agreement, qga_seq, qga_payload, qga_frame)) ==>
      general_cached_sequence_coverage(qga_seq)."""
    normalize = lambda text: re.sub(r"\s+", "", text)
    if normalize(query) != normalize(expected) or not 1 <= target <= 51:
        raise ValueError("local cached range requires its exact component obligation")
    # Inputs may coincide and are neither fresh names nor independent samples.
    # This process alone ranges over public terms. Its extension to inaccessible
    # source material follows from the Lean prefix/selected-case lemmas and the
    # pinned destructor syntax, which never inspects material. Only tags matter.
    cache = "receive_cache_empty()"
    variables = ["selected: sequence"]
    for j in range(1, target):
        cache = f"receive_cache_entry({sequence(j)}, m{j}, {cache})"
        variables.append(f"m{j}: bitstring")
    pattern = variables[0] if target == 1 else "(" + ", ".join(variables) + ")"
    event = "event(GeneralCachedTag(qga_seq))"
    conclusion = cached_coverage_conclusion(target)
    body = event + (" ==> " + conclusion if conclusion else "")
    statement = "query qga_seq: sequence; " + body + ".\n"
    process = (
        "event GeneralCachedTag(sequence).\n"
        + statement
        + "process\n  in(c, "
        + pattern
        + ");\n  let general_cached_result(material, remaining) = "
        + f"general_cache_pop(selected, {cache}) in\n"
        + "  event GeneralCachedTag(selected)\n"
    )
    return process, (
        body.replace("()", "") if conclusion else "not " + event,
        "true",
    )


def check_initial_plan_cases(roles):
    """Check the exact finite selector and every source-order prefix equation."""
    normalize = lambda text: re.sub(
        r"\s+", "", re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    )
    code = normalize(roles)
    prefix = (
        "letfun general_prefix_1(chain: bitstring) = "
        "general_plan(ratchet_material(chain), ratchet_next(chain), receive_cache_empty())."
    )
    for n in range(2, 52):
        prefix += (
            f"letfun general_prefix_{n}(chain: bitstring) = "
            "let general_plan(previous_target, target_chain, skipped) = "
            f"general_prefix_{n - 1}(chain) in "
            "general_plan(ratchet_material(target_chain), ratchet_next(target_chain), "
            f"receive_cache_entry({sequence(n - 1)}, previous_target, skipped))."
        )
    prefix += "letfun general_initial_plan(target: sequence, chain: bitstring) = "
    for n in range(1, 52):
        prefix += (
            f"{'if' if n == 1 else 'else if'} target = {sequence(n)} "
            f"then general_prefix_{n}(chain){'.' if n == 51 else ''}"
        )
    if code.count(normalize(prefix)) != 1:
        raise ValueError(
            "exact source cache-prefix recurrence or case selection changed"
        )


def project_initial_plan(roles, main, target):
    """Evaluate only the selected branch at the main's literal role parameter."""
    check_initial_plan_cases(roles)
    if not 0 <= target <= 52:
        raise ValueError("initial plan normalization outside the checked family")
    code = re.sub(r"\(\*.*?\*\)", "", roles, flags=re.S)
    signature = "let GeneralAdmissionBeacon(main_beacon_record_secret: bitstring, general_expected_sequence: sequence, general_continue: bool) ="
    if (
        code.count(signature) != 1
        or code.count("GeneralAdmissionBeacon(") != 1
        or len(re.findall(r"\bgeneral_expected_sequence\b", code)) != 3
    ):
        raise ValueError(
            "initial plan parameter gained a shadow or another role invocation"
        )
    expected = f"GeneralAdmissionBeacon(BEACON_RECORD_SECRET, {sequence(target)}, "
    if (
        main.count("GeneralAdmissionBeacon(") != 1
        or sum(main.count(expected + flag + ")") for flag in ["true", "false"]) != 1
    ):
        raise ValueError(
            "initial plan normalization lost its unique literal role argument"
        )
    source = """    if general_sequence = general_expected_sequence then
    let general_plan(general_target_material, general_next_chain, general_cache) =
      general_initial_plan(general_expected_sequence, server_to_beacon_chain(main_root)) in"""
    if roles.count(source) != 1:
        raise ValueError("initial plan normalization lost the actual sequence guard")
    if target in {0, 52}:
        return roles
    return roles.replace(
        source,
        source.replace(
            "general_initial_plan(general_expected_sequence, server_to_beacon_chain(main_root))",
            f"general_prefix_{target}(server_to_beacon_chain(main_root))",
        ),
    )


def check_cached_callsite(roles, continuation, environment):
    """Compose the universal tag lemma with the sole owned, unchanged cache."""
    check_initial_plan_cases(roles)
    normalize = lambda text: re.sub(
        r"\s+", "", re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    )
    if (
        len(
            re.findall(
                r"\bgeneral_cache\b", re.sub(r"\(\*.*?\*\)", "", roles, flags=re.S)
            )
        )
        != 3
    ):
        raise ValueError("admitted cache gained another binding, use or publication")
    validated_worker_roles(roles)
    # This checks the unique producer, complete immutable argument substitution,
    # and separate fresh owner product. It assumes no root/key injectivity.
    inline_owned_handoff(roles, continuation, environment)
    expected = """let GeneralAdmissionContinue(agreement: authenticated_registration_session_t) =
      in(general_admitted_states, (=agreement, associated_data: bitstring,
        claimed: key_id, receive_state(counter: sequence, chain: bitstring, cache: receive_cache),
        send_chain: bitstring));
      event GeneralContinuationStarted(agreement, counter, chain, cache);
      in(c, mode: bitstring);
      if mode = general_check_initial() then (
        let initial_result = general_cache_pop(counter, cache) in
        if initial_result <> general_cache_missing() then
          event GeneralInitialTargetRetained(agreement, counter)
      ) else
        if mode = general_use_cached() then (
          in(c, frame: bitstring);
          let crypto_frame(ciphertext, tag, commitment, target, =SERVER_KEY_ID) = frame in
          let general_cached_result(material, remaining_cache) = general_cache_pop(target, cache) in
          let opened = open_frame(material, associated_data, target, SERVER_KEY_ID, frame) in
          event GeneralCachedAccepted(agreement, target, opened, frame);"""
    if normalize(continuation).count(normalize(expected)) != 1:
        raise ValueError(
            "first cached-success site no longer uses the exact admitted cache"
        )
    if continuation.count("event GeneralCachedAccepted(") != 2:
        raise ValueError("cached success event acquired another producer")


def project_cached_target(continuation, index, target, cached_target):
    """Project the sole cached antecedent to its literal decoded sequence."""
    if index not in {10, 12, 15} or cached_target not in cached_query_cases(
        index, target
    ):
        raise ValueError(
            "cached receiver projection is not an origin case or concrete witness"
        )
    if cached_target is None:
        return continuation
    anchor = "let GeneralAdmissionContinueDirect("
    if continuation.count(anchor) != 1:
        raise ValueError(
            "cached projection requires the exact owned direct continuation"
        )
    before, direct = continuation.split(anchor)
    decoded = "      let crypto_frame(ciphertext, tag, commitment, target, =SERVER_KEY_ID) = frame in\n"
    lookup = "      let general_cached_result(material, remaining_cache) = general_cache_pop(target, cache) in"
    event = "      event GeneralCachedAccepted(agreement, target, opened, frame);"
    if direct.count(decoded + lookup) != 1 or direct.count(event) != 1:
        raise ValueError("cached projection lost its decoded target or sole antecedent")
    guarded = (
        decoded
        + f"      if target = {sequence(cached_target)} then\n"
        + lookup.replace(
            "general_cache_pop(target,", f"general_cache_pop({sequence(cached_target)},"
        )
    )
    return before + anchor + direct.replace(decoded + lookup, guarded)


def project_future_safety(continuation, index):
    """Allow the same future input after every non-initial public mode."""
    if index not in {11, 20}:
        raise ValueError("future overapproximation cannot serve other obligations")
    normalize = lambda text: re.sub(
        r"\s+", "", re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    )
    future = """let GeneralAdmissionFuture(
      agreement: authenticated_registration_session_t, associated_data: bitstring,
      counter: sequence, chain: bitstring, cache: receive_cache, send_chain: bitstring
    ) =
      in(c, frame: bitstring);
      let crypto_frame(ciphertext, tag, commitment, =next_sequence(counter), =SERVER_KEY_ID) = frame in
      let opened = open_frame(ratchet_material(chain), associated_data,
        next_sequence(counter), SERVER_KEY_ID, frame) in
      event GeneralFutureAccepted(agreement, next_sequence(counter), opened, frame)."""
    if normalize(continuation).count(normalize(future)) != 1:
        raise ValueError("future body now reads changed state or has another effect")
    anchor = "let GeneralAdmissionContinueDirect("
    if continuation.count(anchor) != 1:
        raise ValueError("future safety requires the same owned continuation")
    before, direct = continuation.split(anchor)
    marker = "    if mode = general_use_cached() then (\n"
    if direct.count(marker) != 1:
        raise ValueError("future safety lost the exact cached/direct branch")
    head, tail = direct.split(marker)
    expected = """in(c, frame: bitstring);
      let crypto_frame(ciphertext, tag, commitment, target, =SERVER_KEY_ID) = frame in
      let general_cached_result(material, remaining_cache) = general_cache_pop(target, cache) in
      let opened = open_frame(material, associated_data, target, SERVER_KEY_ID, frame) in
      event GeneralCachedAccepted(agreement, target, opened, frame);
      let replay_result = general_cache_pop(target, remaining_cache) in
      if replay_result = general_cache_missing() then
        event GeneralReplayRejected(agreement, target);
        GeneralAdmissionFuture(agreement, associated_data, counter, chain, remaining_cache, send_chain)
      else
        let general_cached_result(replayed_material, replayed_cache) = replay_result in
        let replayed = open_frame(replayed_material, associated_data, target, SERVER_KEY_ID, frame) in
        event GeneralReplayAccepted(agreement, target)
    ) else
      GeneralAdmissionFuture(agreement, associated_data, counter, chain, cache, send_chain)."""
    if normalize(tail) != normalize(expected):
        raise ValueError(
            "future safety tail no longer preserves owner and live context"
        )
    # Failed cached attempts also gain a future opportunity. This is a stronger
    # safety process; it is never used to witness progress or cached acceptance.
    return (
        before
        + anchor
        + head
        + "    GeneralAdmissionFuture(agreement, associated_data, counter, chain, cache, send_chain).\n"
    )


def instantiate_query(query, index, target, cached_target=None):
    if index == 23:
        header, body = query.split(";", 1)
        marker = "general_cached_sequence_coverage(qga_seq)"
        if body.count(marker) != 1:
            raise ValueError("cached coverage marker changed")
        conclusion = cached_coverage_conclusion(target)
        if conclusion is None:
            return header + ";" + body.split("==>", 1)[0].rstrip() + "."
        query = query.replace(marker, conclusion)
    if cached_target is not None:
        if index not in {10, 12, 15} or cached_target not in cached_query_cases(
            index, target
        ):
            raise ValueError("cached target outside exact source prefix")
        header, body = query.split(";", 1)
        declarations = [
            decl
            for decl in header.removeprefix("query ").split(",")
            if decl.strip() != "qga_seq: sequence"
        ]
        query = (
            "query "
            + ",".join(declarations)
            + ";"
            + re.sub(r"\bqga_seq\b", sequence(cached_target), body)
        )

    query = query.replace("general_expected_case_sequence()", sequence(target))
    if index in INITIAL_SPECIALIZED | FUTURE_SPECIALIZED:
        header, body = query.split(";", 1)
        declarations = [
            decl
            for decl in header.removeprefix("query ").split(",")
            if decl.strip() != "qga_seq: sequence"
        ]
        value = sequence(target + (index in FUTURE_SPECIALIZED))
        query = (
            "query "
            + ",".join(declarations)
            + ";"
            + re.sub(r"\bqga_seq\b", value, body)
        )
    if (payload := selected_witness_payload(index, target)) is not None:
        header, body = query.split(";", 1)
        declarations = [
            decl
            for decl in header.removeprefix("query ").split(",")
            if decl.strip() != "qga_payload: bitstring"
        ]
        query = (
            "query "
            + ",".join(declarations)
            + ";"
            + re.sub(r"\bqga_payload\b", payload, body)
        )
    if "general_expected_case_sequence" in query:
        raise ValueError("uninstantiated sequence guard marker")
    return query


def validated_worker_roles(roles):
    """Check the entire private send transition; do not erase any origin event."""
    code = re.sub(r"\s+", "", re.sub(r"\(\*.*?\*\)", "", roles, flags=re.S))
    worker = """
let GeneralAdmissionSend() =
  in(general_send_states, (agreement: authenticated_registration_session_t,
    associated_data: bitstring, assigned: key_id, target: sequence,
    chain: bitstring, prior_material: receive_cache, send_peer_chain: bitstring)) [precise];
  in(c, application: bitstring);
  let material = ratchet_material(chain) in
  let frame = seal_frame(material, associated_data, target, SERVER_KEY_ID, application) in
  event GeneralAdmissionRecordOrigin(agreement, target, application, frame, assigned) [];
  event GeneralAdmissionPlanOrigin(agreement, target, send_peer_chain,
    ratchet_next(chain), prior_material, material) [];
  out(c, frame);
  out(general_send_states, (agreement, associated_data, assigned, next_sequence(target),
    ratchet_next(chain), receive_cache_entry(target, material, prior_material), send_peer_chain)).
"""
    if code.count(re.sub(r"\s+", "", worker)) != 1:
        raise ValueError("private send worker transition changed")
    initial = """
      event GeneralAdmissionPlanOrigin(establishment_authenticated_session(main_server_establishment),
        first_sequence(), beacon_to_server_chain(main_root), ratchet_next(main_server_chain_1),
        general_expected_cache_1, main_server_material_1) [];
      out(c, main_response);
      out(general_send_states, (
        establishment_authenticated_session(main_server_establishment),
        main_associated_data, main_assigned_key_id, next_sequence(first_sequence()),
        ratchet_next(main_server_chain_1),
        receive_cache_entry(first_sequence(), main_server_material_1, general_expected_cache_1),
        beacon_to_server_chain(main_root)))
"""
    if code.count(re.sub(r"\s+", "", initial)) != 1:
        raise ValueError("initial send-token provenance or publication order changed")
    if (
        code.count("freegeneral_send_states:channel[private].") != 1
        or code.count("in(general_send_states,") != 1
        or code.count("out(general_send_states,") != 2
        or code.count("GeneralAdmissionSend()") != 1
    ):
        raise ValueError("private send token acquired another owner or producer")
    for name in ("GeneralAdmissionRecordOrigin", "GeneralAdmissionPlanOrigin"):
        if len(re.findall(r"\bevent " + name + r"\(", roles)) != 3:
            raise ValueError("send-origin event inventory changed")
    receive_guard = """
    if general_sequence = general_expected_sequence then
    let general_plan(general_target_material, general_next_chain, general_cache) =
      general_initial_plan(general_expected_sequence, server_to_beacon_chain(main_root)) in
"""
    if code.count(re.sub(r"\s+", "", receive_guard)) != 1:
        raise ValueError(
            "initial-plan constant substitution lost its exact equality guard"
        )
    opening_gate = """
    let main_opened_initial = open_frame(general_target_material,
      main_associated_data, general_sequence, SERVER_KEY_ID, main_initial_frame) in
    if general_sequence = first_sequence() then
    let main_expected_binding =
"""
    if code.count(re.sub(r"\s+", "", opening_gate)) != 1:
        raise ValueError(
            "initial sequence-one gate or decrypt-before-gate order changed"
        )
    return roles


def sender_projection_parameters(index, target, cached_target=None):
    """Only targets at/before cutoff may use the stronger next-chain disclosure."""
    if not 1 <= index <= 23 or not 0 <= target <= 52:
        raise ValueError("sender projection query or target outside the checked family")
    admitted = 1 <= target <= 51
    cached = 2 <= target <= 51
    witness = index in {3, 13} and target == 1
    cutoff = min(51, max(1, target))
    if index in {11, 13, 20} and admitted:
        cutoff = target + 1
    records = set()
    plans = set()
    if index == 2 and admitted:
        records.add(target)
    if index == 9 and admitted:
        plans.add(target)
    if index == 10 and cached:
        if cached_target is None:
            records.update(range(1, target))
        elif cached_target in cached_query_cases(index, target):
            records.add(cached_target)
        else:
            raise ValueError("cached sender projection outside exact prefix")
    elif cached_target is not None and not (
        index in {12, 15} and cached_target in cached_query_cases(index, target)
    ):
        raise ValueError("cached sender projection used for a different query")
    if index == 11 and admitted:
        records.add(target + 1)
    return cutoff, records, plans, witness


def single_owner_witness_main(main):
    """An existential trace needs one honest owner pair and no scheduled extras."""
    for name in ("GeneralAdmissionBeacon", "GeneralAdmissionServer"):
        marker = "!" + name + "("
        if main.count(marker) != 1:
            raise ValueError("finite owner witness role inventory changed")
        main = main.replace(marker, name + "(")
    for marker in ("!MaliciousBeacon()", "!MaliciousServer()"):
        if main.count(marker) != 1:
            raise ValueError("finite owner witness malicious role inventory changed")
        main = main.replace(marker, "0")
    marker = "!GeneralPublicAdmissionWitness("
    if main.count(marker) != 1:
        raise ValueError("finite owner witness public strategy inventory changed")
    return main.replace(marker, "GeneralPublicAdmissionWitness(")


def project_sender_suffix(roles, main, index, target, cached_target=None):
    """Unfold the owned prefix; simulate its public suffix from the actual chain."""
    roles = validated_worker_roles(roles)
    if main.count("!GeneralAdmissionSend()") != 1:
        raise ValueError("unique source worker replication changed")
    cutoff, records, plans, witness = sender_projection_parameters(
        index, target, cached_target
    )
    anchor = "      out(general_send_states, ("
    terminal = "beacon_to_server_chain(main_root)))"
    if roles.count(anchor) != 1:
        raise ValueError("source initial token boundary changed")
    start = roles.index(anchor)
    if roles[start:].count(terminal) != 1:
        raise ValueError("source initial token terminator changed")
    end = roles.index(terminal, start) + len(terminal)
    chain = "ratchet_next(main_server_chain_1)"
    cache = "receive_cache_entry(first_sequence(), main_server_material_1, general_expected_cache_1)"
    lines = []
    for i in range(2, cutoff + 1):
        application = f"general_cutoff_application_{i}"
        material = f"general_cutoff_material_{i}"
        frame = f"general_cutoff_frame_{i}"
        next_chain = f"general_cutoff_next_{i}"
        lines += [
            f"      in(c, {application}: bitstring);",
            f"      let {material} = ratchet_material({chain}) in",
            f"      let {next_chain} = ratchet_next({chain}) in",
            f"      let {frame} = seal_frame({material}, main_associated_data, {sequence(i)}, SERVER_KEY_ID, {application}) in",
        ]
        if i in records:
            lines.append(
                f"      event GeneralAdmissionRecordOrigin(establishment_authenticated_session(main_server_establishment), {sequence(i)}, {application}, {frame}, main_assigned_key_id) [];"
            )
        if i in plans:
            lines.append(
                f"      event GeneralAdmissionPlanOrigin(establishment_authenticated_session(main_server_establishment), {sequence(i)}, beacon_to_server_chain(main_root), {next_chain}, {cache}, {material}) [];"
            )
        lines.append(f"      out(c, {frame});")
        chain = next_chain
        cache = f"receive_cache_entry({sequence(i)}, {material}, {cache})"
    # A witness must be an actual prefix of the reference process. Only safety
    # proofs receive the extra chain, which permits every adaptive later send.
    lines.append(
        "      0"
        if witness
        else f"      out(c, ({chain}, {sequence(cutoff + 1)}, main_associated_data, main_assigned_key_id))"
    )
    projected_roles = roles[:start] + "\n".join(lines) + roles[end:]
    before, after = main.split("!GeneralAdmissionSend()")
    projected_main = before + "0" + after
    if witness:
        projected_main = single_owner_witness_main(projected_main)
        if index == 3 and target == 1:
            marker = "GeneralPublicAdmissionWitness(first_sequence())"
            if projected_main.count(marker) != 1:
                raise ValueError("initial direct-delivery witness changed")
            projected_main = projected_main.replace(marker, "0")
    return projected_roles, projected_main, witness, cutoff


def inline_owned_handoff(roles, continuation, environment):
    """Erase only the private rendezvous paired by the fresh product owner tag."""
    normalize = lambda text: re.sub(r"\s+", "", text)
    beacon = roles.split("let GeneralAdmissionBeacon(", 1)[1].split(
        "let GeneralAdmissionServer(", 1
    )[0]
    if beacon.count("new main_registration_session: bitstring;") != 1:
        raise ValueError("admitted owner tag is no longer separately fresh")
    transcript = re.search(
        r"let main_beacon_establishment = establishment_transcript\((.*?)\) in",
        beacon,
        re.S,
    )
    if (
        transcript is None
        or normalize(transcript.group(1)).split(",")[-1] != "main_registration_session"
    ):
        raise ValueError("admitted agreement no longer carries its own fresh owner tag")
    projection = re.findall(
        r"establishment_authenticated_session\(establishment_transcript\((.*?)\)\)\s*=\s*authenticated_registration_session\((.*?)\)\.",
        environment,
        re.S,
    )
    expected_inputs = [
        "mr_server",
        "mr_beacon",
        "mr_init",
        "mr_id",
        "mr_prekey",
        "mr_one_time",
        "mr_pq",
        "mr_ephemeral",
        "mr_kem",
        "mr_frame",
        "mr_response",
        "mr_root_input",
        "mr_root",
        "mr_ad",
        "mr_assigned",
        "mr_pinned",
        "mr_session",
        "mr_origin",
    ]
    expected_outputs = [
        expected_inputs[i] for i in [0, 1, 2, 3, 4, 5, 6, 12, 13, 15, 17]
    ]
    if len(projection) != 1 or [
        normalize(part).split(",") for part in projection[0]
    ] != [expected_inputs, expected_outputs]:
        raise ValueError("ordinary agreement product lost its exact owner projection")
    constructor = (
        "fun authenticated_registration_session(bitstring,bitstring,"
        "beaconcrypt_core__pqxdh__t_InitKex,beaconcrypt_core__pqxdh__t_RegistrationId,"
        "bitstring,bitstring,bitstring,bitstring,bitstring,key_id,bitstring)"
        ":authenticated_registration_session_t[data]."
    )
    if normalize(environment).count(normalize(constructor)) != 1:
        raise ValueError("owner agreement ceased to be the exact ordinary data product")

    producer = """    (out(general_admitted_states, (establishment_authenticated_session(main_beacon_establishment),
      main_associated_data, main_assigned_key_id,
      receive_state(general_sequence, general_next_chain, general_cache),
      beacon_to_server_chain(main_root)))
    | (if general_continue then GeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment)))
"""
    consumer = """let GeneralAdmissionContinue(agreement: authenticated_registration_session_t) =
  in(general_admitted_states, (=agreement, associated_data: bitstring,
    claimed: key_id, receive_state(counter: sequence, chain: bitstring, cache: receive_cache),
    send_chain: bitstring));
"""
    if roles.count(producer) != 1 or roles.count("out(general_admitted_states,") != 1:
        raise ValueError("owned handoff producer, tuple or parallel scope changed")
    if (
        continuation.count(consumer) != 1
        or continuation.count("in(general_admitted_states,") != 1
    ):
        raise ValueError("owned handoff consumer or bound tuple changed")
    body = continuation.split(consumer, 1)[1]
    if "let General" in body:
        raise ValueError("owned continuation no longer ends at its existing body")
    direct = """
let GeneralAdmissionContinueDirect(agreement: authenticated_registration_session_t,
 associated_data: bitstring, claimed: key_id, counter: sequence, chain: bitstring,
 cache: receive_cache, send_chain: bitstring) =
""" + body
    call = """    ((if general_continue then GeneralAdmissionContinueDirect(
      establishment_authenticated_session(main_beacon_establishment),
      main_associated_data, main_assigned_key_id, general_sequence, general_next_chain,
      general_cache, beacon_to_server_chain(main_root)))
"""
    return roles.replace(producer, call), continuation + direct


def check_case(proverif, timeout, target, log_dir, query_indices):
    main = (HERE / "general-registration-admission.pv").read_text()
    anchor = "GeneralAdmissionBeacon(BEACON_RECORD_SECRET, first_sequence(), true)"
    if main.count(anchor) != 1:
        raise ValueError("general admission main role anchor changed")
    main = main.replace(
        anchor,
        f"GeneralAdmissionBeacon(BEACON_RECORD_SECRET, {sequence(target)}, true)",
    )
    case = log_dir / f"target-{target}.pv"
    case.write_text(main)
    command = [proverif]
    for lib in [
        "production-transcript-interface.pvl",
        "crypto.pvl",
        "extraction/lib.pvl",
        "environment.pvl",
        "general-registration-cache.pvl",
    ]:
        command.extend(["-lib", str(HERE / lib)])
    queries = re.findall(
        r"(?ms)^query .*?\.$",
        (HERE / "general-registration-admission-queries.pvl").read_text(),
    )
    if len(queries) != 23:
        raise ValueError("general admission query inventory changed")
    if 10 in query_indices or (23 in query_indices and 1 <= target <= 51):
        check_cached_callsite(
            (HERE / "general-registration-admission.pvl").read_text(),
            (HERE / "general-registration-continuation.pvl").read_text(),
            (HERE / "environment.pvl").read_text(),
        )
    results = []
    # ProVerif retains solver state between queries. A fresh process per exact
    # statement bounds memory without changing the process, theory, or query.
    with (log_dir / f"target-{target}.log").open("w") as combined:
        selected_queries = [
            (index, query, cached_target)
            for index in query_execution_order(query_indices)
            for query in [queries[index - 1]]
            for cached_target in cached_query_cases(index, target)
        ]
        for index, query, cached_target in selected_queries:
            suffix = "" if cached_target is None else f"-cached-{cached_target}"
            query_stem = f"target-{target}-query-{index}{suffix}"
            if index == 23 and 1 <= target <= 51:
                component, expected_component = local_cached_range(query, target)
                component_file = log_dir / f"{query_stem}-local-cache-range.pv"
                component_file.write_text(component)
                with (log_dir / f"{query_stem}-local-cache-range.log").open(
                    "w+"
                ) as output:
                    subprocess.run(
                        command + [str(component_file)],
                        check=True,
                        timeout=timeout,
                        stdout=output,
                        stderr=subprocess.STDOUT,
                    )
                    output.seek(0)
                    text = output.read()
                found = re.findall(r"^RESULT (.+) is (true|false)\.$", text, re.M)
                if found != [expected_component]:
                    raise ValueError(
                        "local material-parametric cached-range result differs"
                    )
                combined.write(f"LOCAL CACHE RANGE COMPONENT target={target}\n" + text)
                combined.flush()
                results.extend(found)
                continue
            # Admission events precede the private continuation, which has no
            # network output. Its causal-prefix projection preserves queries 1..9.
            query_main = (
                main
                if index > 9 and index not in {18, 19}
                else main.replace(
                    f"GeneralAdmissionBeacon(BEACON_RECORD_SECRET, {sequence(target)}, true)",
                    f"GeneralAdmissionBeacon(BEACON_RECORD_SECRET, {sequence(target)}, false)",
                )
            )
            if index in {3, 7, 12, 13, 15}:
                anchor = "| !MaliciousServer()"
                if query_main.count(anchor) != 1:
                    raise ValueError("public witness composition anchor changed")
                query_main = query_main.replace(
                    anchor,
                    anchor
                    + f"\n    | !GeneralPublicAdmissionWitness({sequence(target)})",
                )
            roles, query_main, finite_witness, cutoff = project_sender_suffix(
                (HERE / "general-registration-admission.pvl").read_text(),
                query_main,
                index,
                target,
                cached_target,
            )
            roles = project_initial_plan(roles, query_main, target)
            continuation = (HERE / "general-registration-continuation.pvl").read_text()
            if index > 9 and index not in {18, 19}:
                roles, continuation = inline_owned_handoff(
                    roles, continuation, (HERE / "environment.pvl").read_text()
                )
            if cached_target is not None:
                continuation = project_cached_target(
                    continuation, index, target, cached_target
                )
            if index in {11, 20}:
                continuation = project_future_safety(continuation, index)
            continuation_file = log_dir / f"{query_stem}-continuation.pvl"
            continuation_file.write_text(continuation)
            query_case = log_dir / f"{query_stem}.pv"
            query_case.write_text(query_main)
            role_file = log_dir / f"{query_stem}-roles.pvl"
            role_file.write_text(roles)
            combined.write(
                f"SENDER PROJECTION target={target} query={index} cached_target={cached_target} cutoff={cutoff} mode={'finite-witness' if finite_witness else 'actual-next-chain-disclosure'}\n"
            )
            query_file = log_dir / f"{query_stem}.pvl"
            query_file.write_text(
                instantiate_query(query, index, target, cached_target) + "\n"
            )
            with (log_dir / f"{query_stem}.log").open("w+") as output:
                subprocess.run(
                    command
                    + [
                        "-lib",
                        str(continuation_file),
                        "-lib",
                        str(role_file),
                        "-lib",
                        str(HERE / "general-registration-public-witness.pvl"),
                        "-lib",
                        str(query_file),
                        str(query_case),
                    ],
                    check=True,
                    timeout=timeout,
                    stdout=output,
                    stderr=subprocess.STDOUT,
                )
                output.seek(0)
                text = output.read()
                combined.write(text)
                combined.flush()
                found = re.findall(r"^RESULT (.+) is (true|false)\.$", text, re.M)
                if len(found) != 1:
                    raise ValueError(
                        f"target {target}, query {index}: expected one conclusive result"
                    )
                if finite_witness and (
                    found[0][1] != "false" or text.count("A trace has been found.") != 1
                ):
                    raise ValueError(
                        "finite reachability witness lacks its concrete trace"
                    )
                if finite_witness:
                    combined.write(
                        f"FINITE REACHABILITY WITNESS target={target} query={index}\n"
                    )
                results.extend(found)
    # Full result strings protect against a different proved event being counted.
    expected = [
        (
            "inj-event(GeneralAdmissionCompleted(qga_agreement,qga_seq,qga_payload,qga_frame,qga_response,qga_claimed)) ==> inj-event(GeneralAdmissionSessionOrigin(qga_agreement,qga_assigned))",
            "true",
        ),
        (
            "inj-event(GeneralAdmissionCompleted(qga_agreement,qga_seq,qga_payload,qga_frame,qga_response,qga_claimed)) ==> inj-event(GeneralAdmissionRecordOrigin(qga_agreement,qga_seq,qga_payload,qga_frame,qga_assigned))",
            "true",
        ),
        (
            "not event(GeneralAdmissionCompleted(qga_agreement,qga_seq,qga_payload,qga_frame,qga_response,qga_claimed))",
            "false" if target == 1 else "true",
        ),
        (
            "not event(GeneralAdmissionCompleted(qga_agreement,qga_seq,registration_payload(qga_binding,general_empty_suffix),qga_frame,qga_response,qga_claimed))",
            "true",
        ),
        (
            "not event(GeneralAdmissionCompleted(qga_agreement,qga_seq,general_short_payload(qga_body),qga_frame,qga_response,qga_claimed))",
            "true",
        ),
        (
            "not event(GeneralAdmissionCompleted(qga_agreement,qga_seq,qga_payload,general_short_payload(qga_body),qga_response,qga_claimed))",
            "true",
        ),
        (
            "not event(GeneralAdmissionRelabelled(qga_seq,qga_payload))",
            "true",
        ),
        (
            "event(GeneralAdmissionCompleted(qga_agreement,qga_seq,registration_payload(beaconcrypt_core__pqxdh__RegistrationKeyIdBinding(sender_id_le64(qga_actual_prefix)),general_nonempty(qga_body)),qga_frame,qga_response,qga_claimed)) ==> qga_actual_prefix = qga_claimed",
            "true",
        ),
        (
            "inj-event(GeneralAdmissionPoststate(qga_agreement,qga_seq,qga_send_chain,qga_next_chain,qga_cache,qga_target_material)) ==> inj-event(GeneralAdmissionPlanOrigin(qga_agreement,qga_seq,qga_send_chain,qga_next_chain,qga_cache,qga_target_material))",
            "true",
        ),
        (
            "inj-event(GeneralCachedAccepted(qga_agreement,qga_seq,qga_payload,qga_frame)) ==> inj-event(GeneralAdmissionRecordOrigin(qga_agreement,qga_seq,qga_payload,qga_frame,qga_assigned))",
            "true",
        ),
        (
            "inj-event(GeneralFutureAccepted(qga_agreement,qga_seq,qga_payload,qga_frame)) ==> inj-event(GeneralAdmissionRecordOrigin(qga_agreement,qga_seq,qga_payload,qga_frame,qga_assigned))",
            "true",
        ),
        (
            "not event(GeneralCachedAccepted(qga_agreement,qga_seq,qga_payload,qga_frame))",
            "true",
        ),
        (
            "not event(GeneralFutureAccepted(qga_agreement,qga_seq,qga_payload,qga_frame))",
            "false" if target == 1 else "true",
        ),
        ("not event(GeneralReplayAccepted(qga_agreement,qga_seq))", "true"),
        (
            "not event(GeneralReplayRejected(qga_agreement,qga_seq))",
            "true",
        ),
        ("not event(GeneralInitialTargetRetained(qga_agreement,qga_seq))", "true"),
        (
            "inj-event(GeneralContinuationStarted(qga_agreement,qga_seq,qga_chain,qga_cache)) ==> inj-event(GeneralAdmissionPoststate(qga_agreement,qga_seq,qga_send_chain,qga_chain,qga_cache,qga_target_material))",
            "true",
        ),
    ]
    expected.extend(
        [
            (
                "event(GeneralAdmissionCompleted(qga_agreement,qga_seq,qga_payload,qga_frame,qga_response,qga_claimed)) ==> qga_seq = CASE",
                "true",
            ),
            (
                "event(GeneralAdmissionPoststate(qga_agreement,qga_seq,qga_send_chain,qga_next_chain,qga_cache,qga_target_material)) ==> qga_seq = CASE",
                "true",
            ),
            (
                "event(GeneralFutureAccepted(qga_agreement,qga_seq,qga_payload,qga_frame)) ==> qga_seq = next_sequence(CASE)",
                "true",
            ),
            (
                "event(GeneralInitialTargetRetained(qga_agreement,qga_seq)) ==> qga_seq = CASE",
                "true",
            ),
            (
                "event(GeneralContinuationStarted(qga_agreement,qga_seq,qga_chain,qga_cache)) ==> qga_seq = CASE",
                "true",
            ),
        ]
    )
    coverage_event = (
        "event(GeneralCachedAccepted(qga_agreement,qga_seq,qga_payload,qga_frame))"
    )
    conclusion = cached_coverage_conclusion(target, printed=True)
    expected.append(
        (
            (
                coverage_event + " ==> " + conclusion
                if conclusion is not None
                else "not " + coverage_event
            ),
            "true",
        )
    )
    instantiated = []
    for index in query_execution_order(query_indices):
        name, polarity = expected[index - 1]
        if index == 23 and 1 <= target <= 51:
            _, (name, polarity) = local_cached_range(queries[index - 1], target)
        if index in INITIAL_SPECIALIZED | FUTURE_SPECIALIZED:
            value = sequence(target + (index in FUTURE_SPECIALIZED)).replace("()", "")
            name = re.sub(r"\bqga_seq\b", value, name)
        name = name.replace("CASE", sequence(target).replace("()", ""))
        if (payload := selected_witness_payload(index, target)) is not None:
            printed_payload = payload.replace(
                "SERVER_KEY_ID", "SERVER_KEY_ID[]"
            ).replace("INITIAL_SECRET", "INITIAL_SECRET[]")
            name = re.sub(r"\bqga_payload\b", printed_payload, name)

        if index in query_indices:
            for cached_target in cached_query_cases(index, target):
                selected_name = (
                    name
                    if cached_target is None
                    else re.sub(
                        r"\bqga_seq\b", sequence(cached_target).replace("()", ""), name
                    )
                )
                instantiated.append((selected_name, polarity))
    expected = instantiated
    if results != expected:
        raise ValueError(f"target {target}: exact query results differ: {results!r}")
    return target, len(results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--timeout", type=int, default=240)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--target", type=int, action="append")
    parser.add_argument("--query", type=int, action="append")
    parser.add_argument("--log-dir", type=Path)
    args = parser.parse_args()
    check_causal_projection()
    check_public_witness()
    subprocess.run(
        ["python3", str(HERE / "generate-general-registration.py"), "--check"],
        check=True,
    )
    targets = args.target if args.target is not None else list(range(53))
    query_indices = args.query if args.query is not None else list(range(1, 24))
    if len(set(query_indices)) != len(query_indices) or any(
        index < 1 or index > 23 for index in query_indices
    ):
        raise ValueError("query selection must be distinct indices 1..23")
    query_indices = sorted(
        set(query_indices)
        | {
            SEQUENCE_GUARDS[index]
            for index in query_indices
            if index in SEQUENCE_GUARDS
        }
    )
    if any(target < 0 or target > 52 for target in targets):
        raise ValueError("target outside checked admission boundary 0..52")
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-general-admission-"
    ) as temporary:
        log_dir = args.log_dir or Path(temporary)
        log_dir.mkdir(parents=True, exist_ok=True)

        def run(target):
            return check_case(
                args.proverif, args.timeout, target, log_dir, query_indices
            )

        total_results = 0
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            for target, count in pool.map(run, targets):
                total_results += count
                print(
                    f"general registration target {target}: {count} exact results passed",
                    flush=True,
                )
    print(
        f"general registration: {len(targets)} cases, {total_results} exact results passed"
    )


if __name__ == "__main__":
    main()
