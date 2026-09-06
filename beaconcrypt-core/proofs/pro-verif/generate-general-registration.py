#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Generate the exhaustive empty-cache admission equations and honest send prefix.

The old first/third-sequence roles remain unchanged. This separate model derives
its Phase-1/Phase-2 code from those reviewed role templates, replacing only the
initial receive plan and the server's application-send continuation.
"""

from pathlib import Path
import argparse
import re

HERE = Path(__file__).resolve().parent
LIMIT = 51


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise ValueError(f"reviewed role anchor is no longer unique: {old[:100]!r}")
    return text.replace(old, new, 1)


def sequence(n):
    if n == 0:
        return "general_zero_sequence()"
    return "next_sequence(" * (n - 1) + "first_sequence()" + ")" * (n - 1)


def generate():
    env = (HERE / "environment.pvl").read_text()
    beacon = env.split("let MainLaterBeacon(", 1)[1].split("let MainLaterServer(", 1)[0]
    beacon = "let GeneralAdmissionBeacon(" + beacon
    beacon = replace_once(
        beacon,
        "main_beacon_record_secret: bitstring)",
        "main_beacon_record_secret: bitstring, general_expected_sequence: sequence, general_continue: bool)",
    )
    start = beacon.index("    let main_server_chain_1 =")
    stop = beacon.index("    let main_expected_binding =", start)
    beacon = (
        beacon[:start]
        + """    let crypto_frame(general_cipher, general_tag, general_commitment,
      general_sequence, =SERVER_KEY_ID) = main_initial_frame in
    if general_sequence = general_expected_sequence then
    let general_plan(general_target_material, general_next_chain, general_cache) =
      general_initial_plan(general_expected_sequence, server_to_beacon_chain(main_root)) in
    let main_opened_initial = open_frame(general_target_material,
      main_associated_data, general_sequence, SERVER_KEY_ID, main_initial_frame) in
"""
        + beacon[stop:]
    )
    beacon = replace_once(
        beacon,
        "    let registration_payload(=main_expected_binding, main_initial_plaintext) = main_opened_initial in",
        "    let registration_payload(=main_expected_binding, general_nonempty(main_initial_plaintext)) = main_opened_initial in",
    )
    start = beacon.index("    event BeaconAnyCommitted(")
    beacon = (
        beacon[:start]
        + """    event GeneralAdmissionCompleted(establishment_authenticated_session(main_beacon_establishment),
      general_sequence, main_opened_initial, main_initial_frame, main_response,
      main_assigned_key_id);
    event GeneralAdmissionPoststate(establishment_authenticated_session(main_beacon_establishment),
      general_sequence, beacon_to_server_chain(main_root),
      general_next_chain, general_cache, general_target_material);
    (* Private state handoff is uniform across every admitted sequence. *)
    (out(general_admitted_states, (establishment_authenticated_session(main_beacon_establishment),
      main_associated_data, main_assigned_key_id,
      receive_state(general_sequence, general_next_chain, general_cache),
      beacon_to_server_chain(main_root)))
    | (if general_continue then GeneralAdmissionContinue(establishment_authenticated_session(main_beacon_establishment)))
    | if main_assigned_key_id = SERVER_KEY_ID then
      event GeneralAdmissionRelabelled(general_sequence, main_opened_initial))
  ).
"""
    )
    server = env.split("let MainLaterServer(", 1)[1]
    server = "let GeneralAdmissionServer(" + server
    stop = server.index("      let main_server_chain_2 =")
    # Retain the reviewed server's initial response and publication prefix.
    prefix = server[:stop]
    if prefix.count("registration_payload(main_binding, main_initial_secret)") != 3:
        raise ValueError("reviewed initial plaintext and origin anchors changed")
    prefix = prefix.replace(
        "registration_payload(main_binding, main_initial_secret)",
        "registration_payload(main_binding, general_nonempty(main_initial_secret))",
    )
    # The separate query events keep old main gates and secrecy fixtures intact.
    prefix = prefix.replace(
        "event ServerAuthenticatedSessionCommitted(",
        "event GeneralAdmissionSessionOrigin(",
    )
    prefix = prefix.replace(
        "event AuthenticatedRegistrationRecordSent(",
        "event GeneralAdmissionRecordOrigin(",
    )
    prefix = replace_once(
        prefix,
        "      out(c, main_response);",
        """      let general_expected_cache_1 = receive_cache_empty() in
      event GeneralAdmissionPlanOrigin(establishment_authenticated_session(main_server_establishment),
        first_sequence(), beacon_to_server_chain(main_root), ratchet_next(main_server_chain_1),
        general_expected_cache_1, main_server_material_1);
      out(c, main_response);""",
    )
    # A private linear token carries the next send state. Each worker consumes
    # one token, handles one actual application request, publishes its record,
    # and only then reinstalls the evolved token. There is no finite send cutoff.
    sends = """      out(general_send_states, (
        establishment_authenticated_session(main_server_establishment),
        main_associated_data, main_assigned_key_id, next_sequence(first_sequence()),
        ratchet_next(main_server_chain_1),
        receive_cache_entry(first_sequence(), main_server_material_1, general_expected_cache_1),
        beacon_to_server_chain(main_root)))
"""
    # This macro's outer replay if has an explicit rejection event at the end.
    end_marker = "    event RegistrationReplayRejected("
    if end_marker not in server:
        raise ValueError("reviewed replay rejection branch disappeared")
    tail_start = server.rfind("  )\n  else")
    if tail_start < 0:
        raise ValueError("reviewed replay branch terminator disappeared")
    tail = server[tail_start:]
    # Drop the final send's semicolon before closing the successful branch.
    server = prefix + sends.rstrip().removesuffix(";") + "\n" + tail
    declarations = """(* SPDX-License-Identifier: 0BSD *)
(* Generated by generate-general-registration.py; review the generator and its diff. *)
(* HB-83: exhaustive empty-cache admission, with arbitrary authenticated application terms. *)
fun general_zero_sequence(): sequence [data].
fun general_nonempty(bitstring): bitstring [data].
fun general_empty_suffix(): bitstring [data].
fun general_short_payload(bitstring): bitstring [data].
fun general_plan(bitstring, bitstring, receive_cache): bitstring [data].
event GeneralAdmissionCompleted(authenticated_registration_session_t, sequence, bitstring, bitstring, bitstring, key_id).
event GeneralAdmissionSessionOrigin(authenticated_registration_session_t, key_id).
event GeneralAdmissionRecordOrigin(authenticated_registration_session_t, sequence, bitstring, bitstring, key_id).
event GeneralAdmissionPoststate(authenticated_registration_session_t, sequence, bitstring, bitstring, receive_cache, bitstring).
event GeneralAdmissionPlanOrigin(authenticated_registration_session_t, sequence, bitstring, bitstring, receive_cache, bitstring).
event GeneralAdmissionRelabelled(sequence, bitstring).
free general_send_states: channel [private].
"""
    definitions = []
    definitions.append("""letfun general_prefix_1(chain: bitstring) =
  general_plan(ratchet_material(chain), ratchet_next(chain), receive_cache_empty()).
""")
    for n in range(2, LIMIT + 1):
        definitions.append(f"""letfun general_prefix_{n}(chain: bitstring) =
  let general_plan(previous_target, target_chain, skipped) = general_prefix_{n - 1}(chain) in
  general_plan(ratchet_material(target_chain), ratchet_next(target_chain),
    receive_cache_entry({sequence(n - 1)}, previous_target, skipped)).
""")
    definitions.append(
        "letfun general_initial_plan(target: sequence, chain: bitstring) ="
    )
    for n in range(1, LIMIT + 1):
        definitions.append(
            f"  {'if' if n == 1 else 'else if'} target = {sequence(n)} then general_prefix_{n}(chain){'.' if n == LIMIT else ''}"
        )
    worker = """
(* One token per admitted server owner; publication precedes the next request. *)
let GeneralAdmissionSend() =
  in(general_send_states, (agreement: authenticated_registration_session_t,
    associated_data: bitstring, assigned: key_id, target: sequence,
    chain: bitstring, prior_material: receive_cache, send_peer_chain: bitstring)) [precise];
  in(c, application: bitstring);
  let material = ratchet_material(chain) in
  let frame = seal_frame(material, associated_data, target, SERVER_KEY_ID, application) in
  event GeneralAdmissionRecordOrigin(agreement, target, application, frame, assigned);
  event GeneralAdmissionPlanOrigin(agreement, target, send_peer_chain,
    ratchet_next(chain), prior_material, material);
  out(c, frame);
  out(general_send_states, (agreement, associated_data, assigned, next_sequence(target),
    ratchet_next(chain), receive_cache_entry(target, material, prior_material), send_peer_chain)).
"""
    result = (
        declarations
        + "\n".join(definitions)
        + "\n"
        + worker
        + "\n"
        + beacon
        + "\n"
        + server
    )
    # Keep only each event's exact arguments in ProVerif's injectivity occurrence
    # names, avoiding every preceding application/chain/cache variable.
    return re.sub(
        r"(?m)^([ \t]+event GeneralAdmission(?:SessionOrigin|RecordOrigin|PlanOrigin|Poststate)\([^;]*?\))\s*;",
        r"\1 [];",
        result,
        flags=re.S,
    )


def generate_cache():
    """Bounded source swap removal; valid source caches have unique sequences."""
    lines = ["""(* SPDX-License-Identifier: 0BSD *)
(* Generated by generate-general-registration.py. Ordered cases cover every source cache position 0..49. *)
fun general_cached_result(bitstring, receive_cache): bitstring [data].
fun general_cache_missing(): bitstring [data].
fun general_cache_pop(sequence, receive_cache): bitstring"""]
    for index in range(50):
        variables = ["target: sequence", "material: bitstring", "tail: receive_cache"]
        for prior in range(index):
            variables.extend([f"s{prior}: sequence", f"m{prior}: bitstring"])
        cache = "receive_cache_entry(target, material, tail)"
        for prior in reversed(range(index)):
            cache = f"receive_cache_entry(s{prior}, m{prior}, {cache})"
        remaining = "tail"
        if index > 0:
            remaining = "receive_cache_entry(s0, m0, tail)"
            for prior in reversed(range(1, index)):
                remaining = f"receive_cache_entry(s{prior}, m{prior}, {remaining})"
        lines.append(
            f"{'reduc' if index == 0 else 'otherwise'} forall {', '.join(variables)};\n  general_cache_pop(target, {cache}) = general_cached_result(material, {remaining})"
        )
    lines.append(
        "otherwise forall target: sequence, cache: receive_cache;\n  general_cache_pop(target, cache) = general_cache_missing() [private].\n"
    )
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = {
        "general-registration-admission.pvl": generate(),
        "general-registration-cache.pvl": generate_cache(),
    }
    for name, generated in outputs.items():
        output = HERE / name
        if args.check:
            if not output.exists() or output.read_text() != generated:
                raise SystemExit(f"{name} differs from reviewed generator output")
        else:
            output.write_text(generated)
    if args.check:
        print(
            "general registration generated equations and roles agree (51 accepted initial targets, 50 cache positions)"
        )


if __name__ == "__main__":
    main()
