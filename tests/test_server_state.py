import copy
import json

import pytest

from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer


def register_beacon(
    server: BeaconCryptServer,
    beacon: BeaconCryptBeacon,
) -> int:
    phase_1 = beacon.generate_registration()
    assert phase_1 is not None

    response = server.register_beacon(phase_1, None)
    assert response is not None
    assert response.key_id() > 0
    assert beacon.process_initial_message(response.serialized()) == b"\xff"
    return response.key_id()


def test_json_updates_include_direction_tags_and_payloads():
    server = BeaconCryptServer(0, None)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    beacon_kid = register_beacon(server, beacon)

    outbound = b"server to beacon JSON update"
    serialized_send = server.encrypt_and_update_json(outbound, beacon_kid)
    assert serialized_send is not None
    send_update = json.loads(serialized_send)

    assert send_update["kid"] == beacon_kid
    assert send_update["seq"] == 2
    assert send_update["state"]["send_key"][:2] == [6, 8]
    assert len(send_update["state"]["send_key"][2]) == 32
    assert send_update["state"]["recv_key"][:2] == [6, 9]
    assert beacon.decrypt_server_message(bytes(send_update["data"])) == outbound

    inbound = b"beacon to server JSON update"
    ciphertext = beacon.encrypt_message_to_server(inbound)
    assert ciphertext is not None
    serialized_recv = server.decrypt_and_update_json(ciphertext)
    assert serialized_recv is not None
    recv_update = json.loads(serialized_recv)

    assert recv_update["kid"] == beacon_kid
    assert recv_update["seq"] == 1
    assert recv_update["state"]["recv_key"][:2] == [6, 9]
    assert len(recv_update["state"]["recv_key"][2]) == 32
    assert recv_update["state"]["send_key"][:2] == [6, 8]
    assert bytes(recv_update["data"]) == inbound


def test_json_update_failures_return_none():
    server = BeaconCryptServer(0, None)

    assert server.encrypt_and_update_json(b"message", 2**64 - 1) is None
    assert server.decrypt_and_update_json(b"not a frame") is None


def test_structured_and_json_updates_match_across_the_binding_boundary():
    seed = bytes([0x31]) * 32
    server = BeaconCryptServer(0, seed)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    beacon_kid = register_beacon(server, beacon)
    initial_state = server.export_state()
    assert initial_state is not None

    structured_server = BeaconCryptServer.from_state(initial_state)
    json_server = BeaconCryptServer.from_state(initial_state)

    outbound = b"compare structured and JSON encryption updates"
    structured_send = structured_server.encrypt_and_update(outbound, beacon_kid)
    serialized_send = json_server.encrypt_and_update_json(outbound, beacon_kid)
    assert structured_send is not None
    assert serialized_send is not None
    json_send = json.loads(serialized_send)

    assert structured_send.key_id() == json_send["kid"]
    assert structured_send.seq() == json_send["seq"]
    assert structured_send.data() == bytes(json_send["data"])
    assert json.loads(structured_send.state()) == json_send["state"]

    inbound = b"compare structured and JSON decryption updates"
    ciphertext = beacon.encrypt_message_to_server(inbound)
    assert ciphertext is not None
    structured_recv = structured_server.decrypt_and_update(ciphertext)
    serialized_recv = json_server.decrypt_and_update_json(ciphertext)
    assert structured_recv is not None
    assert serialized_recv is not None
    json_recv = json.loads(serialized_recv)

    assert structured_recv.key_id() == json_recv["kid"]
    assert structured_recv.seq() == json_recv["seq"]
    assert structured_recv.data() == bytes(json_recv["data"])
    assert json.loads(structured_recv.state()) == json_recv["state"]


def test_seeded_export_restore_continues_sessions_and_next_kid():
    seed = bytes([0x51]) * 32
    server = BeaconCryptServer(0, seed)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    beacon_kid = register_beacon(server, beacon)

    before_export = server.encrypt_to_beacon(b"before export", beacon_kid)
    assert before_export is not None
    assert beacon.decrypt_server_message(before_export) == b"before export"
    before_export_reply = beacon.encrypt_message_to_server(b"reply before export")
    assert before_export_reply is not None
    assert server.decrypt_beacon_message(before_export_reply) == b"reply before export"

    state = server.export_state()
    assert state is not None
    encoded = json.loads(state)
    assert encoded["identity_key"][:2] == [1, 14]
    assert len(encoded["identity_key"][2]) == 32
    assert encoded["identity_key_kid"] == 0
    assert encoded["server_kid"] == beacon_kid
    assert str(beacon_kid) in encoded["known_ids"]
    assert len(encoded["consumed_registrations"]) == 1
    assert len(encoded["consumed_registrations"][0]) == 64

    restored = BeaconCryptServer.from_state(state)
    assert restored.id_pk() == server_pk

    after_restore = restored.encrypt_to_beacon(b"after restore", beacon_kid)
    assert after_restore is not None
    assert beacon.decrypt_server_message(after_restore) == b"after restore"
    after_restore_reply = beacon.encrypt_message_to_server(b"reply after restore")
    assert after_restore_reply is not None
    assert (
        restored.decrypt_beacon_message(after_restore_reply) == b"reply after restore"
    )

    next_beacon = BeaconCryptBeacon(0, server_pk)
    assert register_beacon(restored, next_beacon) == beacon_kid + 1


def test_export_restore_preserves_cached_out_of_order_receive_keys():
    seed = bytes([0x71]) * 32
    server = BeaconCryptServer(0, seed)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    register_beacon(server, beacon)

    ciphertexts = [
        beacon.encrypt_message_to_server(message)
        for message in (b"first", b"second", b"third")
    ]
    assert all(ciphertext is not None for ciphertext in ciphertexts)
    assert server.decrypt_beacon_message(ciphertexts[2]) == b"third"

    state = server.export_state()
    assert state is not None
    encoded = json.loads(state)
    assert set(encoded["known_ids"]["1"]["ratchet"]["recv_past"]) == {"1", "2"}

    restored = BeaconCryptServer.from_state(state)
    assert restored.decrypt_beacon_message(ciphertexts[0]) == b"first"
    assert restored.decrypt_beacon_message(ciphertexts[1]) == b"second"


def test_empty_state_restore_preserves_kid_floor():
    server = BeaconCryptServer(7, None)
    server_pk = server.id_pk()
    state = server.export_state()
    assert state is not None
    encoded = json.loads(state)
    assert encoded["identity_key_kid"] == 7
    assert encoded["server_kid"] == 7
    assert encoded["known_ids"] == {}
    assert encoded["consumed_registrations"] == []

    restored = BeaconCryptServer.from_state(state)
    assert restored.id_pk() == server_pk
    beacon = BeaconCryptBeacon(7, restored.id_pk())

    assert register_beacon(restored, beacon) == 8


@pytest.mark.parametrize(
    "state",
    [
        "{}",
        "not JSON",
        '{"1": {"pk": [], "ratchet": {}}}',
    ],
)
def test_restore_rejects_invalid_state(state: str):
    with pytest.raises(ValueError, match="invalid server state"):
        BeaconCryptServer.from_state(state)


def test_restore_rejects_tampered_exported_state():
    seed = bytes([0x61]) * 32
    server = BeaconCryptServer(0, seed)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    register_beacon(server, beacon)
    state = server.export_state()
    assert state is not None
    encoded = json.loads(state)

    wrong_key_type = copy.deepcopy(encoded)
    wrong_key_type["known_ids"]["1"]["pk"][0] = 2
    short_key = copy.deepcopy(encoded)
    short_key["known_ids"]["1"]["pk"].pop()
    malformed_ratchet = copy.deepcopy(encoded)
    malformed_ratchet["known_ids"]["1"]["ratchet"]["send_key"][0] = 0
    malformed_identity = copy.deepcopy(encoded)
    malformed_identity["identity_key"].pop()
    wrong_identity_system = copy.deepcopy(encoded)
    wrong_identity_system["identity_key"][0] = 0
    wrong_identity_role = copy.deepcopy(encoded)
    wrong_identity_role["identity_key"][1] = 8
    invalid_identity_kid = copy.deepcopy(encoded)
    invalid_identity_kid["identity_key_kid"] = encoded["server_kid"] + 1
    regressed_server_kid = copy.deepcopy(encoded)
    regressed_server_kid["server_kid"] = 0
    short_registration_id = copy.deepcopy(encoded)
    short_registration_id["consumed_registrations"][0].pop()
    duplicate_registration_id = copy.deepcopy(encoded)
    duplicate_registration_id["consumed_registrations"].append(
        duplicate_registration_id["consumed_registrations"][0]
    )
    missing_registration_history = copy.deepcopy(encoded)
    del missing_registration_history["consumed_registrations"]
    incomplete_registration_history = copy.deepcopy(encoded)
    incomplete_registration_history["consumed_registrations"] = []
    identity_key = json.dumps(encoded["identity_key"], separators=(",", ":"))
    principal = json.dumps(encoded["known_ids"]["1"], separators=(",", ":"))
    consumed_registrations = json.dumps(
        encoded["consumed_registrations"], separators=(",", ":")
    )
    duplicate_kid = (
        f'{{"identity_key":{identity_key},"identity_key_kid":0,'
        f'"server_kid":1,"known_ids":'
        f'{{"1":{principal},"1":{principal}}},'
        f'"consumed_registrations":{consumed_registrations}}}'
    )

    for malformed in (
        json.dumps(wrong_key_type),
        json.dumps(short_key),
        json.dumps(malformed_ratchet),
        json.dumps(malformed_identity),
        json.dumps(wrong_identity_system),
        json.dumps(wrong_identity_role),
        json.dumps(invalid_identity_kid),
        json.dumps(regressed_server_kid),
        json.dumps(short_registration_id),
        json.dumps(duplicate_registration_id),
        json.dumps(missing_registration_history),
        json.dumps(incomplete_registration_history),
        duplicate_kid,
    ):
        with pytest.raises(ValueError, match="invalid server state"):
            BeaconCryptServer.from_state(malformed)
