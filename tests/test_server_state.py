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
    assert send_update["key"][:2] == [6, 8]
    assert len(send_update["key"][2]) == 32
    assert beacon.decrypt_server_message(bytes(send_update["data"])) == outbound

    inbound = b"beacon to server JSON update"
    ciphertext = beacon.encrypt_message_to_server(inbound)
    assert ciphertext is not None
    serialized_recv = server.decrypt_and_update_json(ciphertext)
    assert serialized_recv is not None
    recv_update = json.loads(serialized_recv)

    assert recv_update["kid"] == beacon_kid
    assert recv_update["key"][:2] == [6, 9]
    assert len(recv_update["key"][2]) == 32
    assert bytes(recv_update["data"]) == inbound


def test_json_update_failures_return_none():
    server = BeaconCryptServer(0, None)

    assert server.encrypt_and_update_json(b"message", 2**64 - 1) is None
    assert server.decrypt_and_update_json(b"not a frame") is None


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
    assert str(beacon_kid) in json.loads(state)

    restored = BeaconCryptServer.from_state(0, seed, state)
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


def test_empty_state_restore_preserves_kid_floor():
    server = BeaconCryptServer(7, None)
    state = server.export_state()
    assert state is not None
    assert json.loads(state) == {}

    restored = BeaconCryptServer.from_state(7, None, state)
    beacon = BeaconCryptBeacon(7, restored.id_pk())

    assert register_beacon(restored, beacon) == 8


@pytest.mark.parametrize(
    ("seed", "state"),
    [
        (b"short", "{}"),
        (None, "not JSON"),
        (None, '{"1": {"pk": [], "ratchet": {}}}'),
    ],
)
def test_restore_rejects_invalid_seed_or_state(seed: bytes | None, state: str):
    with pytest.raises(ValueError, match="invalid server identity seed or state"):
        BeaconCryptServer.from_state(0, seed, state)
