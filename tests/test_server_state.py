import json

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
    send_snapshot = json.loads(send_update["state"])

    assert send_update["kid"] == beacon_kid
    assert send_update["seq"] == 2
    assert send_snapshot["send_key"][:2] == [6, 8]
    assert len(send_snapshot["send_key"][2]) == 32
    assert send_snapshot["recv_key"][:2] == [6, 9]
    assert beacon.decrypt_server_message(bytes(send_update["data"])) == outbound

    inbound = b"beacon to server JSON update"
    ciphertext = beacon.encrypt_message_to_server(inbound)
    assert ciphertext is not None
    serialized_recv = server.decrypt_and_update_json(ciphertext)
    assert serialized_recv is not None
    recv_update = json.loads(serialized_recv)
    recv_snapshot = json.loads(recv_update["state"])

    assert recv_update["kid"] == beacon_kid
    assert recv_update["seq"] == 1
    assert recv_snapshot["recv_key"][:2] == [6, 9]
    assert len(recv_snapshot["recv_key"][2]) == 32
    assert recv_snapshot["send_key"][:2] == [6, 8]
    assert bytes(recv_update["data"]) == inbound


def test_json_update_failures_return_none():
    server = BeaconCryptServer(0, None)

    assert server.encrypt_and_update_json(b"message", 2**64 - 1) is None
    assert server.decrypt_and_update_json(b"not a frame") is None


def test_full_server_checkpoint_exports_restores_and_continues():
    server = BeaconCryptServer(0, bytes([0x52]) * 32)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    beacon_kid = register_beacon(server, beacon)

    checkpoint = server.export_state()
    assert checkpoint.startswith(b"beaconcrypt-snap")
    del server

    restored = BeaconCryptServer.from_state(checkpoint)
    inbound = beacon.encrypt_message_to_server(b"after Python restore")
    assert restored.decrypt_beacon_message(inbound) == b"after Python restore"

    outbound = restored.encrypt_to_beacon(b"restored reply", beacon_kid)
    assert beacon.decrypt_server_message(outbound) == b"restored reply"
    assert restored.export_state() != checkpoint


def test_rejected_receive_leaves_binding_checkpoint_unchanged():
    server = BeaconCryptServer(0, bytes([0x53]) * 32)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    register_beacon(server, beacon)
    message = bytes([0x5A]) * 32
    authentic = beacon.encrypt_message_to_server(message)
    assert authentic is not None
    corrupted = bytearray(authentic)
    corrupted[-1] ^= 0x01
    checkpoint = server.export_state()

    assert server.decrypt_beacon_message(bytes(corrupted)) is None
    assert server.export_state() == checkpoint

    assert server.decrypt_beacon_message(authentic) == message
    assert server.export_state() != checkpoint
