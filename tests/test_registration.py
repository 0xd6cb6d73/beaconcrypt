from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer


def register_beacon(
    server: BeaconCryptServer,
    beacon: BeaconCryptBeacon,
) -> bytes | None:
    message = bytes([0xFF]) * 32
    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    reg_out = server.register_beacon(phase_1, message)
    assert reg_out is not None
    phase2 = beacon.process_initial_message(reg_out.serialized())
    assert phase2 is not None
    assert phase2 == message
    return phase2


def test_register():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)

    assert register_beacon(server, beacon) is not None


def test_register_without_initial_message():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)

    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    reg_out = server.register_beacon(phase_1, None)
    assert reg_out is not None
    assert reg_out.key_id() == 1

    phase_2 = beacon.process_initial_message(reg_out.serialized())
    assert phase_2 == b""


def test_server_from_seed_uses_stable_identity():
    seed = bytes([0]) * 32
    expected_pk = bytes.fromhex(
        "3b6a27bcceb6a42d62a3a8d02a6f0d73653215771de243a63ac048a18b59da29"
    )

    server_a = BeaconCryptServer(0, seed)
    server_b = BeaconCryptServer(0, seed)

    assert server_a.id_pk() == server_b.id_pk() == expected_pk


def test_malformed_registration_is_rejected():
    server = BeaconCryptServer(0, None)

    assert server.register_beacon(b"not a registration", b"initial") is None


def test_beacon_rejects_registration_response_from_wrong_server():
    expected_server = BeaconCryptServer(0, None)
    wrong_server = BeaconCryptServer(0, None)
    beacon = BeaconCryptBeacon(0, expected_server.id_pk())

    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    assert expected_server.register_beacon(phase_1, b"expected server") is not None
    wrong_response = wrong_server.register_beacon(phase_1, b"wrong server")
    assert wrong_response is not None

    assert beacon.process_initial_message(wrong_response.serialized()) is None
