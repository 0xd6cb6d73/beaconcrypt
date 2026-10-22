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
    assert reg_out.key_id() > 0
    phase2 = beacon.process_initial_message(reg_out.serialized())
    assert phase2 is not None
    assert phase2 == message
    return phase2


def test_register():
    server = BeaconCryptServer(0, None, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk, server.mldsa_public_key())

    assert register_beacon(server, beacon) is not None


def test_register_without_initial_message():
    server = BeaconCryptServer(0, None, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk, server.mldsa_public_key())

    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    reg_out = server.register_beacon(phase_1, None)
    assert reg_out is not None
    assert reg_out.key_id() == 1

    phase_2 = beacon.process_initial_message(reg_out.serialized())
    # `register_beacon` insert a single 0xFF byte if no initial message is provided to satisfy the upstream specification's requirement
    # this allows the beacon to check that keychain derivation is correct
    assert phase_2 == b"\xff"


def test_server_from_seed_uses_stable_identity():
    seed = bytes([0]) * 32
    expected_pk = bytes.fromhex(
        "3b6a27bcceb6a42d62a3a8d02a6f0d73653215771de243a63ac048a18b59da29"
    )

    mldsa_seed = bytes([1]) * 32
    server_a = BeaconCryptServer(0, seed, mldsa_seed)
    server_b = BeaconCryptServer(0, seed, mldsa_seed)

    assert server_a.id_pk() == server_b.id_pk() == expected_pk
    assert len(server_a.mldsa_public_key()) == 1952
    assert server_a.mldsa_public_key() == server_b.mldsa_public_key()
    different_mldsa = BeaconCryptServer(0, seed, bytes([2]) * 32)
    assert different_mldsa.id_pk() == expected_pk
    assert different_mldsa.mldsa_public_key() != server_a.mldsa_public_key()


def test_malformed_registration_is_rejected():
    server = BeaconCryptServer(0, None, None)

    assert server.register_beacon(b"not a registration", b"initial") is None


def test_wrong_mldsa_server_rejects_a_request_with_the_same_ed25519_identity():
    ed_seed = bytes([3]) * 32
    expected_server = BeaconCryptServer(0, ed_seed, bytes([4]) * 32)
    wrong_server = BeaconCryptServer(0, ed_seed, bytes([5]) * 32)
    beacon = BeaconCryptBeacon(
        0, expected_server.id_pk(), expected_server.mldsa_public_key()
    )

    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    correct_response = expected_server.register_beacon(phase_1, b"expected server")
    assert correct_response is not None
    wrong_response = wrong_server.register_beacon(phase_1, b"wrong server")
    assert wrong_response is None

    assert (
        beacon.process_initial_message(correct_response.serialized())
        == b"expected server"
    )
