from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer


def register_beacon(
    server: BeaconCryptServer,
    beacon: BeaconCryptBeacon,
) -> bytes | None:
    message = bytes(0xFF * 32)
    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    reg_out = server.register_beacon(phase_1, message)
    assert reg_out is not None
    phase2 = beacon.process_initial_message(reg_out.serialized())
    assert phase2 is not None
    assert phase2 == message
    return phase2


def test_encrypt_to_multiple():
    server = BeaconCryptServer(0, None)
    b1 = BeaconCryptBeacon(0, None)
    b2 = BeaconCryptBeacon(0, None)
    message = bytes(0x1 * 32)

    b1_initial = register_beacon(server, b1)
    b2_initial = register_beacon(server, b2)
    assert b2_initial == b1_initial

    b1_m1 = server.encrypt_to_beacon(message, 1)
    b2_m1 = server.encrypt_to_beacon(message, 2)
    assert b1_m1 is not None and b2_m1 is not None and b1_m1 != b2_m1


def test_encrypt_multiple():
    server = BeaconCryptServer(0, None)
    b1 = BeaconCryptBeacon(0, None)
    message = bytes(0x1 * 32)

    _ = register_beacon(server, b1)

    b1_m1 = server.encrypt_to_beacon(message, 1)
    b1_m2 = server.encrypt_to_beacon(message, 1)
    assert b1_m1 is not None and b1_m2 is not None and b1_m1 != b1_m2


def test_decrypt_multiple():
    server = BeaconCryptServer(0, None)
    beacon = BeaconCryptBeacon(0, None)
    message = bytes(0x1 * 32)

    _ = register_beacon(server, beacon)
    m1 = server.encrypt_to_beacon(message, 1)
    m2 = server.encrypt_to_beacon(message, 1)
    assert m1 != m2

    plain1 = beacon.decrypt_server_message(m1)
    plain2 = beacon.decrypt_server_message(m2)
    assert plain2 is not None and plain1 is not None
    assert plain2 == plain1 == message


def test_decrypt_multiple_signed():
    server = BeaconCryptServer(0, None)
    beacon = BeaconCryptBeacon(0, None)
    message = bytes(0x1 * 32)

    _ = register_beacon(server, beacon)
    m1 = server.encrypt_to_beacon_signed(message, 1)
    m2 = server.encrypt_to_beacon_signed(message, 1)
    assert m1 != m2

    plain1 = beacon.decrypt_server_message_signed(m1)
    plain2 = beacon.decrypt_server_message_signed(m2)
    assert plain2 is not None and plain1 is not None
    assert plain2 == plain1 == message


def test_decrypt_catch_up():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes(0x1 * 32)

    _ = register_beacon(server, beacon)
    m1 = server.encrypt_to_beacon(message, 1)
    m2 = server.encrypt_to_beacon(message, 1)
    assert m1 != m2

    plain2 = beacon.decrypt_server_message(m2)
    plain1 = beacon.decrypt_server_message(m1)
    assert plain2 is not None and plain1 is not None
    assert plain2 == plain1 == message
