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


def test_encrypt_to_multiple():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    b2 = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

    b1_initial = register_beacon(server, b1)
    b2_initial = register_beacon(server, b2)
    assert b2_initial == b1_initial

    b1_m1 = server.encrypt_to_beacon(message, 1)
    b2_m1 = server.encrypt_to_beacon(message, 2)
    assert b1_m1 is not None and b2_m1 is not None and b1_m1 != b2_m1


def test_encrypt_multiple():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

    _ = register_beacon(server, b1)

    b1_m1 = server.encrypt_to_beacon(message, 1)
    b1_m2 = server.encrypt_to_beacon(message, 1)
    assert b1_m1 is not None and b1_m2 is not None and b1_m1 != b1_m2


def test_decrypt_multiple():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

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
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

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
    message = bytes([0x1]) * 32

    _ = register_beacon(server, beacon)
    m1 = server.encrypt_to_beacon(message, 1)
    m2 = server.encrypt_to_beacon(message, 1)
    assert m1 != m2

    plain2 = beacon.decrypt_server_message(m2)
    plain1 = beacon.decrypt_server_message(m1)
    assert plain2 is not None and plain1 is not None
    assert plain2 == plain1 == message


def test_beacon_encrypts_to_server():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"beacon to server"

    _ = register_beacon(server, beacon)
    ciphertext = beacon.encrypt_message_to_server(message)
    assert ciphertext is not None

    plaintext = server.decrypt_beacon_message(ciphertext, 1)
    assert plaintext == message


def test_beacon_encrypts_to_server_signed():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"signed beacon to server"

    _ = register_beacon(server, beacon)
    signed = beacon.encrypt_to_server_signed(message)
    assert signed is not None

    plaintext = server.decrypt_beacon_message_signed(signed)
    assert plaintext == message


def test_signed_beacon_message_rejects_tampering():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"beacon to server"

    _ = register_beacon(server, beacon)
    signed = beacon.encrypt_to_server_signed(message)
    assert signed is not None
    tampered = bytearray(signed)
    tampered[-1] ^= 0x01

    assert server.decrypt_beacon_message_signed(bytes(tampered)) is None


def test_signed_server_message_rejects_tampering():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"server to beacon"

    _ = register_beacon(server, beacon)
    signed = server.encrypt_to_beacon_signed(message, 1)
    assert signed is not None
    tampered = bytearray(signed)
    tampered[-1] ^= 0x01

    assert beacon.decrypt_server_message_signed(bytes(tampered)) is None


def test_decrypt_rejects_wrong_direction():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)

    _ = register_beacon(server, beacon)
    server_to_beacon = server.encrypt_to_beacon(b"server to beacon", 1)
    assert server_to_beacon is not None
    assert server.decrypt_beacon_message(server_to_beacon, 1) is None

    beacon_to_server = beacon.encrypt_message_to_server(b"beacon to server")
    assert beacon_to_server is not None
    assert beacon.decrypt_server_message(beacon_to_server) is None


def test_beacon_cannot_decrypt_message_for_different_beacon():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    b2 = BeaconCryptBeacon(0, server_pk)
    message = b"for b1 only"

    _ = register_beacon(server, b1)
    _ = register_beacon(server, b2)
    ciphertext = server.encrypt_to_beacon(message, 1)
    assert ciphertext is not None

    assert b2.decrypt_server_message(ciphertext) is None


def test_ciphertext_cannot_be_replayed():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"one shot"

    _ = register_beacon(server, beacon)
    ciphertext = server.encrypt_to_beacon(message, 1)
    assert ciphertext is not None

    assert beacon.decrypt_server_message(ciphertext) == message
    assert beacon.decrypt_server_message(ciphertext) is None
