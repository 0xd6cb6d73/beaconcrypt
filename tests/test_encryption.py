from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer


def register_beacon(
    server: BeaconCryptServer,
    beacon: BeaconCryptBeacon,
) -> int:
    message = bytes([0xFF]) * 32
    phase_1 = beacon.generate_registration()
    assert phase_1 is not None
    reg_out = server.register_beacon(phase_1, message)
    assert reg_out is not None
    phase2 = beacon.process_initial_message(reg_out.serialized())
    assert phase2 is not None
    assert phase2 == message
    return reg_out.key_id()


def corrupt_aead_ciphertext(ciphertext: bytes) -> bytes:
    corrupted = bytearray(ciphertext)
    corrupted[-1] ^= 0x01
    return bytes(corrupted)


def test_encrypt_to_multiple():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    b2 = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

    b1_kid = register_beacon(server, b1)
    b2_kid = register_beacon(server, b2)

    b1_m1 = server.encrypt_to_beacon(message, b1_kid)
    b2_m1 = server.encrypt_to_beacon(message, b2_kid)
    assert b1_m1 is not None and b2_m1 is not None and b1_m1 != b2_m1


def test_server_uses_per_beacon_associated_data():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    b2 = BeaconCryptBeacon(0, server_pk)

    b1_kid = register_beacon(server, b1)
    b2_kid = register_beacon(server, b2)

    to_b1 = server.encrypt_to_beacon(b"server to b1", b1_kid)
    to_b2 = server.encrypt_to_beacon(b"server to b2", b2_kid)
    assert b1.decrypt_server_message(to_b1) == b"server to b1"
    assert b2.decrypt_server_message(to_b2) == b"server to b2"

    from_b1 = b1.encrypt_message_to_server(b"b1 to server")
    from_b2 = b2.encrypt_message_to_server(b"b2 to server")
    assert server.decrypt_beacon_message(from_b1) == b"b1 to server"
    assert server.decrypt_beacon_message(from_b2) == b"b2 to server"


def test_server_can_encrypt_to_beacon_a_after_registering_beacon_b():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon_a = BeaconCryptBeacon(0, server_pk)
    beacon_b = BeaconCryptBeacon(0, server_pk)

    beacon_a_kid = register_beacon(server, beacon_a)
    register_beacon(server, beacon_b)

    message = b"server to beacon A after registering beacon B"
    ciphertext = server.encrypt_to_beacon(message, beacon_a_kid)
    assert beacon_a.decrypt_server_message(ciphertext) == message


def test_server_can_decrypt_from_beacon_a_after_registering_beacon_b():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon_a = BeaconCryptBeacon(0, server_pk)
    beacon_b = BeaconCryptBeacon(0, server_pk)

    beacon_a_kid = register_beacon(server, beacon_a)
    register_beacon(server, beacon_b)

    message = b"beacon A to server after registering beacon B"
    ciphertext = beacon_a.encrypt_message_to_server(message)
    assert server.decrypt_beacon_message(ciphertext) == message


def test_server_can_decrypt_from_beacon_a_after_encrypting_to_beacon_b():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon_a = BeaconCryptBeacon(0, server_pk)
    beacon_b = BeaconCryptBeacon(0, server_pk)

    beacon_a_kid = register_beacon(server, beacon_a)
    beacon_b_kid = register_beacon(server, beacon_b)

    to_beacon_b = server.encrypt_to_beacon(b"server to beacon B", beacon_b_kid)
    assert beacon_b.decrypt_server_message(to_beacon_b) == b"server to beacon B"

    from_beacon_a = beacon_a.encrypt_message_to_server(b"beacon A to server")
    assert (
        server.decrypt_beacon_message(from_beacon_a)
        == b"beacon A to server"
    )


def test_encrypt_multiple():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

    b1_kid = register_beacon(server, b1)

    b1_m1 = server.encrypt_to_beacon(message, b1_kid)
    b1_m2 = server.encrypt_to_beacon(message, b1_kid)
    assert b1_m1 is not None and b1_m2 is not None and b1_m1 != b1_m2


def test_decrypt_multiple():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

    beacon_kid = register_beacon(server, beacon)
    m1 = server.encrypt_to_beacon(message, beacon_kid)
    m2 = server.encrypt_to_beacon(message, beacon_kid)
    assert m1 != m2

    plain1 = beacon.decrypt_server_message(m1)
    plain2 = beacon.decrypt_server_message(m2)
    assert plain2 is not None and plain1 is not None
    assert plain2 == plain1 == message


def test_decrypt_catch_up():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x1]) * 32

    beacon_kid = register_beacon(server, beacon)
    m1 = server.encrypt_to_beacon(message, beacon_kid)
    m2 = server.encrypt_to_beacon(message, beacon_kid)
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

    beacon_kid = register_beacon(server, beacon)
    ciphertext = beacon.encrypt_message_to_server(message)
    assert ciphertext is not None

    plaintext = server.decrypt_beacon_message(ciphertext)
    assert plaintext == message


def test_server_encrypt_and_update_returns_ratchet_state():
    server = BeaconCryptServer(0, None)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    message = b"server to beacon with updated state"

    beacon_kid = register_beacon(server, beacon)
    update = server.encrypt_and_update(message, beacon_kid)

    assert update is not None
    assert update.key_id() == beacon_kid
    assert len(update.key()) == 32
    assert beacon.decrypt_server_message(update.data()) == message


def test_server_decrypt_and_update_returns_ratchet_state():
    server = BeaconCryptServer(0, None)
    beacon = BeaconCryptBeacon(0, server.id_pk())
    message = b"beacon to server with updated state"

    beacon_kid = register_beacon(server, beacon)
    ciphertext = beacon.encrypt_message_to_server(message)
    update = server.decrypt_and_update(ciphertext)

    assert update is not None
    assert update.key_id() == beacon_kid
    assert len(update.key()) == 32
    assert update.data() == message


def test_authenticated_beacon_message_rejects_tampering():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"beacon to server"

    beacon_kid = register_beacon(server, beacon)
    ciphertext = beacon.encrypt_message_to_server(message)
    assert ciphertext is not None
    tampered = bytearray(ciphertext)
    tampered[-1] ^= 0x01

    assert server.decrypt_beacon_message(bytes(tampered)) is None


def test_authenticated_server_message_rejects_tampering():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"server to beacon"

    beacon_kid = register_beacon(server, beacon)
    ciphertext = server.encrypt_to_beacon(message, beacon_kid)
    assert ciphertext is not None
    tampered = bytearray(ciphertext)
    tampered[-1] ^= 0x01

    assert beacon.decrypt_server_message(bytes(tampered)) is None


def test_decrypt_rejects_wrong_direction():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)

    beacon_kid = register_beacon(server, beacon)
    server_to_beacon = server.encrypt_to_beacon(b"server to beacon", beacon_kid)
    assert server_to_beacon is not None
    assert server.decrypt_beacon_message(server_to_beacon) is None

    beacon_to_server = beacon.encrypt_message_to_server(b"beacon to server")
    assert beacon_to_server is not None
    assert beacon.decrypt_server_message(beacon_to_server) is None


def test_beacon_cannot_decrypt_message_for_different_beacon():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    b1 = BeaconCryptBeacon(0, server_pk)
    b2 = BeaconCryptBeacon(0, server_pk)
    message = b"for b1 only"

    b1_kid = register_beacon(server, b1)
    register_beacon(server, b2)
    ciphertext = server.encrypt_to_beacon(message, b1_kid)
    assert ciphertext is not None

    assert b2.decrypt_server_message(ciphertext) is None


def test_ciphertext_cannot_be_replayed():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = b"one shot"

    beacon_kid = register_beacon(server, beacon)
    ciphertext = server.encrypt_to_beacon(message, beacon_kid)
    assert ciphertext is not None

    assert beacon.decrypt_server_message(ciphertext) == message
    assert beacon.decrypt_server_message(ciphertext) is None


def test_beacon_can_retry_decryption_after_corrupted_aead_message():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x01]) * 32

    beacon_kid = register_beacon(server, beacon)
    ciphertext = server.encrypt_to_beacon(message, beacon_kid)
    corrupted = corrupt_aead_ciphertext(ciphertext)

    assert beacon.decrypt_server_message(corrupted) is None
    assert beacon.decrypt_server_message(ciphertext) == message


def test_server_can_retry_decryption_after_corrupted_aead_message():
    server = BeaconCryptServer(0, None)
    server_pk = server.id_pk()
    beacon = BeaconCryptBeacon(0, server_pk)
    message = bytes([0x01]) * 32

    beacon_kid = register_beacon(server, beacon)
    ciphertext = beacon.encrypt_message_to_server(message)
    corrupted = corrupt_aead_ciphertext(ciphertext)

    assert server.decrypt_beacon_message(corrupted) is None
    assert server.decrypt_beacon_message(ciphertext) == message
