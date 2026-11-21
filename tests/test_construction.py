import pytest

from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer


@pytest.mark.parametrize("length", [0, 1, 31, 33, 64])
def test_constructors_reject_bad_ed25519_key_lengths_without_panicking(length):
    server = BeaconCryptServer(19, None, None)
    with pytest.raises(ValueError):
        BeaconCryptBeacon(19, b"x" * length, server.mldsa_public_key())
    with pytest.raises(ValueError):
        BeaconCryptServer(19, b"x" * length, b"m" * 32)


@pytest.mark.parametrize("length", [0, 1, 31, 33, 64])
def test_server_rejects_bad_mldsa_seed_lengths_without_panicking(length):
    with pytest.raises(ValueError):
        BeaconCryptServer(19, b"e" * 32, b"x" * length)


@pytest.mark.parametrize("length", [0, 1, 32, 1951, 1953])
def test_beacon_rejects_bad_mldsa_pin_lengths_without_panicking(length):
    server = BeaconCryptServer(19, None, None)
    with pytest.raises(ValueError):
        BeaconCryptBeacon(19, server.id_pk(), b"x" * length)


def test_constructors_require_explicit_mldsa_arguments():
    server = BeaconCryptServer(19, None, None)
    with pytest.raises(TypeError):
        BeaconCryptServer(19, None)
    with pytest.raises(TypeError):
        BeaconCryptBeacon(19, server.id_pk())
