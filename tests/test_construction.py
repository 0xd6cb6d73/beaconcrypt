import pytest

from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer


@pytest.mark.parametrize("length", [0, 1, 31, 33, 64])
def test_constructors_reject_bad_key_lengths_without_panicking(length):
    with pytest.raises(ValueError):
        BeaconCryptBeacon(19, b"x" * length)
    with pytest.raises(ValueError):
        BeaconCryptServer(19, b"x" * length)
