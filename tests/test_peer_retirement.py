import pytest

from beaconcrypt import BeaconCryptBeacon, BeaconCryptServer, PersistenceError
from test_row_persistence import create, register as register_row


def register(server, beacon, message=None):
    response = server.register_beacon(beacon.generate_registration(), message)
    assert response is not None
    beacon.process_initial_message(response.serialized())
    return response.key_id()


def new_beacon(server):
    return BeaconCryptBeacon(0, server.id_pk(), server.mldsa_public_key())


def test_retired_peer_is_refused_and_limit_refuses_without_consuming():
    server = BeaconCryptServer(0, None, None)
    retired_beacon = new_beacon(server)
    retired = register(server, retired_beacon)
    kept_beacon = new_beacon(server)
    kept = register(server, kept_beacon)
    inbound = retired_beacon.encrypt_message_to_server(b"after retirement")

    assert server.retire_peer(retired) is True
    assert server.retire_peer(retired) is False
    assert (server.peer_count(), server.registration_marker_count()) == (1, 2)
    assert server.decrypt_beacon_message(inbound) is None
    assert server.encrypt_to_beacon(b"tasking", retired) is None
    frame = server.encrypt_to_beacon(b"kept", kept)
    assert kept_beacon.decrypt_server_message(frame) == b"kept"

    server.set_max_peers(1)
    waiting = new_beacon(server)
    bundle = waiting.generate_registration()
    with pytest.raises(PersistenceError) as refused:
        server.register_beacon(bundle, None)
    assert refused.value.code == "capacity_exceeded"
    assert not server.is_poisoned()
    server.set_max_peers(None)
    response = server.register_beacon(bundle, b"late")
    assert waiting.process_initial_message(response.serialized()) == b"late"
    assert response.key_id() > kept
    assert server.registration_marker_count() == 3


def test_row_server_and_session_retire_peers(tmp_path):
    server, _ = create(tmp_path / "state.db")
    beacon, kid, request = register_row(server)
    _, other, _ = register_row(server)
    inbound = beacon.encrypt_message_to_server(b"after retirement")

    assert server.retire_peer(kid) is True
    assert server.retire_peer(kid) is False
    assert server.decrypt_beacon_message(inbound) is None
    assert server.encrypt_to_beacon(b"tasking", kid) is None
    assert server.register_beacon(request, None) is None

    def operation(session):
        session.store(b"audit", b"retired")
        assert session.retire_peer(other) is True
        return b"done"

    assert server.transaction(operation) == b"done"
    assert server.encrypt_to_beacon(b"tasking", other) is None
    server.close()
