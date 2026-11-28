import base64
import json

import pytest

from beaconcrypt import (
    BeaconCryptBeacon,
    BeaconCryptCachedRowServer,
    BeaconCryptRowServer,
    EncryptState,
    PersistenceError,
    RowPersistenceError,
    SendResult,
)
from test_persistence import create, register
from test_row_persistence import Database


def assert_rejected(result):
    assert isinstance(result, SendResult)
    assert result.outcome == "rejected"
    assert result.changed is False
    assert result.value is None
    assert result.key_id is None
    assert result.seq is None


@pytest.mark.parametrize(
    "method",
    [
        "encrypt_to_beacon_outcome",
        "encrypt_and_update_outcome",
        "encrypt_and_update_json_outcome",
    ],
)
def test_snapshot_send_results_are_explicit_and_release_only_committed_outputs(method):
    server, store = create()
    beacon, kid = register(server)
    send = getattr(server, method)
    head = server.head()
    assert_rejected(send(b"", kid))
    assert_rejected(send(b"unknown", 2**64 - 1))
    assert server.head() == head
    sent = send(b"payload", kid)
    assert isinstance(sent, SendResult)
    assert sent.outcome == "sent"
    assert sent.changed is True
    assert sent.key_id == kid
    assert sent.seq == 2
    value = sent.value
    if method == "encrypt_and_update_outcome":
        assert isinstance(value, EncryptState)
        assert value.key_id() == kid
        assert value.seq() == sent.seq
        assert "send_key" in json.loads(value.state())
        frame = value.data()
        assert sent.value.data() == frame
    elif method == "encrypt_and_update_json_outcome":
        assert isinstance(value, str)
        value = json.loads(value)
        assert value["kid"] == kid
        assert value["seq"] == sent.seq
        frame = base64.b64decode(value["data"], validate=True)
    else:
        assert isinstance(value, bytes)
        frame = value
    assert beacon.decrypt_server_message(frame) == b"payload"
    assert server.head().generation == head.generation + 1
    for name, replacement in [
        ("outcome", "rejected"),
        ("changed", False),
        ("value", None),
        ("key_id", 0),
        ("seq", 0),
    ]:
        with pytest.raises(AttributeError):
            setattr(sent, name, replacement)
    store.fail_cas = True
    with pytest.raises(PersistenceError) as failed:
        send(b"withheld", kid)
    assert failed.value.code == "stale_generation"
    assert server.is_poisoned()
    with pytest.raises(PersistenceError) as failed:
        send(b"again", kid)
    assert failed.value.code == "poisoned"


def test_beacon_send_result_preserves_metadata_and_rejections():
    server, _ = create()
    fresh = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    assert_rejected(fresh.encrypt_message_to_server_outcome(b"not registered"))
    beacon, kid = register(server)
    assert_rejected(beacon.encrypt_message_to_server_outcome(b""))
    result = beacon.encrypt_message_to_server_outcome(b"payload")
    assert result.outcome == "sent"
    assert result.changed is True
    assert (result.key_id, result.seq) == (19, 1)
    assert isinstance(result.value, bytes)
    assert server.decrypt_beacon_message(result.value) == b"payload"


def create_row(tmp_path, cached):
    database = Database(tmp_path / "outcomes.db")
    args = (19, b"s" * 32, b"m" * 32, database, b"l" * 32)
    if cached:
        return BeaconCryptCachedRowServer.create(*args, 2), database
    return BeaconCryptRowServer.create(*args), database


@pytest.mark.parametrize("cached", [False, True])
def test_row_send_results_publish_metadata_and_fence_storage_errors(tmp_path, cached):
    server, database = create_row(tmp_path, cached)
    beacon, kid = register(server)
    before = database.rows()
    assert_rejected(server.encrypt_to_beacon_outcome(b"", kid))
    assert_rejected(server.encrypt_to_beacon_outcome(b"unknown", 2**64 - 1))
    assert database.rows() == before
    sent = server.encrypt_to_beacon_outcome(b"payload", kid)
    assert sent.outcome == "sent"
    assert sent.changed is True
    assert (sent.key_id, sent.seq) == (kid, 2)
    assert beacon.decrypt_server_message(sent.value) == b"payload"
    before = database.rows()
    database.fail_commit = True
    with pytest.raises(RowPersistenceError) as failed:
        server.encrypt_to_beacon_outcome(b"withheld", kid)
    assert failed.value.code == "storage"
    assert database.rows() == before
    database.fail_commit = False
    sent = server.encrypt_to_beacon_outcome(b"retried", kid)
    assert sent.seq == 3
    assert beacon.decrypt_server_message(sent.value) == b"retried"
    server.close()


@pytest.mark.parametrize("kind", ["snapshot", "row", "cached"])
def test_optional_registration_empty_payload_consumes_acceptance_without_response(
    tmp_path, kind
):
    if kind == "snapshot":
        server, _ = create()
        checkpoint = server.export_state
    else:
        server, database = create_row(tmp_path, kind == "cached")
        checkpoint = database.rows
    absent = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    response = server.register_beacon(absent.generate_registration(), None)
    assert absent.process_initial_message(response.serialized()) == b"\xff"
    empty = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    request = empty.generate_registration()
    before = checkpoint()
    assert server.register_beacon(request, b"") is None
    after = checkpoint()
    assert after != before
    assert server.register_beacon(request, b"retry") is None
    assert checkpoint() == after
    if kind != "snapshot":
        server.close()
