import gc
import sqlite3
import weakref

import pytest

from beaconcrypt import (
    BeaconCryptBeacon,
    BeaconCryptRowServer,
    RowMessage,
    RowPersistenceError,
)


class Database:
    """Actual file-backed database using one outer serializable transaction per callback group."""

    def __init__(self, path):
        self.connection = sqlite3.connect(path, isolation_level=None)
        self.connection.execute("PRAGMA journal_mode=WAL")
        self.connection.execute("PRAGMA synchronous=FULL")
        self.connection.execute(
            "CREATE TABLE IF NOT EXISTS state (key BLOB PRIMARY KEY, value BLOB NOT NULL)"
        )
        self.loads = []
        self.writes = []
        self.fail_begin = False
        self.fail_commit = False
        self.fail_after_commit = False
        self.fail_load = False

    def begin(self):
        self.connection.execute("BEGIN IMMEDIATE")
        if self.fail_begin:
            raise OSError("begin failed after transaction start")

    def load(self, key):
        self.loads.append(key)
        if self.fail_load:
            raise OSError("load failed")
        row = self.connection.execute(
            "SELECT value FROM state WHERE key = ?", (key,)
        ).fetchone()
        return None if row is None else row[0]

    def store(self, key, value):
        self.writes.append(key)
        self.connection.execute(
            "INSERT INTO state VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
            (key, value),
        )

    def commit(self):
        if self.fail_commit:
            raise OSError("commit failed")
        self.connection.execute("COMMIT")
        if self.fail_after_commit:
            raise OSError("commit acknowledgement lost")

    def rollback(self):
        if self.connection.in_transaction:
            self.connection.execute("ROLLBACK")

    def rows(self):
        return dict(self.connection.execute("SELECT key, value FROM state"))


def create(path):
    database = Database(path)
    server = BeaconCryptRowServer.create(19, b"s" * 32, b"m" * 32, database, b"l" * 32)
    return server, database


def register(server):
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    request = beacon.generate_registration()
    response = server.register_beacon(request, b"registered")
    assert beacon.process_initial_message(response.serialized()) == b"registered"
    return beacon, response.key_id(), request


def test_database_restart_and_selected_peer_only(tmp_path):
    path = tmp_path / "state.db"
    server, database = create(path)
    first, first_id, _ = register(server)
    second, second_id, _ = register(server)
    before = database.rows()
    database.loads.clear()
    database.writes.clear()
    ciphertext = server.encrypt_to_beacon(b"hello", first_id)
    assert first.decrypt_server_message(ciphertext) == b"hello"
    after = database.rows()
    assert len([key for key in before if before[key] != after[key]]) == 1
    assert len(database.writes) == 1
    assert len(database.loads) <= 2
    identity = server.id_pk()
    server.close()
    database.connection.close()
    restarted_store = Database(path)
    restarted = BeaconCryptRowServer.open(restarted_store, b"l" * 32)
    assert restarted.id_pk() == identity
    assert restarted.lineage() == b"l" * 32
    assert (
        restarted.decrypt_beacon_message(first.encrypt_message_to_server(b"first"))
        == b"first"
    )
    assert (
        restarted.decrypt_beacon_message(second.encrypt_message_to_server(b"second"))
        == b"second"
    )
    assert (
        second.decrypt_server_message(restarted.encrypt_to_beacon(b"reply", second_id))
        == b"reply"
    )


def test_authentication_replay_and_commit_rollback(tmp_path):
    server, database = create(tmp_path / "state.db")
    beacon, _, request = register(server)
    message = beacon.encrypt_message_to_server(b"payload")
    original = database.rows()
    invalid = bytearray(message)
    invalid[-1] ^= 1
    assert server.decrypt_beacon_message(invalid) is None
    assert server.decrypt_beacon_message(b"malformed") is None
    assert database.rows() == original
    database.fail_commit = True
    with pytest.raises(RowPersistenceError) as failed:
        server.decrypt_beacon_message(message)
    assert failed.value.code == "storage"
    assert isinstance(failed.value.__cause__, OSError)
    assert database.rows() == original
    assert not database.connection.in_transaction
    database.fail_commit = False
    assert server.decrypt_beacon_message(message) == b"payload"
    assert server.decrypt_beacon_message(message) is None
    assert server.register_beacon(request) is None


def test_authenticated_metadata_and_cached_receive(tmp_path):
    server, database = create(tmp_path / "state.db")
    first, first_id, _ = register(server)
    second, second_id, _ = register(server)
    outbound = server.encrypt_to_beacon_with_metadata(b"outbound", first_id)
    assert isinstance(outbound, RowMessage)
    assert (outbound.key_id, outbound.seq) == (first_id, 2)
    assert first.decrypt_server_message(outbound.data) == b"outbound"
    with pytest.raises(AttributeError):
        outbound.key_id = second_id

    older = first.encrypt_message_to_server(b"older")
    newer = first.encrypt_message_to_server(b"newer")
    other = second.encrypt_message_to_server(b"other peer")
    for message, data, peer_id, seq in [
        (newer, b"newer", first_id, 2),
        (other, b"other peer", second_id, 1),
        (older, b"older", first_id, 1),
    ]:
        result = server.decrypt_beacon_message_with_metadata(message)
        assert (result.data, result.key_id, result.seq) == (data, peer_id, seq)
    assert server.decrypt_beacon_message_with_metadata(older) is None
    database.fail_commit = True
    with pytest.raises(RowPersistenceError):
        server.encrypt_to_beacon_with_metadata(b"uncommitted", first_id)


def test_unknown_commit_does_not_release_or_reuse_consumed_receive(tmp_path):
    server, database = create(tmp_path / "state.db")
    beacon, _, _ = register(server)
    message = beacon.encrypt_message_to_server(b"lost acknowledgement")
    database.fail_after_commit = True
    with pytest.raises(RowPersistenceError):
        server.decrypt_beacon_message(message)
    database.fail_after_commit = False
    assert server.decrypt_beacon_message(message) is None
    assert (
        server.decrypt_beacon_message(beacon.encrypt_message_to_server(b"next"))
        == b"next"
    )


def test_failed_response_keeps_registration_consumed(tmp_path):
    server, database = create(tmp_path / "state.db")
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    request = beacon.generate_registration()
    before = database.rows()
    assert server.register_beacon(request, b"") is None
    assert database.rows() != before
    assert server.register_beacon(request, b"retry") is None


def test_open_errors_load_errors_close_and_gc(tmp_path):
    path = tmp_path / "state.db"
    empty = Database(path)
    with pytest.raises(RowPersistenceError) as missing:
        BeaconCryptRowServer.open(empty, b"l" * 32)
    assert missing.value.code == "missing_identity"
    with pytest.raises(ValueError):
        BeaconCryptRowServer.open(empty, b"short")
    server, database = create(path)
    database.fail_load = True
    with pytest.raises(RowPersistenceError) as failed:
        BeaconCryptRowServer.open(database, b"l" * 32)
    assert isinstance(failed.value.__cause__, OSError)
    database.fail_load = False
    server.close()
    with pytest.raises(RuntimeError):
        server.encrypt_to_beacon(b"closed", 20)


def test_store_cycle_gc(tmp_path):
    server, database = create(tmp_path / "state.db")
    database.owner = server
    reference = weakref.ref(database)
    del server, database
    gc.collect()
    assert reference() is None


def test_failed_begin_rolls_back_and_preserves_cause(tmp_path):
    server, database = create(tmp_path / "state.db")
    beacon, kid, _ = register(server)
    before = database.rows()
    database.fail_begin = True
    with pytest.raises(RowPersistenceError) as failure:
        server.encrypt_to_beacon(b"failed begin", kid)
    assert "begin failed" in str(failure.value.__cause__)
    assert not database.connection.in_transaction
    assert database.rows() == before
    database.fail_begin = False
    assert (
        beacon.decrypt_server_message(server.encrypt_to_beacon(b"retry", kid))
        == b"retry"
    )
