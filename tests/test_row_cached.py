import gc
import weakref

import pytest

from beaconcrypt import (
    BeaconCryptCachedRowServer,
    BeaconCryptRowServer,
    RowPersistenceError,
)
from test_row_persistence import Database, register


class CachedDatabase(Database):
    def __init__(self, path):
        super().__init__(path)
        self.expectations = []
        self.expect_error = None

    def expect(self, key, expected):
        self.expectations.append(key)
        if self.expect_error is not None:
            raise self.expect_error
        row = self.connection.execute(
            "SELECT value FROM state WHERE key = ?", (key,)
        ).fetchone()
        return (None if row is None else row[0]) == expected


def cached(path, capacity=2):
    database = CachedDatabase(path)
    server = BeaconCryptCachedRowServer.create(
        19, b"s" * 32, b"m" * 32, database, b"l" * 32, capacity
    )
    return server, database


def test_warm_expectations_conflict_and_unknown_commit_reload(tmp_path):
    path = tmp_path / "cache.db"
    server, database = cached(path)
    assert isinstance(server, BeaconCryptRowServer)
    _, kid, _ = register(server)
    assert server.cached_peer_count() == 0
    database.loads.clear()
    assert server.encrypt_to_beacon_with_metadata(b"cold", kid).seq == 2
    assert len(database.loads) == 1 and not database.expectations
    database.loads.clear()
    assert server.encrypt_to_beacon_with_metadata(b"warm", kid).seq == 3
    assert not database.loads and len(database.expectations) == 1

    other_database = Database(path)
    other = BeaconCryptRowServer.open(other_database, b"l" * 32)
    other.encrypt_to_beacon(b"other worker", kid)
    with pytest.raises(RowPersistenceError) as failed:
        server.encrypt_to_beacon(b"stale", kid)
    assert failed.value.code == "conflict"
    assert server.cached_peer_count() == 0
    database.loads.clear()
    assert server.encrypt_to_beacon_with_metadata(b"fresh", kid).seq == 5
    assert len(database.loads) == 1
    database.fail_after_commit = True
    with pytest.raises(RowPersistenceError):
        server.encrypt_to_beacon(b"unknown", kid)
    database.fail_after_commit = False
    assert server.cached_peer_count() == 0
    database.loads.clear()
    assert server.encrypt_to_beacon_with_metadata(b"next", kid).seq == 7
    assert len(database.loads) == 1
    database.expect_error = OSError("expectation failed")
    with pytest.raises(RowPersistenceError) as failed:
        server.encrypt_to_beacon(b"storage failure", kid)
    assert failed.value.__cause__ is database.expect_error
    assert server.cached_peer_count() == 0


def test_cached_composition_and_expired_session(tmp_path):
    server, database = cached(tmp_path / "cache.db", 1)
    beacon, kid, _ = register(server)
    server.encrypt_to_beacon(b"warm", kid)
    message = beacon.encrypt_message_to_server(b"receive")
    sessions = []

    def operation(session):
        sessions.append(session)
        pending = session.decrypt_beacon_message(message)
        assert pending.changed
        assert (pending.message.key_id, pending.message.seq) == (kid, 1)
        session.store(b"result", pending.message.data)
        return pending.message.data

    database.loads.clear()
    assert server.transaction(operation) == b"receive"
    assert not database.loads and len(database.expectations) == 1
    with pytest.raises(RuntimeError, match="callback has ended"):
        sessions[0].load(b"result")
    assert server.cache_capacity() == 1
    server.clear_cache()
    assert server.cached_peer_count() == 0
    server.close()
    with pytest.raises(RuntimeError):
        server.cached_peer_count()


def test_zero_capacity_and_missing_expect_fallback(tmp_path):
    path = tmp_path / "cache.db"
    server, database = cached(path, 0)
    _, kid, _ = register(server)
    database.loads.clear()
    for _ in range(2):
        server.encrypt_to_beacon(b"uncached", kid)
    assert len(database.loads) == 2 and not database.expectations
    assert server.cached_peer_count() == 0
    fallback_database = Database(path)
    fallback = BeaconCryptCachedRowServer.open(fallback_database, b"l" * 32, 1)
    fallback_database.loads.clear()
    for _ in range(2):
        fallback.encrypt_to_beacon(b"fallback", kid)
    assert len(fallback_database.loads) == 2
    assert fallback.cached_peer_count() == 1


def test_cached_server_store_cycle_is_collected(tmp_path):
    server, database = cached(tmp_path / "cache.db")
    database.owner = server
    reference = weakref.ref(database)
    del server, database
    gc.collect()
    assert reference() is None
