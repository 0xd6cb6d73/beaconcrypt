import gc
import json
import threading
import weakref
from concurrent.futures import ThreadPoolExecutor

import pytest

from beaconcrypt import (
    BeaconCryptBeacon,
    BeaconCryptServer,
    PersistenceError,
    SnapshotHead,
    snapshot_head,
    validate_snapshot_successor,
)


class Store:
    """Test store with one atomic trusted head; production stores must add durability."""

    def __init__(self):
        self.snapshot = None
        self.current_head = None
        self.cas_calls = []
        self.load_calls = 0
        self.fail_cas = False
        self.callback = None
        self.lock = threading.Lock()

    def load(self):
        self.load_calls += 1
        with self.lock:
            return self.snapshot

    def compare_and_swap(self, expected, replacement):
        assert isinstance(replacement, bytes)
        if self.callback is not None:
            self.callback()
        with self.lock:
            self.cas_calls.append((expected, replacement))
            if self.fail_cas or expected != self.current_head:
                return False
            successor = validate_snapshot_successor(replacement, expected)
            self.snapshot = replacement
            self.current_head = successor
            return True


def create(store=None):
    if store is None:
        store = Store()
    server = BeaconCryptServer.create_with_store(
        19, b"s" * 32, b"m" * 32, store, b"l" * 32
    )
    return server, store


def register(server):
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    registration = beacon.generate_registration()
    response = server.register_beacon(registration, b"registered")
    assert response is not None
    assert beacon.process_initial_message(response.serialized()) == b"registered"
    return beacon, response.key_id()


def assert_error(code, operation):
    with pytest.raises(PersistenceError) as caught:
        operation()
    assert caught.value.code == code
    return caught.value


def test_creation_and_activation_commit_before_returning():
    server, store = create()
    assert store.cas_calls[0][0] is None
    assert store.current_head == server.head()
    assert server.head().generation == 0
    assert server.head().lineage == b"l" * 32
    assert server.export_state() == store.snapshot
    previous = server.head()
    restored = BeaconCryptServer.restore(store)
    assert store.cas_calls[-1][0] == previous
    assert restored.head().generation == 1
    assert restored.head() == store.current_head
    assert restored.id_pk() == server.id_pk()
    assert restored.mldsa_public_key() == server.mldsa_public_key()
    assert restored.export_state() == store.snapshot
    assert_error("stale_generation", server.export_state)


def test_snapshot_heads_are_immutable_value_objects_and_validate_successors():
    server, store = create()
    head = server.head()
    reconstructed = SnapshotHead(head.lineage, head.generation, head.digest)
    assert head == reconstructed == snapshot_head(store.snapshot)
    assert hash(head) == hash(reconstructed)
    assert isinstance(head.lineage, bytes)
    assert isinstance(head.digest, bytes)
    for field, value in [
        ("lineage", b"x" * 32),
        ("generation", 2),
        ("digest", b"x" * 32),
    ]:
        with pytest.raises(AttributeError):
            setattr(head, field, value)
    with pytest.raises(ValueError):
        SnapshotHead(b"short", 0, b"d" * 32)
    with pytest.raises(ValueError):
        SnapshotHead(b"l" * 32, 0, b"short")
    assert validate_snapshot_successor(store.snapshot) == head
    restored = BeaconCryptServer.restore(store)
    assert validate_snapshot_successor(store.snapshot, head) == restored.head()
    assert_error(
        "stale_generation", lambda: validate_snapshot_successor(store.snapshot)
    )
    assert_error("invalid_snapshot", lambda: snapshot_head(b"bad"))


@pytest.mark.parametrize(
    "method", ["encrypt_to_beacon", "encrypt_and_update", "encrypt_and_update_json"]
)
def test_all_send_apis_commit_before_exposing_output(method):
    server, store = create()
    beacon, kid = register(server)
    previous = server.head()
    calls = len(store.cas_calls)
    output = getattr(server, method)(b"task", kid)
    assert len(store.cas_calls) == calls + 1
    assert store.cas_calls[-1][0] == previous
    assert store.current_head == server.head()
    if method == "encrypt_to_beacon":
        ciphertext = output
    elif method == "encrypt_and_update":
        ciphertext = output.data()
    else:
        ciphertext = bytes(json.loads(output)["data"])
    assert beacon.decrypt_server_message(ciphertext) == b"task"
    restored = BeaconCryptServer.restore(store)
    reply = beacon.encrypt_message_to_server(b"reply")
    assert restored.decrypt_beacon_message(reply) == b"reply"


@pytest.mark.parametrize(
    "method",
    ["decrypt_beacon_message", "decrypt_and_update", "decrypt_and_update_json"],
)
def test_all_receive_apis_commit_before_exposing_output_and_reject_replay(method):
    server, store = create()
    beacon, _ = register(server)
    ciphertext = beacon.encrypt_message_to_server(b"reply")
    previous = server.head()
    calls = len(store.cas_calls)
    output = getattr(server, method)(ciphertext)
    assert len(store.cas_calls) == calls + 1
    assert store.cas_calls[-1][0] == previous
    assert store.current_head == server.head()
    if method == "decrypt_beacon_message":
        plaintext = output
    elif method == "decrypt_and_update":
        plaintext = output.data()
    else:
        plaintext = bytes(json.loads(output)["data"])
    assert plaintext == b"reply"
    restored = BeaconCryptServer.restore(store)
    calls = len(store.cas_calls)
    assert getattr(restored, method)(ciphertext) is None
    assert len(store.cas_calls) == calls


@pytest.mark.parametrize(
    "method",
    ["decrypt_beacon_message", "decrypt_and_update", "decrypt_and_update_json"],
)
def test_rejected_receive_never_loads_or_commits(method):
    server, store = create()
    beacon, _ = register(server)
    ciphertext = beacon.encrypt_message_to_server(b"r" * 32)
    corrupted = bytearray(ciphertext)
    corrupted[-1] ^= 1
    head, snapshot = server.head(), store.snapshot
    calls, loads = len(store.cas_calls), store.load_calls
    for frame in [b"bad", bytes(corrupted)]:
        assert getattr(server, method)(frame) is None
    assert len(store.cas_calls) == calls
    assert store.load_calls == loads
    assert server.head() == head
    assert store.snapshot == snapshot
    assert not server.is_poisoned()
    assert getattr(server, method)(ciphertext) is not None


@pytest.mark.parametrize(
    "method", ["encrypt_to_beacon", "encrypt_and_update", "encrypt_and_update_json"]
)
def test_failed_send_cas_suppresses_output_and_poisons(method):
    server, store = create()
    _, kid = register(server)
    committed = store.snapshot
    head = server.head()
    store.fail_cas = True
    assert_error("stale_generation", lambda: getattr(server, method)(b"task", kid))
    assert server.is_poisoned()
    assert server.head() == head
    assert store.snapshot == committed
    calls = len(store.cas_calls)
    assert_error("poisoned", lambda: server.encrypt_to_beacon(b"again", kid))
    assert len(store.cas_calls) == calls


@pytest.mark.parametrize(
    "method",
    ["decrypt_beacon_message", "decrypt_and_update", "decrypt_and_update_json"],
)
def test_failed_receive_cas_suppresses_plaintext_and_poisons(method):
    server, store = create()
    beacon, _ = register(server)
    ciphertext = beacon.encrypt_message_to_server(b"secret reply")
    committed = store.snapshot
    store.fail_cas = True
    assert_error("stale_generation", lambda: getattr(server, method)(ciphertext))
    assert server.is_poisoned()
    assert store.snapshot == committed
    store.fail_cas = False
    restored = BeaconCryptServer.restore(store)
    assert restored.decrypt_beacon_message(ciphertext) == b"secret reply"
    assert_error("poisoned", lambda: getattr(server, method)(ciphertext))


def test_stale_owner_cannot_commit_after_activation():
    first, store = create()
    beacon, kid = register(first)
    restored = BeaconCryptServer.restore(store)
    assert first.decrypt_beacon_message(b"bad") is None
    assert not first.is_poisoned()
    assert_error("stale_generation", lambda: first.encrypt_to_beacon(b"loser", kid))
    assert first.is_poisoned()
    ciphertext = restored.encrypt_to_beacon(b"winner", kid)
    assert beacon.decrypt_server_message(ciphertext) == b"winner"


def test_racing_restorers_activate_only_one_owner():
    _, store = create()
    snapshot = store.snapshot
    barrier = threading.Barrier(2)

    class RacingStore(Store):
        def load(self):
            barrier.wait(timeout=10)
            return snapshot

    racing = RacingStore()
    racing.snapshot = snapshot
    racing.current_head = snapshot_head(snapshot)

    def restore():
        try:
            return BeaconCryptServer.restore(racing)
        except PersistenceError as error:
            return error.code

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda _: restore(), range(2)))
    assert sum(isinstance(result, BeaconCryptServer) for result in results) == 1
    assert results.count("stale_generation") == 1


def test_missing_malformed_and_noncanonical_snapshots_raise_typed_errors():
    store = Store()
    assert_error("missing_snapshot", lambda: BeaconCryptServer.restore(store))
    store.snapshot = b"bad"
    assert_error("invalid_snapshot", lambda: BeaconCryptServer.restore(store))
    server, good = create()
    assert int.from_bytes(good.snapshot[16:18], "little") == 3
    for version in [1, 2]:
        corrupted = bytearray(good.snapshot)
        corrupted[16:18] = version.to_bytes(2, "little")
        store.snapshot = bytes(corrupted)
        assert_error("invalid_snapshot", lambda: BeaconCryptServer.restore(store))
    store.snapshot = good.snapshot + b"extra"
    assert_error("invalid_snapshot", lambda: BeaconCryptServer.restore(store))
    noncanonical = bytearray(good.snapshot + b" ")
    noncanonical[92:100] = (len(noncanonical) - 100).to_bytes(8, "little")
    store.snapshot = bytes(noncanonical)
    assert_error("non_canonical_snapshot", lambda: BeaconCryptServer.restore(store))
    exhausted = bytearray(good.snapshot)
    exhausted[52:60] = (2**64 - 1).to_bytes(8, "little")
    store.snapshot = bytes(exhausted)
    assert_error("generation_exhausted", lambda: BeaconCryptServer.restore(store))
    assert_error("invalid_snapshot", lambda: BeaconCryptServer.from_state(b"bad"))
    assert not server.is_poisoned()


@pytest.mark.parametrize("callback", ["load", "compare_and_swap"])
def test_callback_exceptions_are_chained_and_fail_closed(callback):
    class CallbackFailure(Exception):
        pass

    class FailingStore(Store):
        def load(self):
            if callback == "load":
                raise CallbackFailure("load failed")
            return super().load()

        def compare_and_swap(self, expected, replacement):
            if callback == "compare_and_swap":
                raise CallbackFailure("CAS failed")
            return super().compare_and_swap(expected, replacement)

    store = FailingStore()
    if callback == "load":
        error = assert_error(
            "missing_snapshot", lambda: BeaconCryptServer.restore(store)
        )
    else:
        error = assert_error("stale_generation", lambda: create(store))
    assert isinstance(error.__cause__, CallbackFailure)
    assert str(error.__cause__) in {"load failed", "CAS failed"}


def test_live_callback_exception_poisons_and_preserves_original_exception():
    server, store = create()
    beacon, kid = register(server)

    def raise_io():
        raise OSError("disk unavailable")

    store.callback = raise_io
    error = assert_error(
        "stale_generation", lambda: server.encrypt_to_beacon(b"task", kid)
    )
    assert isinstance(error.__cause__, OSError)
    assert str(error.__cause__) == "disk unavailable"
    assert server.is_poisoned()
    store.callback = None
    restored = BeaconCryptServer.restore(store)
    assert (
        beacon.decrypt_server_message(restored.encrypt_to_beacon(b"safe", kid))
        == b"safe"
    )


def test_wrong_callback_return_type_raises_persistence_error_with_type_error_cause():
    class WrongLoad(Store):
        def load(self):
            return "JSON is not a checkpoint"

    error = assert_error(
        "missing_snapshot", lambda: BeaconCryptServer.restore(WrongLoad())
    )
    assert isinstance(error.__cause__, TypeError)


def test_reentrant_callback_fails_safely_and_poisons():
    server, store = create()
    _, kid = register(server)
    store.callback = lambda: server.head()
    error = assert_error(
        "stale_generation", lambda: server.encrypt_to_beacon(b"task", kid)
    )
    assert isinstance(error.__cause__, RuntimeError)
    assert "borrow" in str(error.__cause__).lower()
    assert server.is_poisoned()
    store.callback = None


def test_server_retains_store_until_its_own_release():
    store = Store()
    weak_store = weakref.ref(store)
    server, _ = create(store)
    del store, _
    gc.collect()
    assert weak_store() is not None
    assert server.export_state() == weak_store().snapshot
    del server
    gc.collect()
    assert weak_store() is None


def test_failed_nonreceive_operation_still_commits_generation():
    server, store = create()
    head = server.head()
    assert server.encrypt_to_beacon(b"task", 2**64 - 1) is None
    assert server.head().generation == head.generation + 1
    assert server.head() == store.current_head


@pytest.mark.parametrize("failing_commit", [1, 2])
def test_registration_commit_failure_never_exposes_response(failing_commit):
    server, store = create()
    beacon = BeaconCryptBeacon(19, server.id_pk(), server.mldsa_public_key())
    registration = beacon.generate_registration()
    previous_calls = len(store.cas_calls)

    def fail_selected_commit():
        store.fail_cas = len(store.cas_calls) == previous_calls + failing_commit - 1

    store.callback = fail_selected_commit
    assert_error(
        "stale_generation", lambda: server.register_beacon(registration, b"registered")
    )
    assert server.is_poisoned()
    store.callback = None
    store.fail_cas = False
    restored = BeaconCryptServer.restore(store)
    response = restored.register_beacon(registration, b"registered")
    if failing_commit == 1:
        assert beacon.process_initial_message(response.serialized()) == b"registered"
    else:
        assert response is None


def test_live_load_exception_is_typed_without_poisoning_owner():
    server, store = create()

    def failed_load():
        raise OSError("read failed")

    store.load = failed_load
    error = assert_error("missing_snapshot", server.export_state)
    assert isinstance(error.__cause__, OSError)
    assert not server.is_poisoned()


def test_wrong_cas_return_type_fails_closed():
    class WrongCas(Store):
        def compare_and_swap(self, expected, replacement):
            return "yes"

    error = assert_error("stale_generation", lambda: create(WrongCas()))
    assert isinstance(error.__cause__, TypeError)


def test_store_server_reference_cycle_is_collected():
    server, store = create()
    weak_store = weakref.ref(store)
    store.server = server
    del store, server
    gc.collect()
    assert weak_store() is None
