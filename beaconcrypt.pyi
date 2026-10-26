from collections.abc import Sequence
from typing import Final, Literal, Protocol, final

MAX_MESSAGE_SIZE: Final[int]
"""Maximum complete encoded transport message in bytes; snapshots and JSON state are uncapped."""

class PersistenceError(ValueError):
    """Persistence failure; callback exceptions are preserved as __cause__."""

    code: Literal[
        "missing_snapshot",
        "invalid_snapshot",
        "non_canonical_snapshot",
        "stale_generation",
        "generation_exhausted",
        "encoding",
        "output_encoding",
        "initialization",
        "digest",
        "poisoned",
    ]

@final
class SnapshotHead:
    def __new__(
        cls, lineage: bytes, generation: int, digest: bytes
    ) -> SnapshotHead: ...
    @property
    def lineage(self) -> bytes: ...
    @property
    def generation(self) -> int: ...
    @property
    def digest(self) -> bytes: ...
    def __hash__(self) -> int: ...
    def __eq__(self, other: object) -> bool: ...

class _SnapshotStore(Protocol):
    """Trusted durable, linearizable, rollback-resistant storage; callbacks cannot reenter the same server."""

    def load(self) -> bytes | None: ...
    def compare_and_swap(
        self, expected: SnapshotHead | None, replacement: bytes
    ) -> bool: ...

def snapshot_head(data: Sequence[int]) -> SnapshotHead:
    """Parse an envelope head without authenticating its provenance."""

def validate_snapshot_successor(
    data: Sequence[int], expected: SnapshotHead | None = None
) -> SnapshotHead:
    """Validate envelope succession inside the store's atomic comparison transaction."""

@final
class BeaconCryptBeacon:
    def __new__(
        cls, /, server_kid: int, server_id_pk: bytes, server_mldsa_pk: bytes
    ) -> BeaconCryptBeacon:
        """Raise ValueError on a bad key length or reported initialization/key-generation failure."""

    def mldsa_public_key(self, /) -> bytes: ...
    def decrypt_server_message(self, /, data: Sequence[int]) -> bytes | None: ...
    def encrypt_message_to_server(self, /, data: Sequence[int]) -> bytes | None: ...
    def generate_registration(self, /) -> bytes | None:
        """
        Begin the beacon registration process. The output buffer should be sent as-is over the network.
        """

    def process_initial_message(self, /, data: Sequence[int]) -> bytes | None:
        """
        Process the registration response and optional initial data. The raw buffer sent by the server must be passed as-is as `data`.
        The response contains the contents of the initial message, or `0xFF` if there was none. Once this function returns, the beacon is registered
        """

@final
class BeaconCryptServer:
    """Protocol rejection returns None; persistence failures raise PersistenceError and failed commits poison the owner."""

    def __new__(
        cls, /, kid: int, id_seed: bytes | None, mldsa_seed: bytes | None
    ) -> BeaconCryptServer:
        """Create an in-memory checkpoint owner; persistence failures raise PersistenceError."""

    @staticmethod
    def create_with_store(
        kid: int,
        id_seed: bytes | None,
        mldsa_seed: bytes | None,
        store: _SnapshotStore,
        lineage: bytes | None = None,
    ) -> BeaconCryptServer:
        """Create and durably commit generation zero before returning; store callbacks cannot reenter this server."""

    @staticmethod
    def restore(store: _SnapshotStore) -> BeaconCryptServer:
        """Validate and activate the current trusted snapshot by compare-and-swap before returning."""

    def head(self) -> SnapshotHead: ...
    def is_poisoned(self) -> bool: ...
    def decrypt_and_update(self, /, data: Sequence[int]) -> EncryptState | None: ...
    def decrypt_and_update_json(self, /, data: Sequence[int]) -> str | None: ...
    def decrypt_beacon_message(self, /, data: Sequence[int]) -> bytes | None: ...
    def encrypt_and_update(
        self, /, data: Sequence[int], kid: int
    ) -> EncryptState | None: ...
    def encrypt_and_update_json(
        self, /, data: Sequence[int], kid: int
    ) -> str | None: ...
    def encrypt_to_beacon(self, /, data: Sequence[int], kid: int) -> bytes | None: ...
    def export_state(self, /) -> bytes:
        """
        Read this owner's committed plaintext checkpoint from its trusted store.

        With the default in-memory store, save after every potentially mutating call, including failures, and before using its output. Rejected receives leave the checkpoint unchanged. Persistence failures raise PersistenceError rather than returning None.
        """

    @staticmethod
    def from_state(state: Sequence[int]) -> BeaconCryptServer:
        """
        Restore trusted checkpoint bytes. The bytes do not authenticate themselves or prevent stale rollback. Restoration advances the generation, so export and save the returned server immediately before using it.
        """

    def id_pk(self, /) -> bytes: ...
    def mldsa_public_key(self, /) -> bytes: ...
    def register_beacon(
        self, /, reg_buffer: bytes, initial_message: bytes | None
    ) -> RegResponse | None: ...

@final
class EncryptState:
    def data(self, /) -> bytes: ...
    def key_id(self, /) -> int: ...
    def seq(self, /) -> int: ...
    def state(self, /) -> str:
        """
        Return inert plaintext ratchet JSON for observation only.

        It is secret-bearing, unauthenticated, and not restorable.
        """

@final
class RegResponse:
    def key_id(self, /) -> int: ...
    def serialized(self, /) -> bytes: ...
