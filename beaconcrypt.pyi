from collections.abc import Sequence
from typing import final

@final
class BeaconCryptBeacon:
    def __new__(cls, /, server_kid: int, server_id_pk: bytes) -> BeaconCryptBeacon:
        """Raise ValueError on a bad key length or reported initialization/key-generation failure."""

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
    def __new__(cls, /, kid: int, id_seed: bytes | None) -> BeaconCryptServer:
        """Raise ValueError on a bad seed length or reported initialization/key-generation failure."""

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
        Export the current plaintext checkpoint.

        Save it immediately after every accepted receive or other state-changing call and before using that call's output. A normal rejected receive leaves the checkpoint unchanged.
        """

    @staticmethod
    def from_state(state: Sequence[int]) -> BeaconCryptServer:
        """
        Restore trusted checkpoint bytes. The bytes do not authenticate themselves or prevent stale rollback. Restoration advances the generation, so export and save the returned server immediately before using it.
        """

    def id_pk(self, /) -> bytes: ...
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
