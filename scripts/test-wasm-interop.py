#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Exercise public Go API interoperability between native and WASM executables.

Build testdata/interop twice, then supply --native and --wasm. Checkpoints here
are trusted test fixtures: their old owner is closed before restoring in the
other backend. Production storage still needs authoritative, durable CAS.
"""

import argparse
import base64
import json
import subprocess
from contextlib import ExitStack
from pathlib import Path


def encode(data):
    return base64.b64encode(data).decode("ascii")


class Fixture:
    def __init__(self, path):
        self.path = path
        self.process = subprocess.Popen(
            [str(path)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True
        )

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.process.stdin.close()
        try:
            status = self.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()
            raise RuntimeError(f"fixture did not stop: {self.path}")
        finally:
            self.process.stdout.close()
        if status and exc_type is None:
            raise RuntimeError(f"fixture exited with status {status}: {self.path}")

    def request(self, op, expected_error=None, **fields):
        command = {"op": op, **fields}
        self.process.stdin.write(json.dumps(command) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError(f"fixture stopped during {op}: {self.path}")
        result = json.loads(line)
        if expected_error is None:
            assert "error" not in result, (op, result)
        else:
            assert result.get("class") == expected_error, (op, result)
            assert "data" not in result, ("rejection leaked output", result)
        return result


class Endpoint:
    def __init__(self, fixture, handle, server=False):
        self.fixture = fixture
        self.handle = handle
        self.server = server

    def request(self, op, **fields):
        return self.fixture.request(op, handle=self.handle, **fields)

    def snapshot(self):
        if self.server:
            return self.request("snapshot")["data"]
        return None


def exchange(sender, receiver, plaintext, beacon_key):
    frame = sender.request("encrypt", kid=beacon_key, data=encode(plaintext))["data"]
    damaged = bytearray(base64.b64decode(frame))
    damaged[-1] ^= 1
    before = receiver.snapshot()
    receiver.request("decrypt", data=encode(damaged), expected_error="crypto")
    assert receiver.snapshot() == before, "tampering changed the server checkpoint"
    opened = receiver.request("decrypt", data=frame)
    assert opened.get("data") == encode(plaintext), "plaintext differs after tampering"
    before = receiver.snapshot()
    receiver.request("decrypt", data=frame, expected_error="crypto")
    assert receiver.snapshot() == before, "replay changed the server checkpoint"


def transfer(server, destination, identity, mldsa_identity):
    checkpoint = server.request("snapshot")["data"]
    previous = server.request("head")["head"]
    server.request("close")
    handle = destination.request("restore", data=checkpoint)["handle"]
    restored = Endpoint(destination, handle, server=True)
    current = restored.request("head")["head"]
    assert current["Lineage"] == previous["Lineage"], "restore changed lineage"
    assert (
        current["Generation"] == previous["Generation"] + 1
    ), "restore did not claim generation"
    assert restored.request("identity")["data"] == identity, "restore changed identity"
    assert (
        restored.request("mldsa-public-key")["data"] == mldsa_identity
    ), "restore changed ML-DSA identity"
    return restored


def check_pair(native_path, wasm_path, wasm_server):
    with ExitStack() as stack:
        native = stack.enter_context(Fixture(native_path))
        wasm = stack.enter_context(Fixture(wasm_path))
        server_fixture, beacon_fixture = (
            (wasm, native) if wasm_server else (native, wasm)
        )
        handle = server_fixture.request(
            "server-new",
            kid=19,
            seed=encode(bytes([9]) * 32),
            mldsa_seed=encode(bytes([10]) * 32),
        )["handle"]
        server = Endpoint(server_fixture, handle, server=True)
        identity = server.request("identity")["data"]
        mldsa_identity = server.request("mldsa-public-key")["data"]
        assert len(base64.b64decode(mldsa_identity)) == 1952
        handle = beacon_fixture.request(
            "beacon-new", kid=19, data=identity, extra=mldsa_identity
        )["handle"]
        beacon = Endpoint(beacon_fixture, handle)
        registration = beacon.request("registration")["data"]
        registered = server.request(
            "register", data=registration, extra=encode(b"initial message")
        )
        beacon_key = registered["kid"]
        assert beacon.request("finish", data=registered["data"])["data"] == encode(
            b"initial message"
        )

        def both_directions(label):
            exchange(beacon, server, label + b" beacon to server", beacon_key)
            exchange(server, beacon, label + b" server to beacon", beacon_key)

        # Cross the canonical CBOR sequence-width boundary as ratchets progress.
        for sequence in range(26):
            both_directions(f"before transfer {sequence}".encode("ascii"))

        server = transfer(server, beacon_fixture, identity, mldsa_identity)
        both_directions(b"after first backend transfer")
        server = transfer(server, server_fixture, identity, mldsa_identity)
        both_directions(b"after second backend transfer")
        server.request("close")
        beacon.request("close")
        print(
            f"PASS: {'WASM' if wasm_server else 'native'} server, mixed handshake/ratchets and both snapshot transfers"
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--wasm", type=Path, required=True)
    args = parser.parse_args()
    native = args.native.resolve(strict=True)
    wasm = args.wasm.resolve(strict=True)
    check_pair(native, wasm, wasm_server=False)
    check_pair(native, wasm, wasm_server=True)


if __name__ == "__main__":
    main()
