# SPDX-License-Identifier: 0BSD
"""Release packaging tests use synthetic guest bytes, without Rust or network."""

import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "package_wasm", Path(__file__).with_name("package-wasm.py")
)
packager = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(packager)


def leb(value):
    result = bytearray()
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return bytes(result)


def name(value):
    encoded = value.encode()
    return leb(len(encoded)) + encoded


def guest(extra_import=None):
    # The packager inspects import/export descriptors; wazero verifies actual
    # guest code and function signatures in the Go suite.
    exports = leb(len(packager.REQUIRED_EXPORTS))
    for export in sorted(packager.REQUIRED_EXPORTS):
        exports += name(export) + bytes([2 if export == "memory" else 0]) + b"\0"
    module = b"\0asm\x01\0\0\0"
    if extra_import:
        imports = b"\x01" + name(extra_import[0]) + name(extra_import[1]) + b"\0\0"
        module += b"\x02" + leb(len(imports)) + imports
    return module + b"\x07" + leb(len(exports)) + exports


class PackagingTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name) / "repo"
        self.output = Path(self.temporary.name) / "release"
        for path, content in {
            "go.mod": f"module {packager.MODULE}\n\ngo 1.25.0\n".encode(),
            "go.sum": b"",
            "api.go": b"package beaconcrypt\n",
            "backend_wazero.go": b'package beaconcrypt\nimport _ "embed"\n//go:embed internal/wasm/beaconcrypt.wasm\nvar guest []byte\n',
            "beaconcrypt_go.c": b"/* C shim */\n",
            "beaconcrypt_go.h": b"/* C declarations */\n",
            "beaconcrypt/bindings.h": b"/* Rust declarations */\n",
            "LICENSE": b"0BSD fixture\n",
            "Cargo.toml": b"[workspace]\n",
            "Cargo.lock": b"# pinned fixture\n",
            "beaconcrypt-crypto/Cargo.toml": b'[package]\nname="beaconcrypt-crypto"\n',
            "beaconcrypt-crypto/src/lib.rs": b"#![no_std]\n",
            "scripts/wasm-toolchain.json": b'{"rust":"1.97.1","target":"wasm32-wasip1","wasm_abi_version":1}',
            "internal/wasm/beaconcrypt.wasm": guest(),
            "internal/wasm/runtime.go": b"package wasm\n",
            "testdata/fixture.json": b'{"fixture":true}',
            "target/do-not-ship": b"build output",
            ".tools/do-not-ship": b"tool cache",
        }.items():
            destination = self.repo / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(content)
        self.state = patch.object(
            packager, "git_state", return_value=("1" * 40, 1_700_000_000, False)
        )
        self.state.start()
        self.addCleanup(self.state.stop)
        self.record_build()

    def record_build(self):
        versions = {
            ("rustc", "--version"): "rustc 1.97.1 (fixture)",
            ("cargo", "--version"): "cargo 1.97.1 (fixture)",
        }
        original_command = packager.command
        with patch.object(
            packager,
            "command",
            side_effect=lambda repo, *args: (
                versions[args] if args in versions else original_command(repo, *args)
            ),
        ):
            return packager.record_build(self.repo)

    def test_rust_only_provenance_and_crypto_input_tracking(self):
        versions = {
            ("rustc", "--version"): "rustc 1.97.1 (fixture)",
            ("cargo", "--version"): "cargo 1.97.1 (fixture)",
        }
        with patch.object(
            packager, "command", side_effect=lambda repo, *args: versions[args]
        ) as invoked:
            info = packager.record_build(self.repo)
        self.assertEqual(
            [call.args[1:] for call in invoked.call_args_list], list(versions)
        )
        self.assertEqual(
            info["toolchain"],
            {
                "rustc": versions[("rustc", "--version")],
                "cargo": versions[("cargo", "--version")],
            },
        )
        source = Path("beaconcrypt-crypto/src/lib.rs")
        self.assertIn(str(source), info["build_inputs_sha256"])
        (self.repo / source).write_text("#![no_std]\npub const CHANGED: bool = true;\n")
        with self.assertRaisesRegex(ValueError, "inputs changed"):
            packager.package(self.repo, self.output, "v0.6.0")

    def test_legacy_toolchain_metadata_remains_packageable(self):
        info = json.loads((self.repo / packager.BUILD_INFO_PATH).read_text())
        info["toolchain"]["zig"] = "0.17.0"
        (self.repo / packager.BUILD_INFO_PATH).write_bytes(packager.json_bytes(info))
        archive = packager.package(self.repo, self.output, "v0.6.0")
        with tarfile.open(archive, "r:gz") as bundle:
            manifest = json.load(
                bundle.extractfile("beaconcrypt-go-v0.6.0/" + packager.MANIFEST_NAME)
            )
            self.assertEqual(manifest["toolchain"]["zig"], "0.17.0")

    def initialize_git(self):
        self.state.stop()
        ignore = Path(__file__).resolve().parent.parent / ".gitignore"
        (self.repo / ".gitignore").write_bytes(ignore.read_bytes())
        empty_ignore = Path(self.temporary.name) / "global-ignore"
        empty_ignore.write_text("")

        def git(*args):
            subprocess.run(
                ["git", *args],
                cwd=self.repo,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )

        git("init", "--quiet")
        git("config", "user.name", "Packaging test")
        git("config", "user.email", "packaging@example.invalid")
        git("config", "commit.gpgsign", "false")
        git("config", "core.excludesFile", str(empty_ignore))
        git("config", "core.hooksPath", str(Path(self.temporary.name) / "hooks"))
        git("add", ".")
        git(
            "commit",
            "--quiet",
            "-m",
            "Packaging fixture",
            "-m",
            "Co-authored-by: Codex <codex@openai.com>",
        )

    def test_complete_module_manifest_and_deterministic_archive(self):
        archive = packager.package(self.repo, self.output, "v0.6.0", require_clean=True)
        original = archive.read_bytes()
        packager.package(self.repo, self.output, "v0.6.0", require_clean=True)
        self.assertEqual(archive.read_bytes(), original)
        with tarfile.open(fileobj=io.BytesIO(original), mode="r:gz") as bundle:
            prefix = "beaconcrypt-go-v0.6.0/"
            names = bundle.getnames()
            for required in (
                "go.mod",
                "go.sum",
                "api.go",
                "backend_wazero.go",
                "beaconcrypt_go.c",
                "beaconcrypt_go.h",
                "beaconcrypt/bindings.h",
                "LICENSE",
                str(packager.WASM_PATH),
                "internal/wasm/runtime.go",
                "testdata/fixture.json",
            ):
                self.assertIn(prefix + required, names)
            self.assertFalse(
                any("target/" in entry or ".tools/" in entry for entry in names)
            )
            manifest = json.load(bundle.extractfile(prefix + packager.MANIFEST_NAME))
            self.assertEqual(manifest["wasm_abi_version"], 1)
            self.assertEqual(manifest["source_revision"], "1" * 40)
            for filename, expected in manifest["files_sha256"].items():
                actual = hashlib.sha256(
                    bundle.extractfile(prefix + filename).read()
                ).hexdigest()
                self.assertEqual(actual, expected)
        for line in (self.output / "SHA256SUMS").read_text().splitlines():
            expected, filename = line.split("  ")
            self.assertEqual(
                hashlib.sha256((self.output / filename).read_bytes()).hexdigest(),
                expected,
            )

    def test_modified_wasm_or_rust_inputs_require_rebuild(self):
        wasm = self.repo / packager.WASM_PATH
        wasm.write_bytes(wasm.read_bytes() + b"\0")
        with self.assertRaisesRegex(ValueError, "differs from recorded build"):
            packager.package(self.repo, self.output, "v0.6.0")
        wasm.write_bytes(guest())
        (self.repo / "Cargo.lock").write_text("# changed dependency lock\n")
        with self.assertRaisesRegex(ValueError, "inputs changed"):
            packager.package(self.repo, self.output, "v0.6.0")

    def test_module_rejects_unexpected_host_access_and_missing_exports(self):
        with self.assertRaisesRegex(ValueError, "unexpected Wasm import"):
            packager.inspect_wasm(guest(("wasi_snapshot_preview1", "path_open")))
        with self.assertRaisesRegex(ValueError, "missing Wasm exports"):
            packager.inspect_wasm(b"\0asm\x01\0\0\0")
        with self.assertRaisesRegex(ValueError, "core WebAssembly"):
            packager.inspect_wasm(b"not a module")

    def test_release_requires_clean_sources_and_safe_names(self):
        with patch.object(
            packager, "git_state", return_value=("1" * 40, 1_700_000_000, True)
        ):
            with self.assertRaisesRegex(ValueError, "clean source"):
                packager.package(self.repo, self.output, "v0.6.0", require_clean=True)
        with self.assertRaisesRegex(ValueError, "safe archive-name"):
            packager.package(self.repo, self.output, "../../escape")

    def test_legacy_tool_cache_keeps_real_release_checkout_clean(self):
        self.initialize_git()
        # Old checkouts may retain the former Zig compiler cache.
        cache = self.repo / ".zig-cache" / "h" / "compiler-cache"
        cache.parent.mkdir(parents=True)
        cache.write_bytes(b"generated by Zig")
        self.assertFalse(packager.git_state(self.repo)[2])
        self.assertFalse(self.record_build()["source_dirty"])
        archive = packager.package(self.repo, self.output, "v0.6.0", require_clean=True)
        with tarfile.open(archive, "r:gz") as bundle:
            self.assertFalse(any(".zig-cache/" in name for name in bundle.getnames()))
            manifest = json.load(
                bundle.extractfile("beaconcrypt-go-v0.6.0/" + packager.MANIFEST_NAME)
            )
            self.assertFalse(manifest["source_dirty"])

        for filename in ("api.go", "unexpected-source.go"):
            with self.subTest(filename=filename):
                source = self.repo / filename
                original = source.read_bytes() if source.exists() else None
                source.write_bytes(b"package beaconcrypt // changed source\n")
                self.assertTrue(packager.git_state(self.repo)[2])
                with self.assertRaisesRegex(ValueError, "clean source"):
                    packager.package(
                        self.repo, self.output, "v0.6.0", require_clean=True
                    )
                if original is None:
                    source.unlink()
                else:
                    source.write_bytes(original)

    def test_dirty_build_cannot_be_released_after_checkout_is_restored(self):
        self.initialize_git()
        source = self.repo / "api.go"
        original = source.read_bytes()
        source.write_bytes(b"package beaconcrypt // dirty at build time\n")
        self.assertTrue(self.record_build()["source_dirty"])
        source.write_bytes(original)
        self.assertFalse(packager.git_state(self.repo)[2])
        with self.assertRaisesRegex(ValueError, "clean source"):
            packager.package(self.repo, self.output, "v0.6.0", require_clean=True)


if __name__ == "__main__":
    unittest.main()
