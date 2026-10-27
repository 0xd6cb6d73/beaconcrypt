#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Package a verified, generated Wasm module with the unchanged Go import path."""

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile

MODULE = "github.com/0xd6cb6d73/beaconcrypt"
WASM_PATH = Path("internal/wasm/beaconcrypt.wasm")
BUILD_INFO_PATH = Path("internal/wasm/beaconcrypt.build.json")
MANIFEST_NAME = "beaconcrypt-wasm-manifest.json"
REQUIRED_EXPORTS = {
    "memory",
    "bc_abi_version",
    "bc_max_message_size",
    "bc_alloc",
    "bc_free",
    "bc_call",
}
ALLOWED_EXPORTS = REQUIRED_EXPORTS | {"_initialize", "__heap_base", "__data_end"}
ALLOWED_IMPORTS = {
    "beaconcrypt_host": {"snapshot_load", "snapshot_cas", "snapshot_destroy"},
    "wasi_snapshot_preview1": {
        "random_get",
        "environ_get",
        "environ_sizes_get",
        "fd_write",
        "proc_exit",
    },
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def command(repo, *args):
    return subprocess.check_output(args, cwd=repo, text=True).strip()


def git_state(repo):
    try:
        revision = command(repo, "git", "rev-parse", "HEAD")
        timestamp = int(command(repo, "git", "show", "-s", "--format=%ct", "HEAD"))
        dirty = bool(command(repo, "git", "status", "--porcelain"))
    except (subprocess.CalledProcessError, FileNotFoundError):
        raise ValueError("build provenance requires a Git checkout") from None
    return revision, timestamp, dirty


def build_inputs(repo):
    """Inputs maintained here; dependency source checksums come from Cargo.lock."""
    paths = [
        Path("Cargo.toml"),
        Path("Cargo.lock"),
        Path(".cargo/config.toml"),
        Path("scripts/wasm-toolchain.json"),
        Path("scripts/build-wasm.sh"),
        Path("scripts/package-wasm.py"),
    ]
    for crate in (
        "beaconcrypt",
        "beaconcrypt-core",
        "beaconcrypt-crypto",
        "beaconcrypt-parse",
        "beaconcrypt-wasm",
    ):
        paths.append(Path(crate) / "Cargo.toml")
        paths.append(Path(crate) / "build.rs")
        source = repo / crate / "src"
        if source.exists():
            paths.extend(
                path.relative_to(repo) for path in source.rglob("*") if path.is_file()
            )
    return {
        str(path): digest((repo / path).read_bytes())
        for path in sorted(set(paths))
        if (repo / path).is_file()
    }


def inspect_wasm(data):
    """Reject an accidental component, JS target, or newly introduced host access."""
    if data[:8] != b"\0asm\x01\0\0\0":
        raise ValueError("expected a core WebAssembly version 1 module")
    position = 8

    def byte():
        nonlocal position
        if position >= len(data):
            raise ValueError("truncated Wasm module")
        result = data[position]
        position += 1
        return result

    def leb():
        value = 0
        for shift in range(0, 35, 7):
            part = byte()
            value |= (part & 127) << shift
            if not part & 128:
                return value
        raise ValueError("invalid Wasm u32 encoding")

    def name():
        nonlocal position
        length = leb()
        end = position + length
        if end > len(data):
            raise ValueError("truncated Wasm name")
        result = data[position:end].decode("utf-8")
        position = end
        return result

    imports, exports = [], []
    while position < len(data):
        section = byte()
        size = leb()
        end = position + size
        if end > len(data):
            raise ValueError("truncated Wasm section")
        if section == 2:
            for _ in range(leb()):
                namespace, function = name(), name()
                if byte() != 0:
                    raise ValueError(
                        "Wasm must not import memory, tables, globals or tags"
                    )
                leb()  # Function type index; wazero validates signatures at load time.
                if function not in ALLOWED_IMPORTS.get(namespace, set()):
                    raise ValueError(f"unexpected Wasm import: {namespace}.{function}")
                imports.append(f"{namespace}.{function}")
        elif section == 7:
            for _ in range(leb()):
                export = name()
                kind, _index = byte(), leb()
                if export not in ALLOWED_EXPORTS:
                    raise ValueError(f"unexpected Wasm export: {export}")
                if export == "memory" and kind != 2:
                    raise ValueError("Wasm memory export has the wrong kind")
                if export.startswith("bc_") and kind != 0:
                    raise ValueError(
                        f"Wasm function export has the wrong kind: {export}"
                    )
                exports.append(export)
        if position > end:
            raise ValueError("invalid Wasm section size")
        position = end
    missing = REQUIRED_EXPORTS - set(exports)
    if missing:
        raise ValueError(f"missing Wasm exports: {', '.join(sorted(missing))}")
    return {"imports": sorted(imports), "exports": sorted(exports)}


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def record_build(repo):
    pins = json.loads((repo / "scripts/wasm-toolchain.json").read_text())
    rustc, cargo = (
        command(repo, *args)
        for args in [("rustc", "--version"), ("cargo", "--version")]
    )
    if rustc.split()[1] != pins["rust"] or cargo.split()[1] != pins["rust"]:
        raise ValueError("installed Rust versions do not match wasm-toolchain.json")
    revision, timestamp, dirty = git_state(repo)
    wasm = (repo / WASM_PATH).read_bytes()
    module_info = inspect_wasm(wasm)
    info = {
        "schema_version": 1,
        "wasm_abi_version": pins["wasm_abi_version"],
        "source_revision": revision,
        "source_dirty": dirty,
        "source_date_epoch": timestamp,
        "wasm": {
            "path": str(WASM_PATH),
            "sha256": digest(wasm),
            "bytes": len(wasm),
            "target": pins["target"],
            **module_info,
        },
        "toolchain": {"rustc": rustc, "cargo": cargo},
        "build": {
            "package": "beaconcrypt-wasm",
            "profile": "release",
            "locked": True,
            "environment": {
                key: value
                for key, value in sorted(os.environ.items())
                if key
                in {
                    "RUSTFLAGS",
                    "CARGO_ENCODED_RUSTFLAGS",
                    "RUSTC_WRAPPER",
                    "RUSTC_WORKSPACE_WRAPPER",
                    "CARGO_BUILD_RUSTFLAGS",
                }
                or key.startswith("CARGO_PROFILE_")
                or (key.startswith("CARGO_TARGET_") and key.endswith("_RUSTFLAGS"))
            },
        },
        "build_inputs_sha256": build_inputs(repo),
    }
    (repo / BUILD_INFO_PATH).write_bytes(json_bytes(info))
    return info


def module_files(repo):
    files = {}
    for pattern in ("*.go", "*.c", "*.h", "*.s", "*.S"):
        files.update(
            {
                path.name: path.read_bytes()
                for path in repo.glob(pattern)
                if path.is_file()
            }
        )
    for required in ("go.mod", "go.sum", "LICENSE", "beaconcrypt/bindings.h"):
        files[required] = (repo / required).read_bytes()
    for optional in ("README.md", "doc/wasm.md", "beaconcrypt-parse/generated/LICENSE"):
        if (repo / optional).is_file():
            files[optional] = (repo / optional).read_bytes()
    for path in sorted((repo / "internal").rglob("*")):
        if path.is_symlink():
            raise ValueError(f"module bundle must not contain symlinks: {path}")
        if path.is_file() and (
            path.suffix == ".go" or path.relative_to(repo) == WASM_PATH
        ):
            files[path.relative_to(repo).as_posix()] = path.read_bytes()
    for path in sorted((repo / "testdata").rglob("*")):
        if path.is_symlink():
            raise ValueError(f"module bundle must not contain symlinks: {path}")
        if path.is_file():
            files[path.relative_to(repo).as_posix()] = path.read_bytes()
    if WASM_PATH.as_posix() not in files:
        raise ValueError("embedded Wasm is missing; run scripts/build-wasm.sh first")
    if not re.search(
        r"^module\s+" + re.escape(MODULE) + r"\s*$", files["go.mod"].decode(), re.M
    ):
        raise ValueError("bundle go.mod does not declare the Beaconcrypt module path")
    return files


def package(repo, output_dir, version, require_clean=False):
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._+-]*", version):
        raise ValueError("version must be a safe archive-name component")
    info = json.loads((repo / BUILD_INFO_PATH).read_text())
    wasm = (repo / WASM_PATH).read_bytes()
    if digest(wasm) != info["wasm"]["sha256"] or len(wasm) != info["wasm"]["bytes"]:
        raise ValueError("Wasm differs from recorded build; rebuild before packaging")
    inspect_wasm(wasm)
    if build_inputs(repo) != info["build_inputs_sha256"]:
        raise ValueError(
            "Rust/build inputs changed after the Wasm build; rebuild before packaging"
        )
    revision, timestamp, dirty = git_state(repo)
    if revision != info["source_revision"]:
        raise ValueError(
            "source revision changed after the Wasm build; rebuild before packaging"
        )
    if require_clean and (dirty or info["source_dirty"]):
        raise ValueError(
            "release packaging requires clean source at build and package time"
        )
    files = module_files(repo)
    manifest = {
        **info,
        "module": MODULE,
        "version": version,
        "source_dirty": dirty or info["source_dirty"],
        "source_date_epoch": timestamp,
        "files_sha256": {name: digest(data) for name, data in sorted(files.items())},
    }
    files[MANIFEST_NAME] = json_bytes(manifest)
    output_dir.mkdir(parents=True, exist_ok=True)
    archive_name = f"beaconcrypt-go-{version}-wasm.tar.gz"
    root_name = f"beaconcrypt-go-{version}"
    archive_path = output_dir / archive_name
    # Deterministic metadata/order for identical inputs, rather than claiming
    # that Rust produces identical bytes across arbitrary hosts/toolchains.
    with archive_path.open("wb") as raw:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=raw, mtime=timestamp
        ) as compressed:
            with tarfile.open(
                fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT
            ) as archive:
                for name, data in sorted(files.items()):
                    member = tarfile.TarInfo(f"{root_name}/{name}")
                    member.size, member.mtime, member.mode = len(data), timestamp, 0o644
                    archive.addfile(member, io.BytesIO(data))
    assets = {"beaconcrypt.wasm": wasm, MANIFEST_NAME: files[MANIFEST_NAME]}
    for name, data in assets.items():
        (output_dir / name).write_bytes(data)
    hashes = {
        archive_name: digest(archive_path.read_bytes()),
        **{name: digest(data) for name, data in assets.items()},
    }
    (output_dir / "SHA256SUMS").write_text(
        "".join(f"{sha}  {name}\n" for name, sha in sorted(hashes.items()))
    )
    return archive_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo", type=Path, default=Path(__file__).resolve().parent.parent
    )
    parser.add_argument("--record-build", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=Path("dist/wasm"))
    parser.add_argument("--version")
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    try:
        if args.record_build:
            record_build(args.repo.resolve())
        elif args.version:
            print(
                package(
                    args.repo.resolve(),
                    args.output_dir.resolve(),
                    args.version,
                    args.require_clean,
                )
            )
        else:
            parser.error("--version is required when packaging")
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"package-wasm: {error}\n")


if __name__ == "__main__":
    main()
