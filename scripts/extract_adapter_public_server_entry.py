#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract the original public Server delegator with exact existing child bodies."""

from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib
import extract_adapter_record as common
import extract_adapter_public_wrappers as wrappers
import prepare_adapter_public_wrappers as preparation

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterPublicServerEntryExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
REQUEST = "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicServerEntryRequestExtraction.lean"
MODELS = ("TypesExternal.lean", "FunsExternal.lean")
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
FLAGS = [
    "--opaque=" + name
    for name in (
        "beaconcrypt",
        "beaconcrypt_core",
        "beaconcrypt_crypto",
        "beaconcrypt_parse",
        "core",
        "alloc",
        "std",
        "rand_core",
        "hashbrown",
    )
]
FLAGS += [
    "--include=" + name
    for name in (
        "core::option::Option",
        "core::ops::control_flow::ControlFlow",
        "core::result::Result",
        "core::convert::Infallible",
        "beaconcrypt::server::_::get_shared_secret_with_rng",
    )
]
FLAGS += ["--start-from=beaconcrypt::server::_::get_shared_secret_with_rng"]
RAW_SHA256 = {
    "Funs.lean": "ed6840db8064aa6fdf33f8266ff7bbe252ecd9b7c98bcd4e903d5ab493f74fe8",
    "Types.lean": "203e203b492f16e8159507be81dfbc87db1de72430aaf796d65b91eaf48e3a9f",
    "FunsExternal_Template.lean": "fd30b8f004a93275728490a6f6f24a921d2f08f31c85a19db523d685eed5ea59",
    "TypesExternal_Template.lean": "0bd18a9ea20e2561ede74c71734bde97a09ca188da725f85600a81a20b9d10c0",
}
TOOL_SHA256 = {
    "charon": "60ac6a5c4bf9151f0d6db961009268b91ea445e3a5c93bdb8dbfe5b48da36ebc",
    "aeneas": "88bc16127fd3f4ebbb72c9d0620d7b4c0c3b0810f8eebcc46c219ff7bba60727",
}
MODEL_SHA256 = {
    "TypesExternal.lean": "49f0a6d409f34778a410bc6803f087cf60fa1907a5ce8bbba5a3fdca45e22e46",
    "FunsExternal.lean": "bdf536336e045713305c01f56edd0350f91a0c692bc08f557599c301f100177b",
}
SOURCE = """\tpub fn get_shared_secret_with_rng<R: TryCryptoRng + ?Sized>(
\t\t&mut self,
\t\tbuffer: &[u8],
\t\trng: &mut R,
\t) -> Option<RegistrationOutput> {
\t\tlet lookup = self.authenticate_registration_lookup(buffer)?;
\t\tself.get_shared_secret_from_lookup_with_rng(lookup, rng)
\t}"""
DEPENDENCIES = (
    "scripts/extract_adapter_public_server_entry.py",
    "scripts/extract_adapter_record.py",
    "scripts/extract_adapter_public_wrappers.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperRequestExtraction.lean",
)


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def inputs(root: Path = ROOT) -> dict[str, str]:
    paths = {
        root / name
        for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "hax.toml")
        if (root / name).exists()
    }
    for member in preparation.MEMBERS:
        paths.update(
            root / member / name
            for name in ("Cargo.toml", "build.rs")
            if (root / member / name).exists()
        )
        paths.update(
            path for path in (root / member / "src").rglob("*") if path.is_file()
        )
    return {
        path.relative_to(root).as_posix(): digest(path.read_bytes())
        for path in sorted(paths)
    }


def require_source(root: Path = ROOT) -> None:
    text = (root / "beaconcrypt/src/server.rs").read_text()
    if text.count(SOURCE) != 1 or text.count("pub fn get_shared_secret_with_rng<") != 1:
        raise ValueError("original public Server delegator changed")


def immutable_fixture(root: Path, destination: Path) -> dict[str, str]:
    if (
        destination.exists()
        or destination.resolve() == root.resolve()
        or root.resolve() in destination.resolve().parents
    ):
        raise ValueError("entry fixture must be new and outside the repository")
    roster = inputs(root)
    destination.mkdir(parents=True)
    for name in roster:
        if name == "hax.toml":
            continue
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / name, target)
    verify_fixture(root, destination, roster)
    return roster


def verify_fixture(root: Path, fixture: Path, roster: dict[str, str]) -> None:
    if roster != inputs(root):
        raise ValueError("entry source input roster drift")
    for name, expected in roster.items():
        if name != "hax.toml" and digest((fixture / name).read_bytes()) != expected:
            raise ValueError("immutable entry fixture changed: " + name)


def normalize(raw: bytes, name: str) -> bytes:
    if name not in RAW_SHA256 or digest(raw) != RAW_SHA256[name]:
        raise ValueError("unreviewed pinned entry extraction: " + name)
    text = raw.decode()
    for linter in wrappers.LINTERS:
        old = "set_option linter." + linter + " false\n"
        if text.count(old) != 1:
            raise ValueError("entry generated warning-policy boundary changed")
        text = text.replace(old, "")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + wrappers.POLICY, 1)
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_public_server_entry\n"
        + wrappers.BASE_BINDERS
        + (wrappers.FUN_BINDERS if name == "Funs.lean" else ""),
    )
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_public_server_entry\n")
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def denormalize(contents: bytes, name: str) -> bytes:
    if name not in ("Types.lean", "Funs.lean"):
        raise ValueError("unknown entry generated artifact")
    common.require_handwritten_warning_policy(contents, name)
    text = contents.decode()
    binders = wrappers.BASE_BINDERS + (
        wrappers.FUN_BINDERS if name == "Funs.lean" else ""
    )
    before = "namespace beaconcrypt_public_server_entry\n" + binders
    if (
        text.count(before) != 1
        or text.count("end beaconcrypt_public_server_entry\n") != 1
    ):
        raise ValueError("entry generated namespace/binders changed")
    text = text.replace(before, "namespace beaconcrypt\n", 1).replace(
        "end beaconcrypt_public_server_entry\n", "end beaconcrypt\n", 1
    )
    before = "open Std.Do\n" + wrappers.POLICY
    if text.count(before) != 1:
        raise ValueError("entry strict policy changed")
    text = text.replace(
        before,
        "open Std.Do\n"
        + "".join(
            "set_option linter." + linter + " false\n" for linter in wrappers.LINTERS
        ),
        1,
    )
    if digest(text.encode()) != RAW_SHA256[name]:
        raise ValueError("installed original entry source body changed")
    return text.encode()


def request(source: bytes) -> bytes:
    denormalize(source, "Funs.lean")
    marker = "/-- [beaconcrypt::server::{beaconcrypt::server::Server}::get_shared_secret_with_rng]"
    text = source.decode()
    if text.count(marker) != 1:
        raise ValueError("entry source function boundary changed")
    selected = text[text.index(marker) :].removesuffix(
        "end beaconcrypt_public_server_entry\n"
    )
    edits = (
        (
            "RustM ((core.option.Option server.RegistrationOutput) × server.Server × R)",
            "m ((core.option.Option server.RegistrationOutput) × server.Server × R)",
        ),
        (
            "server.Server.authenticate_registration_lookup self buffer",
            "server.Server.authenticate_registration_lookup (m := m) self buffer",
        ),
        (
            "core.option.Option.Insts.CoreOpsTry_traitTry.branch o",
            "BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (core.option.Option.Insts.CoreOpsTry_traitTry.branch o)",
        ),
        (
            "server.Server.get_shared_secret_from_lookup_with_rng\n      rand_coreTryCryptoRngInst self val rng",
            "server.Server.get_shared_secret_from_lookup_with_rng (m := m)\n      rand_coreTryCryptoRngInst self val rng",
        ),
        (
            "core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual\n        server.RegistrationOutput residual",
            "BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust\n        (core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual\n          server.RegistrationOutput residual)",
        ),
        ("ok (o1, self, rng)", "pure (o1, self, rng)"),
    )
    for before, after in edits:
        if selected.count(before) != 1:
            raise ValueError("entry source lift boundary changed: " + before)
        selected = selected.replace(before, after, 1)
    header = wrappers.POLICY
    header = (
        "-- SPDX-License-Identifier: 0BSD\n-- Generated by scripts/extract_adapter_public_server_entry.py; do not edit.\n"
        "-- Extracted input SHA-256: " + digest(source) + "\n"
        "import BeaconcryptCore.AdapterPublicWrapperRequestExtraction\n"
        "import BeaconcryptCore.AdapterPublicServerEntryExtraction.Funs\n"
        "open CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\n"
        "open RustM ControlFlow Error\nopen beaconcrypt_public_wrapper\n"
        + header
        + "noncomputable section\nnamespace beaconcrypt_public_request\n"
        + wrappers.BASE_BINDERS
        + wrappers.FUN_BINDERS
        + "variable {m : Type → Type} [Monad m] [BeaconcryptCore.Refinement.AdapterRecordRequestMonad.LiftRust m]\n"
        + "".join(
            "variable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad."
            + kind
            + " m]\n"
            for kind in (
                "LocalOperations",
                "CryptoOperations",
                "ContainerOperations",
                "Codecs",
                "ChildOperations",
            )
        )
    )
    return (header + selected + "\nend beaconcrypt_public_request\n").encode()


def receipt(root: Path, contents: dict[str, bytes], tools: dict[str, str]) -> dict:
    return {
        "schema": 1,
        "entry": "beaconcrypt::server::Server::get_shared_secret_with_rng",
        "tools": common.PINNED_TOOLS,
        "versions": common.PINNED_VERSIONS,
        "tool_sha256": tools,
        "flags": FLAGS,
        "fixture": "byte-identical-original-workspace",
        "source_sha256": inputs(root),
        "dependency_sha256": {
            name: digest((root / name).read_bytes()) for name in DEPENDENCIES
        },
        "installed_sha256": {
            name: digest(contents[name]) for name in (*INSTALLED, *MODELS)
        },
        "request_sha256": digest(request(contents["Funs.lean"])),
        "raw_sha256": RAW_SHA256,
    }


def check_source(root: Path = ROOT, destination: Path | None = None) -> None:
    require_source(root)
    common.validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    target = destination or root / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
    stored = json.loads((target / "provenance.json").read_text())
    common.require_hash_roster(
        stored.get("tool_sha256"), set(common.PINNED_TOOLS), "tool_sha256"
    )
    if stored["tool_sha256"] != TOOL_SHA256:
        raise ValueError("entry pinned tool identity changed")
    contents = {name: (target / name).read_bytes() for name in (*INSTALLED, *MODELS)}
    for name in ("Types.lean", "Funs.lean"):
        denormalize(contents[name], name)
    templates = json.loads(contents["external-signatures.json"])
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("entry external declaration roster changed")
    for name, text in templates.items():
        if digest(text.encode()) != RAW_SHA256[name]:
            raise ValueError("entry external template changed")
    if stored != receipt(root, contents, stored["tool_sha256"]):
        raise ValueError("entry source/interface/provenance drift")
    if (root / REQUEST).read_bytes() != request(contents["Funs.lean"]):
        raise ValueError("entry monadic source lift drift")
    for name in MODELS:
        if digest(contents[name]) != MODEL_SHA256[name]:
            raise ValueError("entry exact helper/type alias changed: " + name)
        common.require_model(contents[name], name)
        common.require_handwritten_warning_policy(contents[name], name)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check-source", action="store_true")
    modes.add_argument("--check", action="store_true")
    modes.add_argument("--write", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--review-external-signatures", action="store_true")
    parser.add_argument(
        "--tools-root", type=Path, default=Path.home() / ".cache/hax/tools"
    )
    args = parser.parse_args()
    if args.review_external_signatures and not args.write:
        parser.error("--review-external-signatures requires --write")
    require_source()
    common.validate_configuration(tomllib.loads((ROOT / "hax.toml").read_text()))
    if args.check_source:
        check_source()
        print(
            "Original public Server entry, exact helper aliases and request lift match"
        )
        return 0
    if args.work_dir is None:
        parser.error("--work-dir is required")
    if args.write and not args.review_external_signatures:
        parser.error("--write requires --review-external-signatures")
    work = common.isolated_work_directory(args.work_dir)
    common.validate_work_paths(work)
    work.mkdir(parents=True, exist_ok=True)
    before = inputs()
    fixture = work / "source"
    immutable_fixture(ROOT, fixture)
    environment = common.extraction_environment(work)
    tools = {
        name: args.tools_root / name / version / name
        for name, version in common.PINNED_TOOLS.items()
    }
    tool_hashes = {name: digest(path.read_bytes()) for name, path in tools.items()}
    if tool_hashes != TOOL_SHA256:
        raise ValueError("entry extraction tools differ from reviewed pins")
    commands = (
        [
            str(tools["charon"]),
            "cargo",
            "--preset=aeneas",
            "--sysroot=default",
            *FLAGS,
            "--dest-file",
            str(work / "beaconcrypt.llbc"),
            "--",
            "-p",
            "beaconcrypt",
            "--lib",
            "--locked",
            "--no-default-features",
            "--features=beacon,server,pqxdh",
        ],
        [
            str(tools["aeneas"]),
            "-backend",
            "lean",
            "-core-models-lib",
            "-split-files",
            "-specs",
            "hax",
            "-no-progress-bar",
            "-sequential",
            "-abort-on-error",
            str(work / "beaconcrypt.llbc"),
            "-dest",
            str(work / "generated"),
            "-subdir",
            SUBDIRECTORY,
        ],
    )
    (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
    for name, command in zip(("charon", "aeneas"), commands, strict=True):
        wrappers.run(command, environment, work / (name + ".log"), fixture)
        if (
            name == "charon"
            and json.loads((work / "beaconcrypt.llbc").read_text())["has_errors"]
        ):
            raise ValueError("incomplete original entry extraction")
    verify_fixture(ROOT, fixture, before)
    raw = {
        name: (work / "generated" / SUBDIRECTORY / name).read_bytes()
        for name in common.GENERATED
    }
    for name, value in raw.items():
        if digest(value) != RAW_SHA256[name]:
            raise ValueError("unreviewed fresh entry artifact: " + name)
    templates = {
        name: raw[name].decode()
        for name in ("TypesExternal_Template.lean", "FunsExternal_Template.lean")
    }
    contents = {
        name: normalize(raw[name], name) for name in ("Types.lean", "Funs.lean")
    }
    contents["external-signatures.json"] = (
        json.dumps(templates, indent=2, sort_keys=True) + "\n"
    ).encode()
    contents.update({name: (DESTINATION / name).read_bytes() for name in MODELS})
    for name in MODELS:
        if digest(contents[name]) != MODEL_SHA256[name]:
            raise ValueError("entry exact helper/type alias changed: " + name)
    metadata = receipt(ROOT, contents, tool_hashes)
    if args.write:
        for name, value in contents.items():
            (DESTINATION / name).write_bytes(value)
        (DESTINATION / "provenance.json").write_text(
            json.dumps(metadata, indent=2, sort_keys=True) + "\n"
        )
        (ROOT / REQUEST).write_bytes(request(contents["Funs.lean"]))
    else:
        check_source()
        if json.loads((DESTINATION / "provenance.json").read_text()) != metadata:
            raise ValueError("fresh original entry extraction drift")
        for name, value in contents.items():
            if (DESTINATION / name).read_bytes() != value:
                raise ValueError("fresh entry artifact drift: " + name)
    print("Pinned original public Server entry extraction and mutable ABI match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
