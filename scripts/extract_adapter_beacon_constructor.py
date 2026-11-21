#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract three unchanged public Beacon constructors and lift exact typed leaves."""

from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib
import extract_adapter_record as common
import extract_adapter_public_server_entry as entry
import extract_adapter_public_wrappers as wrappers
import extract_registration_schema as schema
import lift_adapter_public_wrapper_requests as lift
import check_registration_codec_extraction as checked

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterBeaconConstructorExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
REQUEST = "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterBeaconConstructorRequestExtraction.lean"
BINDINGS = (
    "beaconcrypt-core/proofs/lean/adapter-beacon-constructor-request-bindings.json"
)
SHARED_TYPES = "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Types.lean"
MODELS = ("TypesExternal.lean", "FunsExternal.lean")
INSTALLED = ("Types.lean", "Funs.lean", "source-evidence.json")
ROOTS = ("try_new_with_rng", "try_new", "new")
FLAGS = [
    "--opaque=beaconcrypt",
    "--opaque=beaconcrypt_core",
    "--opaque=beaconcrypt_crypto",
    "--opaque=beaconcrypt_parse",
    "--opaque=core",
    "--opaque=alloc",
    "--opaque=std",
    "--opaque=rand_core",
    "--opaque=hashbrown",
    "--include=core::option::Option",
    "--include=core::ops::control_flow::ControlFlow",
    "--include=core::result::Result",
    "--include=core::convert::Infallible",
    "--include=beaconcrypt::beacon::Beacon",
    "--include=beaconcrypt::beacon::BeaconState",
    "--include=beaconcrypt::beacon::RegistrationAuthentication",
    "--include=beaconcrypt_crypto::crypto_sign::KeyPair",
    "--include=beaconcrypt_crypto::crypto_kx::KeyPair",
    "--include=beaconcrypt_crypto::crypto_kem::mlkem768::KeyPair",
    "--include=beaconcrypt::error::KeyGenError",
    "--include=beaconcrypt_core::pqxdh::ServerBinding",
    "--include=beaconcrypt::beacon::_::new",
    "--include=beaconcrypt::beacon::_::try_new",
    "--include=beaconcrypt::beacon::_::try_new_with_rng",
    "--include=beaconcrypt_crypto::OsRng",
    "--start-from=beaconcrypt::beacon::_::new",
    "--start-from=beaconcrypt::beacon::_::try_new",
    "--start-from=beaconcrypt::beacon::_::try_new_with_rng",
]
RAW_SHA256 = {
    "Funs.lean": "a93c3614a62e4b393032574487ac9dd867adf4ddc6ba4a40141c7aa8f9860ecd",
    "Types.lean": "a86e431fc21f2ef07750782f473d8bd59c9daef8f51f0021f6a24fd9c0bd0052",
    "FunsExternal_Template.lean": "c77512cb200ed1ab80a9cba00593f6eedb62b51213831146a17fdc08ee500c26",
    "TypesExternal_Template.lean": "026d88ee829240f13619108721c1c0e4536b0956f0cd144dfa935149a4be88b9",
}
MODEL_SHA256 = {
    "TypesExternal.lean": "3343d63056b46225cf7619534f067617574f79a289ee7b3935604823f5868b72",
    "FunsExternal.lean": "f4bd9f1ea31fd264b0865fada7ea698d9debf8bf26a7e25cf495800cd81843a5",
}
TOOL_SHA256 = {
    "charon": "60ac6a5c4bf9151f0d6db961009268b91ea445e3a5c93bdb8dbfe5b48da36ebc",
    "aeneas": "88bc16127fd3f4ebbb72c9d0620d7b4c0c3b0810f8eebcc46c219ff7bba60727",
}
BINDINGS_SHA256 = "fa3ec69ae635a6cca8235b05eb709ef414f2d65b8dd44ff56071a925d16cc786"
REQUEST_HEADER = "-- SPDX-License-Identifier: 0BSD\nimport BeaconcryptCore.AdapterBeaconConstructorExtraction.Funs\nimport BeaconcryptCore.AdapterPublicWrapperRequestExtraction\nimport BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction\nopen CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM ControlFlow Error\nopen beaconcrypt_constructor beaconcrypt_public_wrapper\nset_option autoImplicit false\nset_option warningAsError true\nset_option maxRecDepth 4096\nnamespace BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]\nvariable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]\n/-- Shared constructor requests: only the Server controller uses ML generation. -/\nclass Operations (m : Type → Type) where\n  mldsaGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m\n    (core.result.Result beaconcrypt_public_wrapper.auth.MldsaIdentity Unit × R)\n  edGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m\n    (core.result.Result beaconcrypt_crypto.crypto_sign.KeyPair primitive.Error × R)\n  kemGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m\n    (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair primitive.Error × R)\n@[instance_reducible] def rustOperations [ops : AdapterBeaconConstructorPrimitive.Operations] : Operations RustM where\n  mldsaGenerate := ops.mldsaGenerate\n  edGenerate := ops.edGenerate\n  kemGenerate := ops.kemGenerate\nattribute [instance] rustOperations\nend BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad\nnoncomputable section\nnamespace beaconcrypt_constructor_request\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]\nvariable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]\nvariable [BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]\nvariable {m : Type → Type} [Monad m] [BeaconcryptCore.Refinement.AdapterRecordRequestMonad.LiftRust m]\nvariable [BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.ChildOperations m]\n"


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def require_roots(contents: bytes, templates: bytes) -> None:
    code = checked.code(contents)
    external = checked.code(templates)
    for name in ROOTS:
        full = "beacon.Beacon." + name
        if (
            len(
                re.findall(r"^def\s+" + re.escape(full) + r"(?=\s|\{|\(|:)", code, re.M)
            )
            != 1
        ):
            raise ValueError("selected constructor missing or opaque: " + full)
        if re.search(
            r"\b(?:axiom|opaque)\s+" + re.escape(full) + r"(?=\s|\{|\(|:)", external
        ):
            raise ValueError("selected constructor became an external premise: " + full)
    common.require_model(contents, "constructor source")


def alpha(text: str, name: str) -> str:
    rows = []
    for suffix in ("_4", "_3", "_2", "_1", ""):
        decl = "beacon.Beacon.try_new_with_rng.closure" + suffix
        if name == "Types.lean":
            rows += [
                (decl, "R", "_R"),
                (decl, "Clause0_Clause0_Error", "_Clause0_Clause0_Error"),
            ]
        else:
            kind = "TryFromSliceError" if suffix == "_1" else "CryptoError"
            decl += ".Insts.CoreOpsFunctionFnOnceTuple" + kind + "KeyGenError.call_once"
            rows += [
                (decl, before, "_" + before)
                for before in ("rand_coreTryCryptoRngInst", "c", "tupled_args")
            ]
    for declaration, before, after in rows:
        start, end = wrappers.fragment_range(text, declaration)
        fragment = text[start:end]
        code = checked.code(fragment.encode())
        if len(re.findall(r"\b" + re.escape(before) + r"\b", code)) != 1:
            raise ValueError(
                "constructor unused binder changed: " + declaration + ":" + before
            )
        if not re.search(r"[({]" + re.escape(before) + r"\s*:", code):
            raise ValueError("constructor alpha edit is not an unused binder")
        fragment = re.sub(r"\b" + re.escape(before) + r"\b", after, fragment)
        text = text[:start] + fragment + text[end:]
    return text


def shared_blocks(raw: bytes, shared: bytes) -> tuple[str, dict[str, str]]:
    text = raw.decode()
    aliases = {}
    for name in ("RegistrationAuthentication", "BeaconState", "Beacon"):
        pattern = (
            r"/-- \[beaconcrypt::beacon::" + name + r"\][\s\S]*?(?=/--|end beaconcrypt)"
        )
        new = re.findall(pattern, text)
        old = re.findall(pattern, shared.decode())
        if len(new) != 1 or len(old) != 1 or new[0] != old[0]:
            raise ValueError("actual shared Beacon layout changed: " + name)
        aliases[name] = digest(new[0].encode())
        text = text.replace(new[0], "", 1)
    return text, aliases


def normalize(raw: bytes, name: str, shared: bytes) -> bytes:
    if name not in ("Types.lean", "Funs.lean") or digest(raw) != RAW_SHA256[name]:
        raise ValueError("unreviewed original constructor extraction: " + name)
    common.require_model(raw, name)
    text = raw.decode()
    if name == "Types.lean":
        text, _ = shared_blocks(raw, shared)
    if (
        tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M))
        != wrappers.LINTERS
    ):
        raise ValueError("constructor generated warning policy changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    text = text.replace("open Std.Do\n", "open Std.Do\n" + wrappers.POLICY, 1)
    binders = wrappers.BASE_BINDERS
    if name == "Funs.lean":
        binders += (
            "\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]\n"
            "variable [BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Operations]\n"
            "variable [BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]\n"
            "variable [beaconcrypt.auth.Operations]\n"
        )
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_constructor\nopen beaconcrypt_public_wrapper\n"
        + binders,
        1,
    )
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_constructor\n", 1)
    text = alpha(text, name)
    if name == "Funs.lean":
        text = text.replace(
            "import Aeneas\n",
            "import Aeneas\nimport BeaconcryptCore.Refinement.AdapterBeaconConstructorString\n",
            1,
        )
        if text.count('"Failed to construct beacon")') != 1:
            raise ValueError("constructor unchanged panic literal changed")
        text = text.replace(
            '"Failed to construct beacon")',
            '"Failed to construct beacon" BeaconcryptCore.Refinement.AdapterBeaconConstructorString.failure_bound)',
            1,
        )
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def request(source: bytes, bindings: bytes) -> bytes:
    if digest(bindings) != BINDINGS_SHA256:
        raise ValueError("constructor reviewed binding table changed")
    control = json.loads(bindings)
    if digest(source) != control["source_sha256"]:
        raise ValueError("constructor request source changed")
    text = source.decode()
    marker = (
        "/-- [beaconcrypt::beacon::{beaconcrypt::beacon::Beacon}::try_new_with_rng]:"
    )
    if text.count(marker) != 1:
        raise ValueError("constructor source boundary changed")
    selected = text[text.index(marker) :].replace(
        "end beaconcrypt_constructor\n", "end beaconcrypt_parse\n"
    )
    groups = schema.chunks(selected)
    if len(groups) != 3 or [names[0] for names, _ in groups] != [
        "beacon.Beacon." + name for name in ROOTS
    ]:
        raise ValueError("constructor request declaration roster changed")
    output = []
    for (names, chunk), row in zip(groups, control["definitions"], strict=True):
        if names != (row["name"],) or digest(chunk.encode()) != row["sha256"]:
            raise ValueError("constructor source declaration changed")
        split = checked.code(chunk.encode()).index(":=")
        output.append(
            lift.replace_leaves(chunk[:split], row["signature"])
            + ":="
            + lift.replace_leaves(chunk[split + 2 :], row["body"])
        )
    return (
        REQUEST_HEADER + "\n".join(output) + "\nend beaconcrypt_constructor_request\n"
    ).encode()


def snapshot(root: Path, destination: Path) -> dict:
    dependencies = (
        "scripts/extract_adapter_beacon_constructor.py",
        "scripts/extract_adapter_public_server_entry.py",
        "scripts/extract_adapter_public_wrappers.py",
        "scripts/extract_adapter_record.py",
        "scripts/extract_registration_schema.py",
        "scripts/lift_adapter_public_wrapper_requests.py",
        "scripts/check_registration_codec_extraction.py",
        BINDINGS,
        SHARED_TYPES,
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterBeaconConstructorString.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Funs.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/TypesExternal.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/PlatformOperations.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperRequestExtraction.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterPublicWrapperRequestMonad.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterPublicWrapperLiftFunction.lean",
    )
    return {
        "source_sha256": entry.inputs(root),
        "dependency_sha256": {
            name: digest((root / name).read_bytes()) for name in dependencies
        },
        "model_sha256": {
            name: digest((destination / name).read_bytes()) for name in MODELS
        },
    }


def metadata() -> dict:
    return {
        "schema": 1,
        "entries": list(ROOTS),
        "flags": FLAGS,
        "tools": common.PINNED_TOOLS,
        "tool_sha256": TOOL_SHA256,
        "versions": common.PINNED_VERSIONS,
        "features": "beacon,server,pqxdh,std",
        "fixture": "byte-identical-original-workspace",
        "raw_generated_sha256": RAW_SHA256,
        "mutable_rng": "every error arm returns reached RNG",
        "normalization": "unused-binder-alpha; exact shared type aliases; strict warning header; explicit proof-irrelevant panic-string bound",
        "request_binding_sha256": BINDINGS_SHA256,
    }


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    common.validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    provenance = json.loads((destination / "provenance.json").read_bytes())
    expected = {**metadata(), **snapshot(root, destination)}
    installed = provenance.pop("installed_sha256", None)
    if provenance != expected:
        raise ValueError("constructor source/tools/model/provenance drift")
    if expected["model_sha256"] != MODEL_SHA256:
        raise ValueError("constructor reviewed primitive ABI changed")
    if not isinstance(installed, dict) or set(installed) != set(INSTALLED) | {
        "request"
    }:
        raise ValueError("constructor artifact roster changed")
    for name in INSTALLED:
        if digest((destination / name).read_bytes()) != installed[name]:
            raise ValueError("constructor installed source drift: " + name)
    evidence = json.loads((destination / "source-evidence.json").read_bytes())
    if set(evidence) != {"raw", "shared_type_sha256"} or set(evidence["raw"]) != set(
        RAW_SHA256
    ):
        raise ValueError("constructor raw source evidence roster changed")
    raw = {name: value.encode() for name, value in evidence["raw"].items()}
    if {name: digest(value) for name, value in raw.items()} != RAW_SHA256:
        raise ValueError("constructor raw evidence changed")
    require_roots(raw["Funs.lean"], raw["FunsExternal_Template.lean"])
    shared = (root / SHARED_TYPES).read_bytes()
    if shared_blocks(raw["Types.lean"], shared)[1] != evidence["shared_type_sha256"]:
        raise ValueError("constructor exact type alias certificate changed")
    for name in ("Types.lean", "Funs.lean"):
        if normalize(raw[name], name, shared) != (destination / name).read_bytes():
            raise ValueError("constructor checked normalization changed")
    for name in MODELS:
        common.require_model((destination / name).read_bytes(), name)
        common.require_handwritten_warning_policy(
            (destination / name).read_bytes(), name
        )
    lifted = request(
        (destination / "Funs.lean").read_bytes(), (root / BINDINGS).read_bytes()
    )
    if (
        digest(lifted) != installed["request"]
        or lifted != (root / REQUEST).read_bytes()
    ):
        raise ValueError("constructor exact request lift changed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-source", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--review-external-signatures", action="store_true")
    parser.add_argument(
        "--tools-root", type=Path, default=Path.home() / ".cache/hax/tools"
    )
    args = parser.parse_args()
    if args.check_source:
        check_source()
        print(
            "Original Beacon constructors, concrete aliases and typed request lift match"
        )
        return 0
    if args.work_dir is None or (args.write and not args.review_external_signatures):
        parser.error(
            "fresh extraction requires --work-dir; --write also requires --review-external-signatures"
        )
    work = common.isolated_work_directory(args.work_dir)
    work.mkdir(parents=True, exist_ok=True)
    before = snapshot(ROOT, DESTINATION)
    entry.immutable_fixture(ROOT, work / "source")
    environment = common.extraction_environment(work)
    tools = {
        name: args.tools_root / name / version / name
        for name, version in common.PINNED_TOOLS.items()
    }
    if {name: digest(path.read_bytes()) for name, path in tools.items()} != TOOL_SHA256:
        raise ValueError("constructor extraction tools differ from reviewed pins")
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
            "--features=beacon,server,pqxdh,std",
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
        wrappers.run(command, environment, work / (name + ".log"), work / "source")
        if (
            name == "charon"
            and json.loads((work / "beaconcrypt.llbc").read_bytes())["has_errors"]
        ):
            raise ValueError("constructor extraction incomplete")
    entry.verify_fixture(ROOT, work / "source", entry.inputs(ROOT))
    if snapshot(ROOT, DESTINATION) != before:
        raise ValueError("constructor inputs changed during extraction")
    raw = {
        name: (work / "generated" / SUBDIRECTORY / name).read_bytes()
        for name in RAW_SHA256
    }
    if {name: digest(value) for name, value in raw.items()} != RAW_SHA256:
        raise ValueError("fresh original constructor changed")
    require_roots(raw["Funs.lean"], raw["FunsExternal_Template.lean"])
    shared = (ROOT / SHARED_TYPES).read_bytes()
    evidence = {
        "raw": {name: value.decode() for name, value in raw.items()},
        "shared_type_sha256": shared_blocks(raw["Types.lean"], shared)[1],
    }
    contents = {
        name: normalize(raw[name], name, shared) for name in ("Types.lean", "Funs.lean")
    }
    contents["source-evidence.json"] = (
        json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    ).encode()
    lifted = request(contents["Funs.lean"], (ROOT / BINDINGS).read_bytes())
    provenance = {
        **metadata(),
        **before,
        "installed_sha256": {
            **{name: digest(value) for name, value in contents.items()},
            "request": digest(lifted),
        },
    }
    if args.write:
        for name, value in contents.items():
            (DESTINATION / name).write_bytes(value)
        (ROOT / REQUEST).write_bytes(lifted)
        (DESTINATION / "provenance.json").write_text(
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        )
    else:
        check_source()
        if json.loads((DESTINATION / "provenance.json").read_bytes()) != provenance:
            raise ValueError("constructor fresh provenance differs")
    print("Pinned original Beacon constructor bodies and all mutable RNG arms match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
