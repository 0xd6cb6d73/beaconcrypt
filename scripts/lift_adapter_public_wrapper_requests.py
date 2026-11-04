#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Lift all 49 reviewed public-wrapper definitions by exact typed leaf rebinding.

The frozen binding table records each signature and body identifier separately.
Control flow, continuation placement, callback captures and source ordering are
retained. Three source loops use rank-bounded iteration; separate Lean theorems
prove that their RustM specialization equals the original extracted loops.
"""

from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

import check_registration_codec_extraction as checked
import extract_registration_schema as schema

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path(
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Funs.lean"
)
BINDINGS = Path(
    "beaconcrypt-core/proofs/lean/adapter-public-wrapper-request-bindings.json"
)
DESTINATION = Path(
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperRequestExtraction.lean"
)
BINDINGS_SHA256 = "f237aa3629951d5ac351f2edfc80662ddf3cbedc850ae387413f6de99e09295d"
TOKEN = re.compile(
    r"(?<![\w])(?:[A-Za-z_][A-Za-z0-9_']*)(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
HEADER = "import BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction\nimport BeaconcryptCore.Refinement.AdapterPublicInitSourceLoop\nimport BeaconcryptCore.Refinement.AdapterPublicAgreementSourceLoop\nimport BeaconcryptCore.Refinement.AdapterPublicFinishSourceLoop\nopen CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM ControlFlow Error\nopen Std.Do\nopen beaconcrypt_public_wrapper\nset_option autoImplicit false\nset_option warningAsError true\nset_option maxHeartbeats 1000000\nset_option maxRecDepth 4096\nnoncomputable section\nnamespace beaconcrypt_public_request\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]\nvariable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.ContainerOperations]\nvariable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Codecs]\nvariable [BeaconcryptCore.Refinement.RegistrationWriterPrimitive.Operations]\nvariable [BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]\nvariable [beaconcrypt.ratchet.Operations] [beaconcrypt.auth.Operations]\nvariable {m : Type → Type} [Monad m] [BeaconcryptCore.Refinement.AdapterRecordRequestMonad.LiftRust m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.LocalOperations m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.ContainerOperations m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.Codecs m]\nvariable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.ChildOperations m]\n"


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def replace_leaves(text: str, bindings: list[dict]) -> str:
    mapping = {row["before"]: row for row in bindings}
    if len(mapping) != len(bindings):
        raise ValueError("duplicate source leaf binding")
    counts = {token: 0 for token in mapping}
    edits = []
    for match in TOKEN.finditer(checked.code(text.encode())):
        row = mapping.get(match[0])
        if row is not None:
            counts[match[0]] += 1
            edits.append((match.start(), match.end(), row["after"]))
    if any(counts[row["before"]] != row["count"] for row in bindings):
        raise ValueError("source leaf multiplicity changed")
    for start, end, after in reversed(edits):
        text = text[:start] + after + text[end:]
    return text


def transform(source: bytes, bindings: bytes) -> bytes:
    if digest(bindings) != BINDINGS_SHA256:
        raise ValueError("reviewed public wrapper bindings changed")
    control = json.loads(bindings)
    if digest(source) != control["source_sha256"]:
        raise ValueError("reviewed public wrapper source changed")
    source_text = source.decode()
    marker = "/-- [beaconcrypt::auth::fingerprint_pin]"
    if source_text.count(marker) != 1:
        raise ValueError("public wrapper source boundary changed")
    selected = source_text[source_text.index(marker) :].replace(
        "end beaconcrypt_public_wrapper\n", "end beaconcrypt_parse\n"
    )
    groups = schema.chunks(selected)
    if len(groups) != 49 or [names[0] for names, _ in groups] != [
        row["name"] for row in control["definitions"]
    ]:
        raise ValueError("public wrapper declaration roster changed")
    output = []
    for (names, chunk), row in zip(groups, control["definitions"], strict=True):
        name = names[0]
        if digest(chunk.encode()) != row["sha256"]:
            raise ValueError("public wrapper declaration changed: " + name)
        if re.search(
            r"\b(?:sorry|admit|axiom|opaque|unsafe|partial)\b",
            checked.code(chunk.encode()),
        ):
            raise ValueError("unchecked source declaration")
        if row["mode"] == "static":
            output.append(
                "abbrev " + name + " := @beaconcrypt_public_wrapper." + name + "\n"
            )
            continue
        split = checked.code(chunk.encode()).index(":=")
        signature, value = chunk[:split], chunk[split + 2 :]
        declaration = re.search(
            r"\bdef\s+" + re.escape(name) + r"(?=\s|\{|\(|:)",
            checked.code(signature.encode()),
        )
        if declaration is None:
            raise ValueError("source definition boundary changed")
        before = re.sub(
            r"^@\[rust_loop(?:_body)?\]\n",
            "",
            signature[: declaration.end()],
            flags=re.M,
        )
        output.append(
            before
            + replace_leaves(signature[declaration.end() :], row["signature"])
            + ":="
            + replace_leaves(value, row["body"])
        )
    return (
        "-- SPDX-License-Identifier: 0BSD\n-- Generated by scripts/lift_adapter_public_wrapper_requests.py; do not edit.\n"
        + "-- Extracted input SHA-256: "
        + digest(source)
        + "\n"
        + "-- Binding table SHA-256: "
        + digest(bindings)
        + "\n"
        + "-- Transformation SHA-256: "
        + digest(Path(__file__).read_bytes())
        + "\n"
        + HEADER
        + "\n".join(output)
        + "\nend beaconcrypt_public_request\n"
    ).encode()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = transform((ROOT / SOURCE).read_bytes(), (ROOT / BINDINGS).read_bytes())
    destination = ROOT / DESTINATION
    if args.write:
        destination.write_bytes(expected)
    elif not destination.exists() or destination.read_bytes() != expected:
        parser.error(
            "public wrapper requests differ; review generated diff with --write"
        )
    print("public wrapper requests match all 49 reviewed source definitions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
