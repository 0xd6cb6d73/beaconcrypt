#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Prepare isolated public-wrapper extraction inputs without editing production.

The two Rust changes only factor the original Init loop and distribute an
Option continuation through the four secret-role cases. LLBC preparation
distributes a block continuation through switches, preserving terminal exits.
The corresponding effect-polymorphic laws are checked in
Refinement/AdapterPublicControlNormalization. Every ordinary statement, branch
selector, call operand and loop body remains in the checked transformation.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import shutil

from registration_codec_normalization import close, mask

BEACON_LOOP_SHA256 = "d63c59d9e331b085cf28e1e591af76624defdfcd98af1a06785cef2b0ea5e832"
DH_SELECTION_SHA256 = "3203fc86d6d3efa27ac19233e31d607179f22b2e16640b0767fd1c3535630274"
RUST_CHANGED = ("beaconcrypt/src/beacon.rs", "beaconcrypt/src/pqxdh.rs")
MEMBERS = (
    "beaconcrypt",
    "beaconcrypt-core",
    "beaconcrypt-crypto",
    "beaconcrypt-parse",
    "beaconcrypt-ffi",
    "beaconcrypt-wasm",
)
LEAF_KINDS = {
    "StorageDead",
    "Drop",
    "StorageLive",
    "Assign",
    "Call",
    "Borrowck",
    "PlaceMention",
}
EXIT_KINDS = {"Return", "UnwindResume", "Break", "Continue", "Abort"}
CONTROL_KINDS = {"Switch", "Loop"}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def checked(contents: str, expected: str, label: str) -> None:
    if digest(contents.encode()) != expected:
        raise ValueError("unreviewed original " + label)


def factor_beacon(source: str) -> tuple[str, dict]:
    lexical = mask(source)
    start = source.index(
        "\t\tlet ready = loop {",
        source.index("pub fn get_registration_bundle_with_rng"),
    )
    opening = lexical.index("{", start)
    end = close(lexical, opening)
    if source[end + 1] != ";":
        raise ValueError("Init loop no longer ends its let binding")
    original = source[start : end + 2]
    checked(original, BEACON_LOOP_SHA256, "Init loop")
    body = source[opening + 1 : end]
    if body.count("break ready") != 1 or body.count("return None") != 1:
        raise ValueError("Init loop exit roster changed")
    helper_body = re.sub(r"\bself\b", "beacon", body).replace(
        "break ready", "return Some(ready)"
    )
    helper = """
// Isolated proof fixture: original operations with both exits returned to the caller.
fn _proof_beacon_init_ready(
    beacon: &Beacon,
    mut effect: beaconcrypt_core::registration::BeaconInitEffect,
) -> Option<beaconcrypt_core::registration::BeaconInitReady> {
    use beaconcrypt_core::registration::BeaconInitEffect;
    loop {""" + helper_body + "\n    }\n}\n"
    prepared = (
        source[:start]
        + "\t\tlet ready = _proof_beacon_init_ready(self, effect)?;"
        + source[end + 2 :]
        + helper
    )
    return prepared, {
        "law": "AdapterPublicControlNormalization.init_loop_factor",
        "original_sha256": BEACON_LOOP_SHA256,
        "original": original,
        "helper_body": helper_body,
        "helper_sha256": digest(helper.encode()),
        "exits": ["return None", "return Some(ready)"],
    }


def distribute_dh(source: str) -> tuple[str, dict]:
    start = source.index("\t\t\t\tlet secret: Option<&[u8]>")
    end = source.index("\n\t\t\t\tpending.resume(shared)", start)
    original = source[start:end]
    checked(original, DH_SELECTION_SHA256, "DH selection")
    roles = [
        ("LocalIdentity", "local_identity.as_ref()", "key.as_slice()"),
        (
            "ServerEphemeral",
            "server_ephemeral.as_ref()",
            "key.secret_key.as_bytes().as_slice()",
        ),
        ("BeaconPrekey", "keys.beacon_prekey", "key.as_bytes().as_slice()"),
        ("BeaconOneTime", "keys.beacon_one_time", "key.as_bytes().as_slice()"),
    ]
    prepared = "\t\t\t\tlet shared = match request.secret_role {\n"
    for role, value, view in roles:
        prepared += f"\t\t\t\t\tDhSecretRole::{role} => {value}.and_then(|key| {{\n"
        prepared += f"\t\t\t\t\t\tcrypto_scalarmult::scalarmult({view}, request.public_key).ok()\n"
        prepared += "\t\t\t\t\t}),\n"
    prepared += "\t\t\t\t};"
    return source[:start] + prepared + source[end:], {
        "law": "AdapterPublicControlNormalization.dh_selectionM",
        "original_sha256": DH_SELECTION_SHA256,
        "original": original,
        "prepared": prepared,
        "roles": [list(row) for row in roles],
    }


def prepare_source(root: Path, destination: Path) -> dict:
    root, destination = root.resolve(), destination.resolve()
    if destination == root or root in destination.parents:
        raise ValueError("wrapper extraction fixture must be outside the repository")
    if destination.exists():
        raise ValueError("wrapper extraction fixture must not exist")
    destination.mkdir(parents=True)
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        if (root / name).exists():
            shutil.copy2(root / name, destination / name)
    for member in MEMBERS:
        for name in ("Cargo.toml", "build.rs"):
            if (root / member / name).exists():
                (destination / member).mkdir(exist_ok=True)
                shutil.copy2(root / member / name, destination / member / name)
        if (root / member / "src").exists():
            shutil.copytree(root / member / "src", destination / member / "src")
    certificate = {}
    for name, transform in zip(
        RUST_CHANGED, (factor_beacon, distribute_dh), strict=True
    ):
        original = (root / name).read_text()
        prepared, evidence = transform(original)
        (destination / name).write_text(prepared)
        certificate[name] = {
            **evidence,
            "source_sha256": digest(original.encode()),
            "prepared_sha256": digest(prepared.encode()),
        }
    unchanged = {}
    for path in destination.rglob("*"):
        if (
            path.is_file()
            and path.relative_to(destination).as_posix() not in RUST_CHANGED
        ):
            name = path.relative_to(destination).as_posix()
            if path.read_bytes() != (root / name).read_bytes():
                raise ValueError("unreviewed fixture edit: " + name)
            unchanged[name] = digest(path.read_bytes())
    return {"source_changes": certificate, "unchanged_sha256": unchanged}


def hashcons_pool(value: object) -> dict:
    pool = {}

    def visit(node):
        if isinstance(node, dict):
            if set(node) == {"HashConsedValue"}:
                index, contents = node["HashConsedValue"]
                if index in pool and pool[index] != contents:
                    raise ValueError("inconsistent hash-cons definition")
                pool[index] = contents
            for contents in node.values():
                visit(contents)
        elif isinstance(node, list):
            for contents in node:
                visit(contents)

    visit(value)
    return pool


def recode_hashcons(value: object, pool: dict) -> object:
    seen = set()

    def visit(node):
        if isinstance(node, dict):
            if set(node) in ({"HashConsedValue"}, {"Deduplicated"}):
                index = (
                    node["HashConsedValue"][0]
                    if "HashConsedValue" in node
                    else node["Deduplicated"]
                )
                if index not in pool:
                    raise ValueError("undefined hash-cons reference")
                if index in seen:
                    return {"Deduplicated": index}
                seen.add(index)
                return {"HashConsedValue": [index, visit(pool[index])]}
            return {key: visit(contents) for key, contents in node.items()}
        if isinstance(node, list):
            return [visit(contents) for contents in node]
        return node

    return visit(value)


def prepare_llbc(original: dict) -> tuple[dict, dict]:
    prepared = copy.deepcopy(original)
    pool = hashcons_pool(original)
    distributions = []
    terminals = []

    def normalize(block, function):
        statements = block["statements"]
        for index, statement in enumerate(statements):
            kind = statement["kind"]
            if isinstance(kind, str):
                tag = kind
            elif isinstance(kind, dict) and len(kind) == 1:
                tag = next(iter(kind))
            else:
                raise ValueError("unreviewed LLBC statement shape")
            if tag not in LEAF_KINDS | EXIT_KINDS | CONTROL_KINDS:
                raise ValueError("unreviewed LLBC statement: " + tag)
            if tag in EXIT_KINDS:
                if index + 1 < len(statements):
                    terminals.append(
                        {
                            "function": function,
                            "exit": statement["id"],
                            "discarded": copy.deepcopy(statements[index + 1 :]),
                        }
                    )
                block["statements"] = statements[: index + 1]
                return
            if tag == "Loop":
                normalize(kind["Loop"], function)
            if tag == "Switch":
                switch = kind["Switch"]
                if not switch["branches"]:
                    raise ValueError("empty LLBC switch")
                if index + 1 < len(statements):
                    rest = statements[index + 1 :]
                    distributions.append(
                        {
                            "function": function,
                            "switch": statement["id"],
                            "branches": len(switch["branches"]),
                            "tail": copy.deepcopy(rest),
                        }
                    )
                    for branch in switch["branches"]:
                        branch["statements"].extend(copy.deepcopy(rest))
                    block["statements"] = statements[: index + 1]
                for branch in switch["branches"]:
                    normalize(branch, function)
                if len(block["statements"]) == index + 1:
                    return

    functions = []
    for function in prepared["translated"]["fun_decls"]:
        if (
            function
            and isinstance(function["body"], dict)
            and "Structured" in function["body"]
        ):
            name = function["item_meta"]["name"]
            functions.append(name)
            normalize(function["body"]["Structured"]["body"], name)
    serial = 0

    def refresh(node):
        nonlocal serial
        if isinstance(node, dict):
            if (
                "id" in node
                and "span" in node
                and ("kind" in node or "statements" in node)
            ):
                node["id"] = serial
                serial += 1
            for contents in node.values():
                refresh(contents)
        elif isinstance(node, list):
            for contents in node:
                refresh(contents)

    refresh(prepared)
    return recode_hashcons(prepared, pool), {
        "laws": [
            "AdapterPublicControlNormalization.branch_tail",
            "AdapterPublicControlNormalization.terminal_tail",
            "AdapterPublicControlNormalization.loop_congr",
        ],
        "functions": functions,
        "distributions": distributions,
        "terminal_tails": terminals,
        "refreshed_labels": serial,
    }


def check_llbc(original: dict, prepared: dict, certificate: dict) -> None:
    expected, evidence = prepare_llbc(original)
    if prepared != expected or certificate != evidence:
        raise ValueError("LLBC source-control certificate mismatch")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--fixture", type=Path)
    parser.add_argument("--llbc", type=Path)
    parser.add_argument("--prepared-llbc", type=Path)
    parser.add_argument("--certificate", type=Path, required=True)
    args = parser.parse_args()
    if args.source_root is not None and args.fixture is not None and args.llbc is None:
        evidence = prepare_source(args.source_root, args.fixture)
    elif (
        args.llbc is not None
        and args.prepared_llbc is not None
        and args.source_root is None
    ):
        source = json.loads(args.llbc.read_bytes())
        prepared, evidence = prepare_llbc(source)
        check_llbc(source, prepared, evidence)
        args.prepared_llbc.write_text(json.dumps(prepared))
    else:
        parser.error("select source preparation or LLBC preparation")
    args.certificate.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
