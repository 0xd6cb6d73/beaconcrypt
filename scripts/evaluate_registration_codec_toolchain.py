#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Evaluate named candidate codec tools without changing the pinned checkpoint.

This never installs generated output and cannot certify source correspondence.
The candidate executable hashes identify the exact locally reviewed x86_64
tools, rather than accepting arbitrary tools under a version-shaped directory.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

import check_registration_codec_extraction as checkpoint

CANDIDATE = "hax-6d284c4"
CUSTOM = "aeneas-41977a5-nojoins"
RECOVER = "aeneas-41977a5-recoverjoins"
MIR_PIPELINES = {
    "default": (),
    "optimized": (
        "--mir=optimized",
        "--rustc-arg=-Zmir-opt-level=4",
        "--rustc-arg=-Copt-level=3",
    ),
    "inlined": (
        "--mir=optimized",
        "--rustc-arg=-Zmir-opt-level=4",
        "--rustc-arg=-Copt-level=3",
        "--rustc-arg=-Zinline-mir=yes",
        "--rustc-arg=-Zinline-mir-threshold=10000",
        "--rustc-arg=-Zinline-mir-hint-threshold=10000",
        "--rustc-arg=-Zinline-mir-forwarder-threshold=10000",
    ),
    "inlined-std-models": (
        "--mir=optimized",
        "--rustc-arg=-Zmir-opt-level=4",
        "--rustc-arg=-Copt-level=3",
        "--rustc-arg=-Zinline-mir=yes",
        "--rustc-arg=-Zinline-mir-threshold=10000",
        "--rustc-arg=-Zinline-mir-hint-threshold=0",
        "--rustc-arg=-Zinline-mir-forwarder-threshold=0",
    ),
}
TOOLS = {"charon": "nightly-2026.10.17", "aeneas": "build-41977a5"}
VERSIONS = {
    "lean": "leanprover/lean4:v4.35.0",
    "hax-lean-lib": "410c796d60d92d5acae0ba13c9ecbb550dac208b",
}
SOURCE_COMMITS = {
    "hax": "6d284c4f06d17b1a60f2e066644240be8a2f7ed2",
    "aeneas": "41977a5c4d200838c3db2997e962f2e2d079ab68",
    "charon_release": "nightly-2026.10.17",
}
HASHES = {
    "charon": "a28d8689627a1e1dfa87dd65df56b58ff449512faa37699b2f8e0f7527183849",
    "charon-driver": "1e78719acdeb3cea9aa3c32769c72da934a04e6e5112e7a16457862d6c5446b1",
    "rust-toolchain": "60d242314032dfb524f52d9c31397a64dcf6697cdb20a08c29c004fef4059306",
    "aeneas": "9a749237af19788cea712f088dceace5492df13ea3ce00f286bc33216131e364",
}
CUSTOM_HASH = "708230686973004108bf572c0f645dc1cb193d2868ccb53ddec3934b0cf9382d"
CUSTOM_SOURCE_HASH = "0528089d49e0a9b6f767f6788baf91daca5aa346c6bb32d8fb622220b7c99e7b"
RECOVER_HASH = "fbc24f8bf3bf7d1873ce50baa6ca63cdca5641f5832ab18664d71d9dffcaadf8"
RECOVER_SOURCE_HASH = "83a942243ece1b0faa883c40ad821e758def685ac26182ab23ff34c58592931b"
CUSTOM_PATCH = {
    "source_commit": SOURCE_COMMITS["aeneas"],
    "file": "src/interp/InterpStatements.ml",
    "before_sha256": "26bf8b08730b391f98d775fd3fb8309fd5784fd51fddfc79951a1326cd41040c",
    "after_sha256": "20a8479b93e2855de48929bc9d3abd0fe05376cd9f718ced71a38ef4f9e7565e",
    "replacement": ["if join then", "if false && join then"],
    "occurrences": 3,
    "flake_after_sha256": "3606bc167d1710c2f97d9251af7df8e59ac9aac6e506d4407c511ae16f269843",
    "flake_change": "Remove only the postInstall Charon symlink to avoid rebuilding the Rust tool; use the separately checked Charon executable.",
    "nix_derivation": "ndznqv9ai1gqqvv9qivn667rp4wnidgc-ocaml5.2.1-aeneas-0.1.0.drv",
    "nix_output": "/nix/store/ifi8n86wh62vpjvi62nnm7h2s793addg-ocaml5.2.1-aeneas-0.1.0",
}
RECOVER_PATCH = {
    "source_commit": SOURCE_COMMITS["aeneas"],
    "change": "Propagate the existing recoverable flag through nested-borrow destructuring and context matching. Required joins retain their errors; an optional failed switch join uses the existing full-branch duplication path.",
    "patches": [
        {
            "file": "src/interp/InterpBorrows.ml",
            "before_sha256": "41fe2d959370354e5187007eb358088883a196ebc44f6635511f215dba332a7a",
            "after_sha256": "0bd83d3948e3614eabd436a2a06f994d6e3caf587dd340fb809a4d07334129fa",
        },
        {
            "file": "src/interp/InterpJoin.ml",
            "before_sha256": "57c5478aae42f8a354755424b67f67f37dc8bd233d653c97de0dcbbea5dd6229",
            "after_sha256": "d943f2358d8cf015f2fae7ec4f4172f303c658f2fe608a842c5fe30dcc4308c5",
        },
        {
            "file": "src/interp/InterpBorrows.mli",
            "before_sha256": "bec35be5ccd34bc596d23deaa4f1f4b93358759a385e9f55bef794c26d8ebcba",
            "after_sha256": "f3ba1cec24107efca97d7e92e6f74af32ec6b687f39872b50895ffacacbd80a3",
        },
    ],
    "flake_after_sha256": CUSTOM_PATCH["flake_after_sha256"],
    "flake_change": CUSTOM_PATCH["flake_change"],
    "nix_derivation": "9wdv73szrrjddi5gfng92ylvfs31i3ad-ocaml5.2.1-aeneas-0.1.0.drv",
    "nix_output": "/nix/store/0rn8wkbz1ycslc0hwkmnm4asc7jvv2a8-ocaml5.2.1-aeneas-0.1.0",
}


def checked_hash(path: Path, expected: str) -> str:
    value = checkpoint.digest(path.read_bytes())
    if value != expected:
        raise ValueError(f"candidate identity mismatch: {path}")
    return value


def source_hash(root: Path) -> str:
    """Hash the complete Nix build source and its unchanged dependency lock."""
    paths = [root / "flake.nix", root / "flake.lock", *(root / "src").rglob("*")]
    if not (root / "src").is_dir() or (root / "src").is_symlink():
        raise ValueError("candidate source must contain a real src tree")
    for path in paths:
        if path.is_symlink() and (
            path.relative_to(root).as_posix() != "src/charon"
            or path.readlink() != Path("../charon")
        ):
            raise ValueError("candidate source has an unreviewed symlink")
    hashes = {
        p.relative_to(root).as_posix(): (
            "symlink:" + str(p.readlink())
            if p.is_symlink()
            else checkpoint.digest(p.read_bytes())
        )
        for p in sorted(paths)
        if p.is_file() or p.is_symlink()
    }
    return checkpoint.digest(
        json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode()
    )


def candidate_tools(
    mode: str, tools_root: Path, custom_aeneas: Path | None, custom_source: Path | None
) -> tuple[dict[str, Path], dict]:
    custom_mode = mode in (CUSTOM, RECOVER)
    if mode not in (CANDIDATE, CUSTOM, RECOVER):
        raise ValueError("unknown candidate toolchain")
    if mode == CANDIDATE and (custom_aeneas is not None or custom_source is not None):
        raise ValueError("custom paths require the explicitly custom candidate mode")
    if custom_mode and (custom_aeneas is None or custom_source is None):
        raise ValueError("the custom candidate requires both executable and source")
    tools = {
        name: tools_root / name / version / name for name, version in TOOLS.items()
    }
    if custom_mode:
        tools["aeneas"] = custom_aeneas
    paths = {
        "charon": tools["charon"],
        "charon-driver": tools["charon"].parent / "charon-driver",
        "rust-toolchain": tools["charon"].parent / "rust-toolchain",
        "aeneas": tools["aeneas"],
    }
    hashes = {
        name: checked_hash(
            path,
            (
                (CUSTOM_HASH if mode == CUSTOM else RECOVER_HASH)
                if custom_mode and name == "aeneas"
                else HASHES[name]
            ),
        )
        for name, path in paths.items()
    }
    for name in ("charon", "charon-driver", "aeneas"):
        if not os.access(paths[name], os.X_OK):
            raise ValueError(f"candidate tool is not executable: {paths[name]}")
    provenance = {"mode": mode, "source_identities": SOURCE_COMMITS, "sha256": hashes}
    if custom_mode:
        actual = source_hash(custom_source)
        if actual != (CUSTOM_SOURCE_HASH if mode == CUSTOM else RECOVER_SOURCE_HASH):
            raise ValueError(
                "custom candidate source differs from the reviewed exact patch"
            )
        provenance.update(
            source_tree_sha256=actual,
            exact_patch=CUSTOM_PATCH if mode == CUSTOM else RECOVER_PATCH,
        )
    return tools, provenance


def label_report(report: dict, provenance: dict) -> None:
    report.update(
        evaluation_only=True,
        current_pin_acceptance=False,
        candidate_provenance=provenance,
        source_correspondence_proved=False,
        installs_output=False,
    )
    if report["status"] != "blocked":
        report["status"] = "candidate-extraction-without-external-obligations"


def pipeline_commands(
    commands: tuple[list[str], list[str]], mode: str
) -> tuple[list[str], list[str]]:
    if mode not in MIR_PIPELINES:
        raise ValueError("unknown candidate MIR pipeline")
    charon, aeneas = commands
    return [*charon[:2], *MIR_PIPELINES[mode], *charon[2:]], list(aeneas)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--candidate", required=True, choices=(CANDIDATE, CUSTOM, RECOVER)
    )
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--cohort", choices=checkpoint.COHORTS, default="registration")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--all-errors", action="store_true")
    parser.add_argument("--mir-pipeline", choices=MIR_PIPELINES, default="default")
    parser.add_argument("--custom-aeneas", type=Path)
    parser.add_argument("--custom-source", type=Path)
    parser.add_argument(
        "--tools-root",
        type=Path,
        default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
        / "hax/tools",
    )
    args = parser.parse_args()
    try:
        if args.timeout <= 0:
            raise ValueError("--timeout must be positive")
        checkpoint.configuration()
        tools, provenance = candidate_tools(
            args.candidate, args.tools_root, args.custom_aeneas, args.custom_source
        )
        own_path = Path(__file__).resolve()
        own_hash = checkpoint.digest(own_path.read_bytes())
        directory = checkpoint.isolated_work(args.work_dir)
        directory.mkdir(parents=True, exist_ok=True)
        work = Path(
            tempfile.mkdtemp(
                prefix=args.candidate + "-" + args.cohort + "-", dir=directory
            )
        )
        unfinished = {
            "status": "blocked",
            "error": "candidate probe has not completed",
            "source_sha256": checkpoint.snapshot(),
        }
        pipeline_metadata = {
            "mir_pipeline": args.mir_pipeline,
            "mir_flags": list(MIR_PIPELINES[args.mir_pipeline]),
        }
        label_report(
            unfinished,
            {**provenance, **pipeline_metadata, "evaluator_sha256": own_hash},
        )
        (work / "report.json").write_text(
            json.dumps(unfinished, indent=2, sort_keys=True) + "\n"
        )
        # This process invokes only the candidate evaluator; the pinned command
        # and its configuration/defaults are never changed on disk.
        previous_tools, previous_versions = checkpoint.TOOLS, checkpoint.VERSIONS
        previous_commands = checkpoint.commands
        try:
            checkpoint.TOOLS, checkpoint.VERSIONS = dict(TOOLS), dict(VERSIONS)
            if args.candidate != CANDIDATE:
                checkpoint.TOOLS["aeneas"] = args.candidate

            def commands(tools, directory, cohort, all_errors):
                return pipeline_commands(
                    previous_commands(tools, directory, cohort, all_errors),
                    args.mir_pipeline,
                )

            checkpoint.commands = commands
            report = checkpoint.run(
                work, tools, args.cohort, args.timeout, args.all_errors
            )
        finally:
            checkpoint.TOOLS, checkpoint.VERSIONS = previous_tools, previous_versions
            checkpoint.commands = previous_commands
        try:
            _, after = candidate_tools(
                args.candidate, args.tools_root, args.custom_aeneas, args.custom_source
            )
            if (
                after != provenance
                or checkpoint.digest(own_path.read_bytes()) != own_hash
            ):
                raise ValueError(
                    "candidate evaluator inputs changed during the checkpoint"
                )
        except (OSError, ValueError) as error:
            report.update(status="blocked", error=str(error))
        provenance["evaluator_sha256"] = own_hash
        provenance.update(pipeline_metadata)
        label_report(report, provenance)
        (work / "report.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n"
        )
        print(
            f"Candidate-only codec checkpoint: {report['status']}; evidence: {work / 'report.json'}"
        )
        if "error" in report:
            print(report["error"], file=sys.stderr)
        return int(report["status"] == "blocked")
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
