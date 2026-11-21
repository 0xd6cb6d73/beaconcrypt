#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Probe the actual registration codecs without installing incomplete output.

This is a fail-closed feasibility checkpoint, not a codec refinement theorem.
Every selected entry point keeps its complete reachable parser/serializer body;
only beaconcrypt-core is opaque, as in the existing ordinary-frame extraction.
The report and raw compiler logs remain in an isolated, newly created run tree.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile

from extract_frame_codec import (
    ROOT,
    RUSTFLAGS,
    TOOLS,
    VERSIONS,
    checked_lean,
    checked_template,
    code,
    configuration,
    isolated_work,
)

SUBDIRECTORY = "BeaconcryptCore/RegistrationCodecExtraction"
COHORTS = {
    "registration": (
        "decode_init",
        "decode_response",
        "encode_init",
        "encode_response",
    ),
    "parser": (
        "transport::validate_and_parse_initkex",
        "transport::validate_and_parse_kexresponse",
    ),
    "serializer": ("transport::serialize_initkex", "transport::serialize_kexresponse"),
}
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def snapshot(root: Path = ROOT) -> dict[str, str]:
    files = [
        root / "Cargo.toml",
        root / "Cargo.lock",
        root / "hax.toml",
        root / "beaconcrypt-parse/Cargo.toml",
        root / "beaconcrypt-core/Cargo.toml",
        root / "scripts/check_registration_codec_extraction.py",
        root / "scripts/extract_frame_codec.py",
        *(root / "beaconcrypt-parse/src").rglob("*.rs"),
        *(root / "beaconcrypt-core/src").rglob("*.rs"),
    ]
    return {
        p.relative_to(root).as_posix(): digest(p.read_bytes()) for p in sorted(files)
    }


def commands(
    tools: dict[str, Path], work: Path, cohort: str, all_errors: bool
) -> tuple[list[str], list[str]]:
    return (
        [
            str(tools["charon"]),
            "cargo",
            "--preset=aeneas",
            "--sysroot=default",
            *("--start-from=beaconcrypt_parse::" + name for name in COHORTS[cohort]),
            "--opaque=beaconcrypt_core",
            "--dest-file",
            str(work / "beaconcrypt_parse.llbc"),
            "--",
            "-p",
            "beaconcrypt-parse",
            "--lib",
            "--locked",
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
            *([] if all_errors else ["-abort-on-error"]),
            str(work / "beaconcrypt_parse.llbc"),
            "-dest",
            str(work / "generated"),
            "-subdir",
            SUBDIRECTORY,
        ],
    )


def checked_diagnostics(log: str) -> None:
    clean = ANSI.sub("", log)
    if re.search(
        r"\[\s*Error\s*\]|Could not translate the body|Ignoring the body", clean
    ):
        raise ValueError(
            "compiler rejected a reachable source body; inspect the raw log"
        )


def checked_output(generated: Path, cohort: str) -> dict[str, str]:
    """Absent bodies and unresolved external templates cannot pass the checkpoint."""
    result = {}
    for name in ("Types.lean", "Funs.lean"):
        contents = (generated / name).read_bytes()
        if not contents.strip():
            raise ValueError(f"empty generated output: {name}")
        checked_lean(contents, name)
        result[name] = digest(contents)
    functions = code((generated / "Funs.lean").read_bytes())
    for name in COHORTS[cohort]:
        lean_name = name.replace("::", ".")
        if (
            len(
                re.findall(
                    r"^def " + re.escape(lean_name) + r"\b", functions, re.MULTILINE
                )
            )
            != 1
        ):
            raise ValueError(f"missing or duplicate generated entry point: {name}")
    templates = sorted(generated.glob("*_Template.lean"))
    if not any(p.name == "FunsExternal_Template.lean" for p in templates):
        raise ValueError("missing external-signature template")
    for path in templates:
        contents = path.read_bytes()
        checked_template(contents)
        result[path.name] = digest(contents)
    return result


def run(
    work: Path, tools: dict[str, Path], cohort: str, timeout: int, all_errors: bool
) -> dict:
    before = snapshot()
    tool_hashes = {name: digest(path.read_bytes()) for name, path in tools.items()}
    report = {
        "status": "blocked",
        "cohort": cohort,
        "tools": TOOLS,
        "versions": VERSIONS,
        "tool_sha256": tool_hashes,
        "source_sha256": before,
        "rust_start_from": ["beaconcrypt_parse::" + name for name in COHORTS[cohort]],
        "generated_transformation": None,
        "charon_sysroot": "default",
        "rustflags": RUSTFLAGS,
        "lean_namespace": "beaconcrypt_parse",
        "commands": [],
        "source_correspondence_proved": False,
    }
    environment = dict(os.environ)
    environment.pop("CARGO_ENCODED_RUSTFLAGS", None)
    environment.update(
        CARGO_TARGET_DIR=str(work / "target"), CARGO_BUILD_JOBS="2", RUSTFLAGS=RUSTFLAGS
    )
    (work / "generated" / SUBDIRECTORY).mkdir(parents=True)
    try:
        for name, command in zip(
            ("charon", "aeneas"), commands(tools, work, cohort, all_errors)
        ):
            entry = {"tool": name, "argv": command}
            report["commands"].append(entry)
            with (work / (name + ".log")).open("w") as output:
                output.write("Command: " + repr(command) + "\n")
                output.flush()
                try:
                    process = subprocess.Popen(
                        command,
                        cwd=ROOT,
                        env=environment,
                        stdout=output,
                        stderr=output,
                        start_new_session=True,
                    )
                    returncode = process.wait(timeout=timeout)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                    entry["timeout_seconds"] = timeout
                    raise ValueError(
                        f"{name} exceeded the {timeout}s checkpoint timeout"
                    ) from None
            entry["returncode"] = returncode
            entry["log_sha256"] = digest((work / (name + ".log")).read_bytes())
            if returncode:
                raise ValueError(
                    f"{name} exited {returncode}; inspect {work / (name + '.log')}"
                )
            checked_diagnostics((work / (name + ".log")).read_text())
            llbc = work / "beaconcrypt_parse.llbc"
            if not llbc.is_file() or not llbc.stat().st_size:
                raise ValueError("compiler returned without fresh nonempty LLBC")
            report["llbc_sha256"] = digest(llbc.read_bytes())
        report["generated_sha256"] = checked_output(
            work / "generated" / SUBDIRECTORY, cohort
        )
        report["status"] = "extracted-without-external-obligations"
    except (OSError, ValueError) as error:
        report["error"] = str(error)
    if before != snapshot() or tool_hashes != {
        name: digest(path.read_bytes()) for name, path in tools.items()
    }:
        report.update(
            status="blocked", error="extraction inputs changed during the checkpoint"
        )
    (work / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--cohort", choices=COHORTS, default="registration")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--all-errors", action="store_true")
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
        configuration()
        directory = isolated_work(args.work_dir)
        directory.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix=args.cohort + "-", dir=directory))
        tools = {
            name: args.tools_root / name / version / name
            for name, version in TOOLS.items()
        }
        for path in tools.values():
            if not path.is_file() or not os.access(path, os.X_OK):
                raise ValueError(f"missing pinned executable: {path}")
        report = run(work, tools, args.cohort, args.timeout, args.all_errors)
        print(
            f"Registration codec checkpoint: {report['status']}; evidence: {work / 'report.json'}"
        )
        if "error" in report:
            print(report["error"], file=sys.stderr)
        return int(report["status"] == "blocked")
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
