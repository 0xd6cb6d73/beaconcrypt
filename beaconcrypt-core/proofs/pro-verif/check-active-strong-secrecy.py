#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the separate bounded active strong-secrecy group, serially.

Every result concerns the stated symbolic process, with public Some/None bits,
under the inherited primitive idealizations and pending source abstractions.
The source adapters and computational plaintext oracle have separate obligations.
"""

import argparse
from datetime import datetime, timezone
from dataclasses import dataclass
import fcntl
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FS = load("fs_active_base", "check-free-schedule.py")
MODELS = load("fs_active_models", "active-strong-secrecy-models.py")
COMMON = """fun fs_strong_reply(bitstring, bitstring, bool): bitstring [data].
nounif x:bitstring, y:bitstring; attacker(choice[x25519_public(x),x25519_public(y)])."""
PARTNER = "free fs_strong_partner: channel [private]."
CONTROL_COMMON = """fun fs_strong_reply(bitstring, bitstring, bool): bitstring [data].
event FsStrongControlSecret(bitstring)."""
CONTROL_RESULT = "not (event(FsStrongControlSecret(m)) && attacker(m)) is false."


@dataclass(frozen=True)
class Target:
    name: str
    direction: str
    bound: int
    control: str = ""

    def libraries(self):
        shared = FS.COMMON_LOADER + (
            "fs-strong-control-common.pvl" if self.control else "fs-strong-common.pvl",
        )
        app = "sends" if self.direction == "b2s" else "taskings"
        app_file = (
            f"fs-strong-control-{self.direction}-{self.control}.pvl"
            if self.control
            else f"fs-strong-{self.direction}-{app}.pvl"
        )
        hooks = (
            (FS.B2S_WINDOW, FS.BINDING)
            if self.direction == "b2s"
            else ("fs-strong-s2b-interface.pvl", FS.WINDOW, FS.GATE)
        )
        return (
            shared
            + hooks
            + (
                app_file,
                f"fs-strong-{self.direction}-receive.pvl",
                f"fs-records-{self.direction}-kr{self.bound}.pvl",
                f"fs-strong-{self.direction}.pvl",
            )
        )

    @property
    def query(self):
        prefix = "control-" if self.control else ""
        return f"fs-strong-{prefix}{self.direction}.pv"

    @property
    def result(self):
        return CONTROL_RESULT if self.control else "Observational equivalence is true."

    @property
    def results(self):
        return (self.result,)

    def expected_traces(self):
        return int(bool(self.control))


# These bounds are independent of the older correspondence group's K_r=3.
# A larger scratch probe is not evidence for this maintained manifest.
TARGETS = tuple(
    Target(f"SS-{direction}", direction, 1) for direction in ("b2s", "s2b")
) + tuple(
    Target(f"SS-{direction}-{control}", direction, 1, control)
    for direction in ("b2s", "s2b")
    for control in ("leak", "ungated")
)


def same_tokens(directory, filename, expected):
    if FS.uncommented((directory / filename).read_text()) != FS.uncommented(expected):
        raise ValueError(f"{filename}: differs from the reviewed source derivative")


def check_derivatives(directory=HERE):
    same_tokens(directory, "fs-strong-common.pvl", COMMON)
    same_tokens(directory, "fs-strong-control-common.pvl", CONTROL_COMMON)
    same_tokens(directory, "fs-strong-s2b-interface.pvl", PARTNER)
    for direction in ("b2s", "s2b"):
        expected = getattr(MODELS, f"derive_{direction}")(directory)
        for name, text in expected.items():
            if name == "interface.pvl":
                continue
            suffix = (
                ".pvl"
                if name == f"{direction}.pvl"
                else ".pv" if name == "query.pv" else "-" + name
            )
            same_tokens(directory, f"fs-strong-{direction}{suffix}", text)
        if direction == "b2s":
            app = expected["sends.pvl"]
            app = (
                app.replace(
                    "  let record_1 = ",
                    "  new fs_strong_control_secret: bitstring;\n"
                    "  event FsStrongControlSecret(fs_strong_control_secret);\n"
                    "  let record_1 = ",
                    1,
                )
                .replace("choice[left_1, right_1]", "fs_strong_control_secret")
                .replace("choice[left_2, right_2]", "left_2")
            )
            leak = app.replace(
                "  event FsSent(", "  out(c, record_1);\n  event FsSent(", 1
            )
            old = "if server_identity = ed_public(SERVER_IDENTITY_SECRET) then fs_strong_control_secret else left_1"
            ungated = app.replace(old, "fs_strong_control_secret", 1)
        else:
            app = expected["taskings.pvl"]
            partner = "    in(fs_strong_partner,(=assigned_key_id,=root));\n"
            app = app.replace(
                partner,
                partner + "    new fs_strong_control_secret: bitstring;\n"
                "    event FsStrongControlSecret(fs_strong_control_secret);\n",
                1,
            ).replace("choice[left,right]", "fs_strong_control_secret")
            old = "  event FsSent(server_to_beacon(),server_identity,beacon_identity,assigned_key_id,root,2,tasking_2);"
            leak = app.replace(old, "  out(c, tasking_2);\n" + old, 1)
            ungated = app.replace(
                "    in(fs_strong_partner,(=assigned_key_id,=root));\n", "", 1
            )
        if leak == app or ungated == app:
            raise ValueError("negative-control mutation anchor changed")
        same_tokens(directory, f"fs-strong-control-{direction}-leak.pvl", leak)
        same_tokens(directory, f"fs-strong-control-{direction}-ungated.pvl", ungated)
        process = "FsRecordsB2sMainAnyPin" if direction == "b2s" else "FsRecordsS2bMain"
        same_tokens(
            directory,
            f"fs-strong-control-{direction}.pv",
            "query m: bitstring; event(FsStrongControlSecret(m)) && attacker(m).\n"
            f"process {process}()",
        )


def validate_targets(targets=TARGETS, directory=HERE):
    FS.validate_targets(directory=directory)
    check_derivatives(directory)
    if tuple(targets) != TARGETS:
        raise ValueError(
            "active strong-secrecy target roster, classification or bounds changed"
        )
    if {p.name for p in directory.glob("fs-strong-*.pv")} != {t.query for t in targets}:
        raise ValueError("active strong-secrecy query roster is incomplete")
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError(f"missing target input {name}")


def check_output(output, target):
    if target.control:
        FS.check_output(output, target)
        return
    for word in FS.FORBIDDEN:
        if word in output:
            raise ValueError(f"{target.name}: unproved or unconfirmed result: {word}")
    if re.search(r"^(Error|Warning)", output, re.M):
        raise ValueError(f"{target.name}: ProVerif error or warning")
    for line in output.splitlines():
        if "warning" in line.lower() and not line.startswith(FS.TERMINATION_WARNING):
            raise ValueError(f"{target.name}: unapproved warning")
    if output.count("Verification summary:") != 1:
        raise ValueError(f"{target.name}: missing or duplicated summary")
    primary, summary = output.split("Verification summary:")
    results = re.findall(r"^RESULT (.+)$", primary, re.M)
    reported = re.findall(
        r"^(?:Observational equivalence|Diff-equivalence|Query).*", summary, re.M
    )
    if results != [target.result] or reported != [target.result]:
        raise ValueError(f"{target.name}: exact equivalence verdict mismatch")
    if primary.count("A trace has been found.") != bool(target.control):
        raise ValueError(f"{target.name}: reconstructed trace count mismatch")


def run(args, targets, logdir):
    rows = []
    failures = []
    for target in targets:
        paths = [HERE / name for name in (*target.libraries(), target.query)]
        command = [args.proverif]
        for path in paths[:-1]:
            command += ["-lib", str(path)]
        command.append(str(paths[-1]))
        log = logdir / f"{target.name}.log"
        receipt = {
            "name": target.name,
            "class": "control" if target.control else "security",
            "direction": target.direction,
            "receive_attempts_per_peer": target.bound,
            "start": datetime.now(timezone.utc).isoformat(),
            "limits": {
                "seconds": args.timeout,
                "address_space_kib": args.address_space_kib,
            },
            "sources": {
                str(p.relative_to(HERE)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in paths
            },
        }
        seconds, peak, code, timed_out = FS.run_process(
            command, log, args.timeout, args.address_space_kib
        )
        receipt.update(
            seconds=seconds,
            peak_rss_kib=peak,
            exit=code,
            timed_out=timed_out,
            end=datetime.now(timezone.utc).isoformat(),
            log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
        )
        try:
            if any(
                hashlib.sha256(p.read_bytes()).hexdigest()
                != receipt["sources"][str(p.relative_to(HERE))]
                for p in paths
            ):
                raise ValueError(f"{target.name}: input changed during verification")
            if timed_out or code:
                raise ValueError(
                    f"{target.name}: verifier exit {code}, timeout={timed_out}"
                )
            check_output(log.read_text(), target)
            receipt["checked"] = True
            print(f"{target.name}: {target.result} ({seconds:.1f}s)", flush=True)
        except ValueError as error:
            receipt.update(checked=False, error=str(error))
            failures.append(str(error))
            print(str(error), file=sys.stderr, flush=True)
        rows.append(receipt)
        (logdir / "receipts.json").write_text(json.dumps(rows, indent=2) + "\n")
    if failures:
        raise ValueError("active strong-secrecy group failed: " + "; ".join(failures))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument("--target", action="append", choices=[t.name for t in TARGETS])
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    args = parser.parse_args()
    validate_targets()
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error("retain the approved 1800-second and 10-GiB per-target caps")
    if args.check_only:
        print(f"active strong-secrecy manifest: {len(TARGETS)} targets checked")
        return
    targets = [t for t in TARGETS if args.target is None or t.name in args.target]
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    with args.lock.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if args.log_dir:
            args.log_dir.mkdir(parents=True, exist_ok=True)
            run(args, targets, args.log_dir)
        else:
            with tempfile.TemporaryDirectory(
                prefix="beaconcrypt-active-strong-"
            ) as scratch:
                run(args, targets, Path(scratch))


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        print(f"active strong-secrecy check failed: {error}", file=sys.stderr)
        sys.exit(1)
