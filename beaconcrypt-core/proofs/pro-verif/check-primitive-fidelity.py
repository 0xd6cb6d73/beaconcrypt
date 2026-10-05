#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the separate bounded primitive-fidelity group (symbolic results only).

The encoding profile retains role-asymmetric DH and the existing ML-KEM binding
idealisation. It is not a replacement for the three-step legacy fs registration
claims. Limits are the separately approved 1800 seconds and 10 GiB per target.
"""

import argparse
from dataclasses import dataclass
import importlib.util
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "fs_primitive_base", HERE / "check-free-schedule.py"
)
FS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FS)
ENCODING = "fs-encoding"
THEORY_START = "fun x25519_public(bitstring): bitstring."
THEORY_END = "fun registration_identifier(bitstring, bitstring): bitstring [data]."
SERVER_GATE = "if fs_dh_nonzero(dh1, dh2, dh3, dh4) then"
ZERO_BRANCH = """else (
  event FsServerZeroRejected(obj, server_identity, identity, registration_id);
  event FsServerAcceptFailed(obj, server_identity, identity, registration_id);
  Next(obj, kid_next, slot_1, slot_2)
)"""
ZERO_RETRY = FS.R5.replace("FsServerAcceptFailed", "FsServerZeroRejected")


@dataclass(frozen=True)
class EncodingTarget(FS.Target):
    def libraries(self):
        return (
            (
                "production-transcript-interface.pvl",
                "crypto-fs-encoding.pvl",
                "extraction/lib.pvl",
                "fs-common.pvl",
                "fs-encoding-interface.pvl",
            )
            + self.hooks
            + (
                "fs-encoding-registration.pvl",
                f"fs-registration-k{self.bound}.pvl",
            )
        )


def encoding(name, cls, query, result, consumed=FS.CONSUMED, binding=FS.BINDING):
    return EncodingTarget(
        name, ENCODING, cls, 2, (consumed, binding), query, tuple(result)
    )


TARGETS = tuple(
    encoding(
        f"encoding-{target.name}",
        target.cls,
        target.query,
        target.results,
        *target.hooks,
    )
    for target in FS.TARGETS
    if target.scenario == FS.REGISTRATION
    and target.name in ("A1", "A2", "R1", "R1'", "R3", "W1", "R5", "C-NOCHECK")
) + (
    encoding(
        "encoding-ZERO-RETRY",
        "witness",
        "fs-encoding-zero-retry.pv",
        (ZERO_RETRY + " is false.",),
    ),
)


def exactly_once(text, old, new, label):
    if text.count(old) != 1:
        raise ValueError(f"{label}: expected exactly one anchor")
    return text.replace(old, new)


def check_derivative(directory=HERE):
    """Check every process token outside the two gates and one failure branch.

    The checked derivative is maintained and reviewable, not rewritten per query.
    Existing queries, consumed-set, binding and bound files are loaded directly.
    """
    compact = FS.uncommented
    source = compact((directory / "fs-registration.pvl").read_text())
    derived = compact((directory / "fs-encoding-registration.pvl").read_text())
    expected = exactly_once(
        source,
        ") in ( let root = pqxdh_root(",
        ") in " + SERVER_GATE + " ( let root = pqxdh_root(",
        "server DH/root boundary",
    )
    failure = (
        "else ( event FsServerAcceptFailed(obj, server_identity, identity, registration_id); "
        "Next(obj, kid_next, slot_1, slot_2) )"
    )
    expected = exactly_once(
        expected,
        failure,
        compact(ZERO_BRANCH) + " " + failure,
        "server refusal boundary",
    )
    beacon_dh = (
        "let dh4 = x25519_beacon_dh(beacon_one_time_secret, server_ephemeral) in"
    )
    expected = exactly_once(
        expected, beacon_dh, beacon_dh + " " + SERVER_GATE, "beacon DH/root boundary"
    )
    if derived != expected:
        raise ValueError(
            "encoding process differs outside the reviewed gate insertions"
        )
    real = compact((directory / "crypto.pvl").read_text())
    theory = compact((directory / "crypto-fs-encoding.pvl").read_text())
    for text in (real, theory):
        for marker in (THEORY_START, THEORY_END):
            if text.count(marker) != 1:
                raise ValueError("primitive theory section boundary changed")
    if real.split(THEORY_START)[0] != theory.split(THEORY_START)[0]:
        raise ValueError("encoding theory changed the Ed25519/prefix interface")
    if real.split(THEORY_END)[1] != theory.split(THEORY_END)[1]:
        raise ValueError("encoding theory changed the KDF/AEAD/CTX suffix interface")


def check_source_boundary(directory=HERE):
    root = directory.parents[2]
    source = (root / "beaconcrypt-core/src/pqxdh.rs").read_text()
    start = source.index("pub fn build_root_key_input(")
    body = source[start : source.index("let bytes:", start)]
    expected = """if is_all_zero(&secrets.dh1)
        || is_all_zero(&secrets.dh2)
        || is_all_zero(&secrets.dh3)
        || is_all_zero(&secrets.dh4)
        { return Err(RegistrationError::InvalidDhOutput); }"""
    if " ".join(expected.split()) not in " ".join(body.split()):
        raise ValueError("Rust four-DH rejection before root construction changed")
    interface = FS.uncommented((directory / "fs-encoding-interface.pvl").read_text())
    predicate = """letfun fs_dh_nonzero(dh1: bitstring, dh2: bitstring, dh3: bitstring, dh4: bitstring) =
      dh1 <> x25519_all_zero && dh2 <> x25519_all_zero && dh3 <> x25519_all_zero && dh4 <> x25519_all_zero."""
    if interface.count(FS.uncommented(predicate)) != 1:
        raise ValueError("symbolic four-DH rejection changed")


def validate_targets(targets=TARGETS, directory=HERE):
    FS.validate_targets(directory=directory)
    check_derivative(directory)
    check_source_boundary(directory)
    if len({t.name for t in targets}) != len(targets):
        raise ValueError("duplicate primitive target name")
    if len({FS.log_name(t) for t in targets}) != len(targets):
        raise ValueError("duplicate primitive log path")
    used_new = set()
    for target in targets:
        if target.scenario != ENCODING or target.bound != 2:
            raise ValueError("encoding targets have exactly K_reg = 2")
        if target.cls not in FS.CLASSES or target.inverted or target.failstop:
            raise ValueError("unsupported encoding target classification")
        if target.hooks not in ((FS.CONSUMED, FS.BINDING), (FS.NOCHECK, FS.BINDING)):
            raise ValueError("unsupported encoding hook")
        if (target.cls == "control") != (target.hooks[0] == FS.NOCHECK):
            raise ValueError("only the declared control may change consumed admission")
        for filename in (*target.libraries(), target.query):
            if not (directory / filename).is_file():
                raise ValueError(f"missing primitive target input {filename}")
        if not target.results or (
            target.results[0].endswith(" is true.") != target.expected_true()
        ):
            raise ValueError("primitive target class/verdict mismatch")
        if target.query.startswith("fs-encoding-"):
            used_new.add(target.query)
        elif target.query not in {
            t.query for t in FS.TARGETS if t.scenario == FS.REGISTRATION
        }:
            raise ValueError("encoding target must reuse a registration query")
    if used_new != {p.name for p in directory.glob("fs-encoding-*.pv")}:
        raise ValueError("encoding query roster is incomplete")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--results", type=Path)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument("--target", action="append", choices=[t.name for t in TARGETS])
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    validate_targets()
    if args.check_only:
        print(f"primitive-fidelity manifest: {len(TARGETS)} targets checked")
        return
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error("the primitive group must retain the approved per-target caps")
    targets = [t for t in TARGETS if args.target is None or t.name in args.target]
    FS.run_logged(
        args.proverif,
        targets,
        args.log_dir,
        args.timeout,
        args.address_space_kib,
        args.results,
    )


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        print(f"primitive-fidelity check failed: {error}", file=sys.stderr)
        sys.exit(1)
