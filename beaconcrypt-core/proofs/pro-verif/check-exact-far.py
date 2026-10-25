#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check literal first-far HKDF material for the bounded hidden-reply projection.

The five targets supplement the unchanged fs group. The reviewed trace argument,
not this generator, connects the one-attempt C4 results to longer hidden-reply
traces. The finite cases follow the source cache bound and exact chain relation.
"""

import argparse
from dataclasses import dataclass, replace
from datetime import datetime, timezone
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
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


FS = load("exact_far_fs", "check-free-schedule.py")
PINS = load("exact_far_pins", "pin-origin-theory.py")
DECLARATION = "fun fs_far_chain(bitstring, nat): bitstring."
PUBLIC_CHAIN = "pqxdh_ff32_padding()"


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    base: str
    query: str
    results: tuple[str, ...]
    public_chain: bool = False

    @property
    def direction(self):
        return self.base.split("-", 1)[0]

    def fs_target(self):
        original = next(t for t in FS.TARGETS if t.name == self.base)
        return replace(original, bound=1, failstop=False, query=self.query)

    def libraries(self):
        return self.fs_target().libraries()

    def expected_traces(self):
        return int(self.cls in ("witness", "negative-control"))


TARGETS = (
    Target(
        "far-b2s-C4",
        "security",
        "b2s-C4",
        "exact-far-b2s-c4.pv",
        (FS.B2S_C4 + " is true.",),
    ),
    Target(
        "far-s2b-C4",
        "security",
        "s2b-C4",
        "exact-far-s2b-c4.pv",
        (FS.S2B_C4 + " is true.",),
    ),
    Target(
        "far-b2s-C-public",
        "negative-control",
        "b2s-C4",
        "exact-far-b2s-control.pv",
        (
            "not (event(FsFarAccepted(beacon_to_server,s,ed_public(k),kid,root_2,t)) && event(FsBeaconStarted(s2,ed_public(k),init_2,rid))) is false.",
        ),
        True,
    ),
    Target(
        "far-s2b-C-public",
        "negative-control",
        "s2b-C4",
        "exact-far-s2b-control.pv",
        (FS.S2B_C4 + " is false.",),
        True,
    ),
    Target(
        "far-b2s-owned",
        "witness",
        "b2s-FAR",
        "exact-far-b2s-witness.pv",
        (FS.B2S_FAR + " is false.",),
    ),
)

TOKEN_SHA256 = {
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "exact-far-b2s-c4.pv": "63452b141ebcef84e3b209666752b4b10569b986f8640f41bdeadf5042544846",
    "exact-far-b2s-control.pv": "8faff51d67972a3cc332ff4434468236c3e0d5e8fa5d15511e044c1e6d49c2c3",
    "exact-far-b2s-witness.pv": "e10097789d8b47d1f34b317386495c255cab00853301f0a536009e1590654867",
    "exact-far-s2b-c4.pv": "d67011809ae315532c2b341ff1c70d2c5df60b4f1538fcc253cc0a5f751eb3b5",
    "exact-far-s2b-control.pv": "d67011809ae315532c2b341ff1c70d2c5df60b4f1538fcc253cc0a5f751eb3b5",
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
    "fs-records-b2s-kr1.pvl": "d7bd28eedf72bcaf6a9cc458c85eb51994359d7ee56cc3ef6acd9765c52919d1",
    "fs-records-b2s-receive.pvl": "804737cf522cf20cb7f68f50f7680ba99357c87581e3d1f47f44ccb2cd6224d0",
    "fs-records-b2s-sends-chosen.pvl": "2c89ae654ea2a0ddf186a3538ae03688d707193661376bdd02e3daa8f0fb99aa",
    "fs-records-b2s-sends.pvl": "bdab11d7acec74c06cec4acf91cc0645f1d098a75725b2563cdc105cbf372a98",
    "fs-records-b2s-window.pvl": "b67656982edb0f39a44efa3c1697727004979ae6d110aee3c54ebde8af222fd5",
    "fs-records-b2s.pvl": "7fc2a35fefe9cfa0aa0e93a641b73523e8d1d2345baa55edf717772ad1bdaf3a",
    "fs-records-s2b-gate.pvl": "51fe23b53f5eba28e6ac20803a65470a45b8d73213f3fca458cd38a93d87c6ca",
    "fs-records-s2b-kr1.pvl": "9dee616a3940952f128bf539d3af7440a4a8ec1de0c6907218f4d3ed24bd9502",
    "fs-records-s2b-receive.pvl": "a83895f5cc1c2dd143c3726d53eb17119d005ba7755cda2ccb7f6237d3b97bce",
    "fs-records-s2b-taskings-chosen.pvl": "a5067f8ef8951a4cef7b2905ae3e723141decce3e63b38a7a918b6f46f98d906",
    "fs-records-s2b-window.pvl": "d2afce0c953ed7baec3108346bbd403ae92ea9d36b85c6fddb4bbe87e4aa5549",
    "fs-records-s2b.pvl": "cdadbc31c34fbe7bc6b592bdcd21f88427c420af0586e036aad80f171ffd4e22",
    "fs-registration-binding.pvl": "50b006405e0a98006e2f1ebabe854b466569beed15b7338d656557bf573a679c",
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
}
# Reviewed classical projection of the ML-DSA source; see doc/impl/mldsa-source-pins.md.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt-core/src/ratchet/control.rs": "6c17cc0dbe7445be04dc3ab123a60ecbf3d757da6337a7132d5dafd3e06f5639",
    "beaconcrypt-core/src/ratchet/concrete.rs": "c9f907f20f23ac2851792ff6eef77565a843e61ff266d21617411100e12e431d",
    "beaconcrypt-core/src/ratchet/refined.rs": "ce940e42b1e95bc841121ba80107ce74757fea4f4fcbd771834b93e28cdb459f",
    "beaconcrypt/src/ratchet.rs": "7aa3675eb4f340523da263b26294af9d10e060c2ded34226d0789aaa7c9c7ce4",
    "beaconcrypt/src/beacon.rs": "28fdde51b14eb4c7d44552dd5828cb036b4ad845a0434d9b5dfb84a628d43734",
    "beaconcrypt/src/server.rs": "fe723eba1b1f8b84c37a1272a9326b93d6a5d987b2b6288df47bbf1e1e302bc3",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RatchetControl.lean": "467e40094bfde41c7ebeed24761788c263d5ba12e21d3dfd86e981917b60565c",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RatchetRefinement.lean": "813d26cedc7a82a9c19f795fdc8599809aac8d0626608000a626a2986be2c915",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RatchetFuturePublication.lean": "b87aff9e49e929786c8e7a158e6e470d84a4f07f9fbbe9b5e65837a4065162f8",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RatchetReceiveAdmission.lean": "a54ed0972451e2075b91e792b154e5615e99bf3934e656d8a5c21d2dd78b2794",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Model/Ratchet.lean": "e9bb9592009c51a1e9246de3ec86abf66c9784901b90e3d2ff3ac2f8732c5522",
    "beaconcrypt-core/src/session.rs": "3779c778ce4f8ec534c2fa610c0a334302ada76fc5cd601ade575802ff9c07c4",
    "beaconcrypt/src/auth.rs": "e4119ce56650add757b83144f728aabc84904219e4f3fc3678fdce7028ebca29",
    "beaconcrypt/src/pqxdh.rs": "4d786bf9f42a8f05204bc871f987f2b93440238672120af16c02f6837b11c52d",
    "beaconcrypt-core/src/agreement.rs": "cd4f62dab7d18c9237ad7ce46480ae76faf8e9983b97a9f7af34473550acbabb",
    "beaconcrypt-core/src/registration.rs": "a27884eb8e09752c84f997472652ad54362444d99bf4c104caef0367dbe49f1d",
    "beaconcrypt-core/src/pqxdh.rs": "bff5dca4b9a292a025ad96ab9fba8761bc63d2e49dac493a2bae0d1cea67a018"
}


def first_far(direction):
    if direction not in ("b2s", "s2b"):
        raise ValueError("unknown far direction")
    return 3 if direction == "b2s" else 4


def family(direction, public_chain=False):
    start = first_far(direction)
    chain = "anchor"
    rules = []
    for sequence in range(start, start + 51):
        keyword = "reduc" if sequence == start else "otherwise"
        rhs = PUBLIC_CHAIN if public_chain else chain
        rules.append(
            f"{keyword} forall anchor: bitstring; fs_far_chain(anchor, {sequence}) = {rhs}"
        )
        chain = (
            f"hkdf_second_32(hkdf_sha512_no_salt({chain}, symmetric_ratchet_domain()))"
        )
    return "fun fs_far_chain(bitstring, nat): bitstring\n" + "\n".join(rules) + "."


def check_family(text, direction, public_chain=False):
    """Independently parse every case, then peel its exact public recipe."""
    start = first_far(direction)
    header = "fun fs_far_chain(bitstring, nat): bitstring\n"
    if not text.startswith(header) or not text.endswith("."):
        raise ValueError("far declaration changed")
    lines = text[len(header) : -1].splitlines()
    if len(lines) != 51:
        raise ValueError("far family must contain exactly 51 cases")
    for offset, line in enumerate(lines):
        matched = re.fullmatch(
            r"(reduc|otherwise) forall anchor: bitstring; fs_far_chain\(anchor, ([0-9]+)\) = (.+)",
            line,
        )
        if not matched:
            raise ValueError("malformed far case")
        keyword, sequence, term = matched.groups()
        if (
            keyword != ("reduc" if offset == 0 else "otherwise")
            or int(sequence) != start + offset
        ):
            raise ValueError("far cases reordered, missing or duplicated")
        if public_chain:
            if term != PUBLIC_CHAIN:
                raise ValueError("public-chain control changed")
        else:
            prefix = "hkdf_second_32(hkdf_sha512_no_salt("
            suffix = ", symmetric_ratchet_domain()))"
            depth = 0
            while term.startswith(prefix) and term.endswith(suffix):
                term = term[len(prefix) : -len(suffix)]
                depth += 1
            if term != "anchor" or depth != int(sequence) - start:
                raise ValueError(
                    "far key recipe, projection or zero-step anchor changed"
                )


def receive_model(source, direction, public_chain=False):
    if source.count(DECLARATION) != 1:
        raise ValueError("original far declaration changed")
    replacement = family(direction, public_chain)
    check_family(replacement, direction, public_chain)
    return source.replace(DECLARATION, replacement)


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    FS.validate_legacy_scope(directory)
    if tuple(targets) != TARGETS:
        raise ValueError("exact-far roster, classes, controls or formulas changed")
    if {p.name for p in directory.glob("exact-far-*.pv")} != {t.query for t in targets}:
        raise ValueError("exact-far query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if PINS.digest((directory / filename).read_text()) != wanted:
            raise ValueError("review changed exact-far input: " + filename)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError("review changed far source/refinement: " + filename)
    for target in targets:
        name = f"fs-records-{target.direction}-receive.pvl"
        source = (directory / name).read_text()
        receive_model(source, target.direction, target.public_chain)
        for filename in (*target.libraries(), target.query):
            if filename not in TOKEN_SHA256:
                raise ValueError("unreviewed exact-far dependency: " + filename)


def prepare(target, output, directory=HERE):
    paths = []
    for name in (*target.libraries(), target.query):
        destination = output / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        data = (directory / name).read_bytes()
        if name == f"fs-records-{target.direction}-receive.pvl":
            data = receive_model(
                data.decode(), target.direction, target.public_chain
            ).encode()
        destination.write_bytes(data)
        paths.append(destination)
    return paths


def check_output(output, target):
    FS.check_output(output, target)
    if "I could not confirm" in output:
        raise ValueError("unconfirmed exact-far trace")
    if re.findall(r"^RESULT (.+)$", output, re.M) != list(target.results):
        raise ValueError("extra exact-far result outside primary output")
    if output.count("A trace has been found.") != target.expected_traces():
        raise ValueError("extra exact-far trace outside primary output")


def run(args, logdir):
    rows, failures = [], []
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    for target in TARGETS:
        with args.lock.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            paths = prepare(target, logdir / (target.name + "-inputs"))
            command = [args.proverif]
            for path in paths[:-1]:
                command += ["-lib", str(path)]
            command.append(str(paths[-1]))
            before = {
                str(p.relative_to(paths[-1].parent)): hashlib.sha256(
                    p.read_bytes()
                ).hexdigest()
                for p in paths
            }
            log = logdir / (target.name + ".log")
            row = {
                "name": target.name,
                "class": target.cls,
                "start": datetime.now(timezone.utc).isoformat(),
                "sources": before,
                "limits": {
                    "seconds": args.timeout,
                    "address_space_kib": args.address_space_kib,
                },
                "command": command,
            }
            seconds, peak, code, timed_out = FS.run_process(
                command, log, args.timeout, args.address_space_kib
            )
            row.update(
                end=datetime.now(timezone.utc).isoformat(),
                seconds=seconds,
                peak_rss_kib=peak,
                exit=code,
                timed_out=timed_out,
                log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
            )
            try:
                if timed_out or code:
                    raise ValueError("timeout or verifier failure")
                if before != {
                    str(p.relative_to(paths[-1].parent)): hashlib.sha256(
                        p.read_bytes()
                    ).hexdigest()
                    for p in paths
                }:
                    raise ValueError("exact-far inputs changed during verification")
                check_output(log.read_text(), target)
                row["checked"] = True
                print(
                    f"{target.name}: exact {target.cls} result ({seconds:.2f}s)",
                    flush=True,
                )
            except ValueError as error:
                row.update(checked=False, error=str(error))
                failures.append(target.name + ": " + str(error))
        rows.append(row)
        (logdir / "receipts.json").write_text(json.dumps(rows, indent=2) + "\n")
    if failures:
        raise ValueError("; ".join(failures))
    print(
        "Exact far material: 5 targets, 2 scoped symbolic TRUE lines and 3 confirmed traces."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    validate_targets()
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error("retain the approved 1800-second and 10-GiB maximum caps")
    if args.check_only:
        print(
            "Exact far material: five reviewed targets; both complete 51-case families checked."
        )
        return
    logdir = args.log_dir or Path(tempfile.mkdtemp(prefix="beaconcrypt-exact-far-"))
    logdir.mkdir(parents=True, exist_ok=True)
    print("Exact-far logs: " + str(logdir), flush=True)
    run(args, logdir)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("exact-far check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
