#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check selected near-record publication origin in the exact scoped T0 process."""

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FS = load("record_origin_fs", "check-free-schedule.py")
MODELS = load("record_origin_models", "record-origin-models.py")
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
    "fs-registration-binding.pvl",
    "registration-set-admission.pvl",
    "fs-pending-response.pvl",
)


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    query: str
    results: tuple[str, ...]
    process: str
    bound: int = 3
    cache_witness: bool = False

    def libraries(self):
        prefix = "record-origin-cache" if self.cache_witness else "record-origin"
        return LIBRARIES + (
            prefix + "-receive.pvl",
            f"record-origin-kr{self.bound}.pvl",
            prefix + "-sends.pvl",
            prefix + ".pvl",
        )

    def expected_traces(self):
        return int(self.cls in ("witness", "negative-control"))


ORIGIN = "event(FsReceived(beacon_to_server,s,ed_public(k),kid,root_4,t,m)) && event(L2SelectedIdentity(k)) ==> event(L2Published(beacon_to_server,s,ed_public(k),kid,root_4,t,m))"
TARGETS = (
    Target(
        "L2-origin",
        "security",
        "record-origin-auth.pv",
        (ORIGIN + " is true.",),
        "L2Main(false)",
    ),
    Target(
        "L2-identity",
        "security",
        "record-origin-identity.pv",
        ("not (event(L2SelectedIdentity(k)) && attacker(k)) is true.",),
        "L2Main(false)",
    ),
    Target(
        "L2-C-chain",
        "negative-control",
        "record-origin-leak-control.pv",
        (ORIGIN + " is false.",),
        "L2Main(true)",
    ),
    Target(
        "L2-cache",
        "witness",
        "record-origin-cache-witness.pv",
        (
            "not (event(L2CachedAccepted(s,ed_public(k),kid,root_4,m)) && event(L2SelectedIdentity(k))) is false.",
        ),
        "L2Main(false)",
        2,
        True,
    ),
)

TOKEN_SHA256 = {
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
    "fs-registration-binding.pvl": "50b006405e0a98006e2f1ebabe854b466569beed15b7338d656557bf573a679c",
    "registration-set-admission.pvl": "31c72ebb741cef0fdddaafebc3159c6adbc8a43ce39fc2b3e22138e8122c3fbd",
    "fs-pending-response.pvl": "709def004f3ee92f1694ca7b09e0d981111a4353acdaa4d4b38a99cabe4ddd67",
    "delayed-response.pvl": "c2ce813d9d2c27de7516621781f637d69b7e15b1bfceb478fbe82050b0b3adcd",
    "registration-provenance.pvl": "c75baa6a7ffe8c8a320365940a19bbe91f72c7263ac91b04382e866ecd1f8349",
    "record-origin-auth.pv": "23447544587bbb618572d7bcdec8fb33db9d7eea339b39e4611dd53f25a5f6e4",
    "record-origin-cache-receive.pvl": "fd5755370828ded315488f66c00d70aa534588d6a3a7004e15338c0d65f5a0e2",
    "record-origin-cache-sends.pvl": "b87e459475d5f04a45fbd24f1d373c20cab0afd7534e3e0c9e1111acbcf7e3e7",
    "record-origin-cache-witness.pv": "37a38897cf13ba3886b7e817a975335e9149f0285bcade6c0fce7d74193eb281",
    "record-origin-cache.pvl": "6125eb383e37dfb6cde8740b381eeb61599995ed1104d782d28af748c3dc4883",
    "record-origin-identity.pv": "344b162cada803c6a6f0ec8e54ccf3bc74c8e63860b44dbcc9cbc79a0f195fea",
    "record-origin-kr2.pvl": "ade2896d6f22a8aeeb5239857e76d357b0b6213e2db23f3ce36178a943078a45",
    "record-origin-kr3.pvl": "f817aff4f11b7d8ba2729349d7df9ebc77f06ac7f0b39b7b2ed98fe07e1948b5",
    "record-origin-leak-control.pv": "718f6de1b4226f28d15c0d7bacdc2ac22d8247db7644c06da3ec7cc5d7bd0406",
    "record-origin-receive.pvl": "ed55b9872958c9ce8026a79ae3659a23454663ca2b6d5916ed01f2da7364519d",
    "record-origin-sends.pvl": "221a9af907cb8bfc8c1a8a9610867f21455c634f9b27d2180bfd0599d21dd67b",
    "record-origin.pvl": "3862e9ec62a600e59d92933c2f9be980e7dc195b1ea18786b8fee73a1f8caf71",
}
# Reviewed classical projection of the ML-DSA source; see doc/impl/mldsa-source-pins.md.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "28fdde51b14eb4c7d44552dd5828cb036b4ad845a0434d9b5dfb84a628d43734",
    "beaconcrypt/src/server.rs": "fe723eba1b1f8b84c37a1272a9326b93d6a5d987b2b6288df47bbf1e1e302bc3",
    "beaconcrypt/src/ratchet.rs": "7aa3675eb4f340523da263b26294af9d10e060c2ded34226d0789aaa7c9c7ce4",
    "beaconcrypt/src/shared.rs": "29367e958808b0c11d75b5ee1659dd518ea8f7d5379c94fcddb287cfc122183d",
    "beaconcrypt/src/pqxdh.rs": "4d786bf9f42a8f05204bc871f987f2b93440238672120af16c02f6837b11c52d",
    "beaconcrypt-core/src/pqxdh.rs": "bff5dca4b9a292a025ad96ab9fba8761bc63d2e49dac493a2bae0d1cea67a018",
    "beaconcrypt-core/src/pqxdh/concrete.rs": "b3a22f8a7c4adb087e217d58e2d302a057fd5ae224cd8fe2c44777472e469c50",
    "beaconcrypt-core/src/ratchet.rs": "3ed4d65ed1a63605819f8e685707d47b718a91ea9ee23069da88501c8031fa51",
    "beaconcrypt-core/src/ratchet/concrete.rs": "c9f907f20f23ac2851792ff6eef77565a843e61ff266d21617411100e12e431d",
    "beaconcrypt-core/src/ratchet/refined.rs": "ce940e42b1e95bc841121ba80107ce74757fea4f4fcbd771834b93e28cdb459f",
    "beaconcrypt-core/src/record.rs": "2246e63184225fe95f7596454db9380a71c88702b2b57756513cfdcdd9d6623d",
    "beaconcrypt-core/src/session.rs": "3779c778ce4f8ec534c2fa610c0a334302ada76fc5cd601ade575802ff9c07c4",
    "beaconcrypt/src/auth.rs": "e4119ce56650add757b83144f728aabc84904219e4f3fc3678fdce7028ebca29",
    "beaconcrypt-core/src/agreement.rs": "cd4f62dab7d18c9237ad7ce46480ae76faf8e9983b97a9f7af34473550acbabb",
    "beaconcrypt-core/src/registration.rs": "a27884eb8e09752c84f997472652ad54362444d99bf4c104caef0367dbe49f1d"
}


def digest(text):
    return hashlib.sha256(
        json.dumps(MODELS.tokens(text), separators=(",", ":")).encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    FS.validate_legacy_scope(directory)
    if tuple(targets) != TARGETS:
        raise ValueError("record-origin roster, classes or formulas changed")
    if {p.name for p in directory.glob("record-origin-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("record-origin query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed record-origin theory/model/query: " + filename
            )
    MODELS.validate(directory)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed record-origin source projection: " + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing record-origin input " + name)


def run(args, logdir):
    import fcntl

    rows = []
    failures = []
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    for target in TARGETS:
        paths = [HERE / name for name in (*target.libraries(), target.query)]
        command = [args.proverif]
        for path in paths[:-1]:
            command += ["-lib", str(path)]
        command.append(str(paths[-1]))
        log = logdir / (target.name + ".log")
        with args.lock.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            before = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
            row = {
                "name": target.name,
                "class": target.cls,
                "start": datetime.now(timezone.utc).isoformat(),
                "sources": before,
                "limits": {
                    "seconds": args.timeout,
                    "address_space_kib": args.address_space_kib,
                },
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
                    p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths
                }:
                    raise ValueError("verifier sources changed during execution")
                FS.check_output(log.read_text(), target)
                row["checked"] = True
                print(
                    f"{target.name}: {target.cls}, exact expected verdict ({seconds:.2f}s)",
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
        "Record origin: 4 checked T0 targets; injectivity additionally uses the reviewed paper replay argument."
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
    if not 0 < args.timeout <= 180 or not 0 < args.address_space_kib <= 10485760:
        parser.error("retain the reviewed 180-second and 10-GiB maximum caps")
    if args.check_only:
        print(
            "Record origin manifest: 4 targets; Kr3 security, Kr2 cache-prefix witness, scoped paper replay composition."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-record-origin-"))
        print("Record origin logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("record-origin check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
