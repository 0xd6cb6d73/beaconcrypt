#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact-interface Kr3 active secrecy and public-response lookup auxiliaries.

The private-application paired source/context argument is separately reviewed.
No public optional-plaintext or completed computational/global result is claimed.
"""

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
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


FS = load("exact_strong_fs", "check-free-schedule.py")
ACTIVE = load("exact_strong_active", "check-active-strong-secrecy.py")
MODELS = load("exact_strong_models", "exact-interface-strong-models.py")
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
    "fs-registration-binding.pvl",
)


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    direction: str
    kind: str
    query: str
    result: str
    process: str
    bound: int = 3

    @property
    def results(self):
        return (self.result,)

    @property
    def control(self):
        return self.kind != "equivalence"

    def expected_traces(self):
        return int(self.cls == "negative-control")

    def libraries(self):
        prefix = "exact-interface-strong-" + self.direction
        old = "record-origin" if self.direction == "b2s" else "tasking-origin"
        if self.kind == "equivalence":
            registration = "exact-interface-strong-registration.pvl"
            receive = "-receive.pvl"
            sends = "-sends.pvl"
            main = ".pvl"
        else:
            registration = "registration-set-admission.pvl"
            receive = (
                "-origin-receive.pvl"
                if self.kind == "origin"
                else "-control-receive.pvl"
            )
            sends = "-" + self.kind + "-sends.pvl"
            main = "-origin.pvl" if self.kind == "origin" else "-auxiliary.pvl"
        return LIBRARIES + (
            registration,
            "fs-pending-response.pvl",
            prefix + receive,
            old + "-kr3.pvl",
            prefix + sends,
            prefix + main,
        )


TARGETS = (
    Target(
        "SSX-b2s",
        "security",
        "b2s",
        "equivalence",
        "exact-interface-strong-b2s.pv",
        "Observational equivalence is true.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b",
        "security",
        "s2b",
        "equivalence",
        "exact-interface-strong-s2b.pv",
        "Observational equivalence is true.",
        "S2bMain(false)",
        3,
    ),
    Target(
        "SSX-b2s-origin",
        "security",
        "b2s",
        "origin",
        "exact-interface-strong-b2s-origin.pv",
        "event(ExactStrongFinishedResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) && event(L2SelectedIdentity(k)) ==> event(ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) is true.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b-origin",
        "security",
        "s2b",
        "origin",
        "exact-interface-strong-s2b-origin.pv",
        "event(ExactStrongFinishedResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) && event(S2bSelectedIdentity(k)) ==> event(ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) is true.",
        "S2bMain(false)",
        3,
    ),
    Target(
        "SSX-b2s-leak",
        "negative-control",
        "b2s",
        "leak",
        "exact-interface-strong-b2s-leak.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b-leak",
        "negative-control",
        "s2b",
        "leak",
        "exact-interface-strong-s2b-leak.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "S2bMain(false)",
        3,
    ),
    Target(
        "SSX-b2s-ungated",
        "negative-control",
        "b2s",
        "ungated",
        "exact-interface-strong-b2s-ungated.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b-ungated",
        "negative-control",
        "s2b",
        "ungated",
        "exact-interface-strong-s2b-ungated.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "S2bMain(false)",
        3,
    ),
)

TOKEN_SHA256 = {
    "application-secrecy-b2s-leak-sends.pvl": "101c4ed638ee169413fbebf99fe5272ea478cc0078d1c9cb52bbc0e93090bf9f",
    "application-secrecy-b2s-leak.pv": "c1245b0b56a1c9d0157baa3c1433e22ec362c177f79f014cde264fb95fc75f81",
    "application-secrecy-b2s-receive.pvl": "abc719ac4d0435ccdd3e5484b3088b1d351fac1e42b9dcd9dd38bba2084fec0e",
    "application-secrecy-b2s-sends.pvl": "5e3cd1beb81e955767afc6fa51362768d8426f09e048b1db461a8ec73e80f847",
    "application-secrecy-b2s.pv": "c1245b0b56a1c9d0157baa3c1433e22ec362c177f79f014cde264fb95fc75f81",
    "application-secrecy-b2s.pvl": "2da210517fb66ccde25ae913fdfc4fc61e19c8c2797ad65b00bd1dbc249ae862",
    "application-secrecy-s2b-leak-sends.pvl": "a9b7ed262b7de336d1d9697ba1cecd617a6548a71a4b34f43d9b9f79c63added",
    "application-secrecy-s2b-leak.pv": "2c36eef0e4b73451b3c441110a4113abd7ab804e21683670369d3429b4164eeb",
    "application-secrecy-s2b-receive.pvl": "829e8086b22ca8972d5f6b6e50207982978a5aff76922f4fb9bdea3d6908c23d",
    "application-secrecy-s2b-sends.pvl": "0ade487b09cbe3158bb57663da7d5ad0e57b45e9fb3e7966bad008b751cc1ce7",
    "application-secrecy-s2b.pv": "2c36eef0e4b73451b3c441110a4113abd7ab804e21683670369d3429b4164eeb",
    "application-secrecy-s2b.pvl": "fb60484a0456a27f0fc1b37987dc9bea869821983198b01bc764d452d5762a0b",
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "delayed-response.pvl": "c2ce813d9d2c27de7516621781f637d69b7e15b1bfceb478fbe82050b0b3adcd",
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
    "fs-pending-response.pvl": "709def004f3ee92f1694ca7b09e0d981111a4353acdaa4d4b38a99cabe4ddd67",
    "fs-registration-binding.pvl": "50b006405e0a98006e2f1ebabe854b466569beed15b7338d656557bf573a679c",
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
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
    "registration-provenance.pvl": "c75baa6a7ffe8c8a320365940a19bbe91f72c7263ac91b04382e866ecd1f8349",
    "registration-set-admission.pvl": "31c72ebb741cef0fdddaafebc3159c6adbc8a43ce39fc2b3e22138e8122c3fbd",
    "tasking-origin-auth.pv": "27d45efd8e7da6907ff2b0a2d3fb9e069de29dfefd220f3afb2543f5b3933590",
    "tasking-origin-cache-receive.pvl": "a5e4f61fc4cfd66b43022daf8597587c61404dc83920db6ab0c66684437e49d5",
    "tasking-origin-cache-sends.pvl": "8c48ea0b0e74f9a022761ec0e463ecbdd303d37a206467f317939fcb4a5a0b29",
    "tasking-origin-cache-witness.pv": "a82b2aa9fffcb98a91ae5085030017eb2e011b6c71cf6602c615396c46652b67",
    "tasking-origin-cache.pvl": "ebefb3ea873a8565f03730d7af1283453108d377ee8de93c2ab3f5b137e3bfde",
    "tasking-origin-identity.pv": "f2c9e537971e1be783a2333fe1f0e547cee8b6b64ddce57837698de9675c642d",
    "tasking-origin-initial.pv": "8cdc8c218aec8644b1b99c4911bfea3157f9f42b47620f0d78da89a3208cdf41",
    "tasking-origin-kr2.pvl": "ecb0f4d5b2bcd0bd9bf9bd2770d8f3db124ed5d9650a67f72bf1257558d357bb",
    "tasking-origin-kr3.pvl": "90bdf7d544fe3e0b66ee9a854b6df0f702610b3382d796c52837f442fc525ef6",
    "tasking-origin-leak-control.pv": "bf5896bdda3af995c47e9f250a978706ed05e19f13954bc0217ab1b243d64c28",
    "tasking-origin-receive.pvl": "cde8076d5e39b37015d3b4014eb6f78ba6d2936ce5051d899aed19415a66ac82",
    "tasking-origin-sends.pvl": "8c48ea0b0e74f9a022761ec0e463ecbdd303d37a206467f317939fcb4a5a0b29",
    "tasking-origin.pvl": "ebefb3ea873a8565f03730d7af1283453108d377ee8de93c2ab3f5b137e3bfde",
    "exact-interface-strong-b2s-auxiliary.pvl": "2da210517fb66ccde25ae913fdfc4fc61e19c8c2797ad65b00bd1dbc249ae862",
    "exact-interface-strong-b2s-control-receive.pvl": "6ff16f4611ca9f001e736e7fd1e7b9d1cc4f2086c5ec52ed4034938f0e2feb7d",
    "exact-interface-strong-b2s-leak-sends.pvl": "e3eeec9eb2948af166f36b2db08fc7054af25d6e517e5b939e717bbd026c5f19",
    "exact-interface-strong-b2s-leak.pv": "97c53615086d3f663ae1de1dad3e2296a90344d6a19ec5851afcccb577db0d84",
    "exact-interface-strong-b2s-origin-receive.pvl": "6b5ac22c9fff06e79029e3016793c532731a2b4ec846e1f1d6e20d6902b8c08d",
    "exact-interface-strong-b2s-origin-sends.pvl": "66db1c17862ce80332bf62c2d51b1f58b183219801e75c79a12787d51db02f05",
    "exact-interface-strong-b2s-origin.pv": "2e7d1269144bc2b2b1d453c4e548209e21673e6f7bd11c1bd6eee6303b9bd8b5",
    "exact-interface-strong-b2s-origin.pvl": "5f53fd78e147decd1dbca780b517451d2d6c1bcc76eacc9b3f7199c1c9e6f036",
    "exact-interface-strong-b2s-receive.pvl": "4ea1e57f24a76d22c14b67d191c3279cc82e4db9bcc01f6eb26390c9010e7f5b",
    "exact-interface-strong-b2s-sends.pvl": "16937c05492ab24141c8f367147d46e8ee795b50fce627002a830216b674567d",
    "exact-interface-strong-b2s-ungated-sends.pvl": "60cc2b6e47ee0034211d51b06b9d2a051155896480d6c5d6c7454d3b31120375",
    "exact-interface-strong-b2s-ungated.pv": "97c53615086d3f663ae1de1dad3e2296a90344d6a19ec5851afcccb577db0d84",
    "exact-interface-strong-b2s.pv": "e25e4c1d5084d7cdeb6df48f16fb0e876c89756ed544f0bd76484aca08bfaf4b",
    "exact-interface-strong-b2s.pvl": "3862e9ec62a600e59d92933c2f9be980e7dc195b1ea18786b8fee73a1f8caf71",
    "exact-interface-strong-registration.pvl": "5d81da76601be3eed72cd535a725716da7fa241efd4293fd9e13016a91da155c",
    "exact-interface-strong-s2b-auxiliary.pvl": "7fed610b93cd6800839483067710d2d26522635f84f9ffefb433a29e490b7955",
    "exact-interface-strong-s2b-control-receive.pvl": "bdbaa3a87c1ca5eb52acee934871b0f03f0e252004200a81aedaca52c535bf04",
    "exact-interface-strong-s2b-leak-sends.pvl": "6c79f950a8fd7efd02f14973359691ec85cf1fba20af776c994454b131f2e7f3",
    "exact-interface-strong-s2b-leak.pv": "48a2b2db58378b910b7e126ec3b103abd4cfb13cbe36d59d895db4d9700bb843",
    "exact-interface-strong-s2b-origin-receive.pvl": "f108f7548aa66582412f80d529e2ba9645478369b8b7cb441f2677649143cf58",
    "exact-interface-strong-s2b-origin-sends.pvl": "637971062de2dd9cfc19f2d5cff9120b188017306e202e6733ee5de92ca91034",
    "exact-interface-strong-s2b-origin.pv": "665526184085f995812e723db119665ce5c304f753d2e2284e1008d61db2a1c2",
    "exact-interface-strong-s2b-origin.pvl": "3853c2be6b10954fd4161d069f7300620e0580d77f7ef03f877b61534fc75867",
    "exact-interface-strong-s2b-receive.pvl": "62c073c129af5198adbe84a63f1c04ba0b1ff9c012d144830c21e6db7812d5e2",
    "exact-interface-strong-s2b-sends.pvl": "5b34ffb832c165cf8bb14e6b8dbf491425d6008e462406577a4a42532df1925c",
    "exact-interface-strong-s2b-ungated-sends.pvl": "d968d33b859c642899235e370fef52632575b247654b267938937fb03d5be535",
    "exact-interface-strong-s2b-ungated.pv": "48a2b2db58378b910b7e126ec3b103abd4cfb13cbe36d59d895db4d9700bb843",
    "exact-interface-strong-s2b.pv": "3390dcea7fc8605b42c71dc106713a107ca4d9fce07d1d0cdc7ba1fb4cd0f222",
    "exact-interface-strong-s2b.pvl": "4ea762ad8f2bba44039afaa68106e66b3a6c661cf96244ad981109acce71542f",
}
# Reviewed classical projection of the ML-DSA source; see doc/impl/mldsa-source-pins.md.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "880a240ccfda92565734d31ae3a7e630e988d3e1ff77666579ed31dafd15fd68",
    "beaconcrypt/src/server.rs": "1cf58484619c712f3970f1bde06789559ee11e3af50430d42c1e3fe41fded706",
    "beaconcrypt/src/ratchet.rs": "bfe86fc2b5589a706c0513505e6cf9249741654538eabe7d2708c8213baf256b",
    "beaconcrypt/src/shared.rs": "9100666b1a7f037bb792778cb1433ea9b5b03c715ed3e1c482f7362ff2c3d56e",
    "beaconcrypt/src/pqxdh.rs": "892c9b689b6ccfcec08d5d76707667d181c22e021f6b7106495844f5c8ca2fd1",
    "beaconcrypt-core/src/pqxdh.rs": "2f2e1b3c8e02ad605d5078a8ca16ccf569c50a77bda6df787d84722a16806763",
    "beaconcrypt-core/src/pqxdh/concrete.rs": "b3a22f8a7c4adb087e217d58e2d302a057fd5ae224cd8fe2c44777472e469c50",
    "beaconcrypt-core/src/ratchet.rs": "3ed4d65ed1a63605819f8e685707d47b718a91ea9ee23069da88501c8031fa51",
    "beaconcrypt-core/src/ratchet/concrete.rs": "c9f907f20f23ac2851792ff6eef77565a843e61ff266d21617411100e12e431d",
    "beaconcrypt-core/src/ratchet/refined.rs": "ce940e42b1e95bc841121ba80107ce74757fea4f4fcbd771834b93e28cdb459f",
    "beaconcrypt-core/src/record.rs": "2246e63184225fe95f7596454db9380a71c88702b2b57756513cfdcdd9d6623d",
}


def digest(text):
    return hashlib.sha256(
        json.dumps(MODELS.tokens(text), separators=(",", ":")).encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    FS.validate_legacy_scope(directory)
    if tuple(targets) != TARGETS:
        raise ValueError("exact-interface-strong roster, classes or formulas changed")
    if {p.name for p in directory.glob("exact-interface-strong-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("exact-interface-strong query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed exact-interface-strong theory/model/query: " + filename
            )
    MODELS.validate(directory)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed exact-interface-strong source projection: " + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing exact-interface-strong input " + name)


def check_output(output, target):
    ACTIVE.check_output(output, target)


def run(args, logdir):
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
                check_output(log.read_text(), target)
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
        "Exact-interface strong secrecy: 8 checked T0 targets: 2 equivalences, 2 public-response safety auxiliaries, 4 reachability controls; private application profile only."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    validate_targets()
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error("retain the reviewed 1800-second and 10-GiB maximum caps")
    if args.check_only:
        print(
            "Exact-interface strong secrecy manifest: 8 targets: both Kr3 equivalences, exact public response/root origin, four confirmed-trace controls."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-exact-interface-strong-"))
        print("Exact-interface strong secrecy logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("exact-interface-strong check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
