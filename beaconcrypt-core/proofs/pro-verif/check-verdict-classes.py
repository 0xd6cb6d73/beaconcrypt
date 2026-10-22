#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the complete classification of maintained ProVerif expectations.

This is a metadata gate. It neither runs ProVerif nor asserts that an expected
verdict was proved. Actual verdict gates and their evidence remain separate.
"""

import argparse
from collections import Counter
import csv
import importlib.util
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "verdict_inventory", HERE / "verdict-inventory.py"
)
INVENTORY = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = INVENTORY
SPEC.loader.exec_module(INVENTORY)
FIELDS = ("checker", "target", "position", "status", "formula_sha256", "class", "scope")
CLASSES = {
    "security",
    "witness",
    "negative-control",
    "differential-control",
    "definitional",
    "limitation",
    "diagnostic",
}


def validate(rows, expected):
    wanted = {entry.key: entry for entry in expected}
    found = {}
    for row in rows:
        if set(row) != set(FIELDS):
            raise ValueError("classification columns changed")
        key = row["checker"], row["target"], row["position"]
        if key in found:
            raise ValueError(f"duplicate classification: {key}")
        if key not in wanted:
            raise ValueError(f"unexpected classification: {key}")
        entry = wanted[key]
        if row["status"] != entry.status or row["formula_sha256"] != entry.digest:
            raise ValueError(f"changed exact formula or status: {key}")
        cls = row["class"]
        if cls not in CLASSES or not row["scope"].strip():
            raise ValueError(f"missing reviewed class/scope: {key}")
        if (entry.status == "unknown") != (cls == "diagnostic"):
            raise ValueError(f"unknown is only an unresolved diagnostic: {key}")
        if cls == "security" and entry.status != "true":
            raise ValueError(f"security evidence requires TRUE: {key}")
        if (
            cls in {"witness", "negative-control", "limitation"}
            and entry.status != "false"
        ):
            raise ValueError(f"{cls} requires FALSE: {key}")
        found[key] = row
    if found.keys() != wanted.keys():
        raise ValueError(
            f"unclassified expected verdicts: {sorted(wanted.keys() - found.keys())}"
        )
    return Counter(row["class"] for row in rows)


def extension_class_scope(name, target, driver):
    """Reviewed added groups with their exact interface and control scopes."""
    if name == "check-pending-registration":
        fixture, caps = {
            "pending-CROSS": (
                "SchedCrossObjectWitness",
                "objects=2, accept=1, build=1",
            ),
            "pending-REVERSE": ("SchedReverseWitness", "objects=1, accept=2, build=2"),
            "pending-LINEAR": ("SchedLinearFixture", "objects=2, accept=1, build=2"),
            "pending-C-REUSE": ("SchedLinearFixture", "objects=2, accept=1, build=2"),
        }[target.name]
        cls = {
            "witness": "witness",
            "definitional": "definitional",
            "control": "negative-control",
        }[target.cls]
        scope = (
            f"finite operational fixture {fixture}; {caps}; "
            f"manifest bound={target.bound}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return cls, scope
    if name == "check-aead-differential":
        cls = {
            "definitional": "definitional",
            "differential": "differential-control",
        }[target.cls]
        scope = (
            "replicated open contexts and raw frame; public weak-AEAD fixture; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(driver.LIBRARIES)
        )
        return cls, scope
    if name == "check-active-strong-secrecy":
        # Equivalence and single-world disclosure controls have different
        # observations; neither adds an optional-plaintext receive oracle.
        cls = "negative-control" if target.control else "security"
        profile = {
            "b2s": "AnyPin; honest-Server-pin challenge eligibility; T_max = 2",
            "s2b": "honest pins; deferred matching (kid,root) challenge slot; T_max = 3",
        }[target.direction]
        if target.control == "ungated":
            profile = {
                "b2s": "AnyPin; honest-Server-pin eligibility removed; T_max = 2",
                "s2b": "honest pins; matching-partner wait removed; T_max = 3",
            }[target.direction]
        experiment = {
            "": "two-world observational equivalence",
            "leak": "single-world fresh-secret plaintext disclosure control",
            "ungated": "single-world fresh-secret eligibility-removal control",
        }[target.control]
        query = driver.FS.uncommented((HERE / target.query).read_text())
        processes = re.findall(r"\bprocess (\w+)\(\)", query)
        if len(processes) != 1:
            raise ValueError("strong-secrecy process selector changed")
        scope = (
            f"{experiment}; K_reg = 1, K_s = 2, K_r = {target.bound}; {profile}; "
            "labelled finish/receive Some/None bits; no plaintext/reveal oracle; "
            f"process={processes[0]}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return cls, scope
    if name == "check-registration-provenance":
        profile = (
            "wrong one-time purpose parser"
            if target.wrong_purpose
            else "exact source-purpose parser"
        )
        publications = 2 if target.process == "ProvMain(true)" else 1
        scope = (
            f"T0 signature-only source-profile projection; publications_per_identity = {publications}; "
            f"replicated owners, role-DH and verification observers; {profile}; "
            "no snapshot/persistence or native-byte/computational conclusion; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return target.cls, scope
    if name == "check-delayed-response":
        observation = (
            "initial Server chain disclosed"
            if target.process == "A1Main(true)"
            else "post-initial Server chain and initial Beacon chain disclosed"
        )
        claim = (
            "auxiliary completed-root secrecy"
            if target.name == "A1-root"
            else "initial-response origin/projection witness or control"
        )
        scope = (
            f"exact T0 fresh target source-event/knowledge projection; {claim}; "
            "one selected fresh Beacon; unbounded accepts and delayed one-use private pending contexts; "
            "arbitrary actual builder/own/assigned IDs; selected identity/prekey/onetime/KEM and Server identity protected; "
            f"{observation}; binding_removed={target.wrong_binding}; "
            "no full API/native-byte/computational theorem; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return target.cls, scope
    if name == "check-record-origin":
        claim = {
            "L2-origin": "ordinary successful-publication origin; injectivity additionally requires reviewed paper C3, not a solver verdict",
            "L2-identity": "auxiliary selected-identity seed secrecy",
            "L2-C-chain": "initial Beacon-chain disclosure negative control",
            "L2-cache": "selected honest-context sequence2 then cached1 reachability; Kr2 prefix embeds into Kr3",
        }[target.name]
        scope = (
            f"exact T0 source-profile near-event projection; {claim}; "
            f"K_s=2, K_r={target.bound}; AnyPin selected Beacon; replicated arbitrary-candidate accepts and one-use pending builds; "
            "actual Server/Beacon signing identities and assigned IDs; near Some/None plaintext replies; "
            "opposite post-initial chain and Beacon chain3 disclosed; first-far public-computation projection; "
            "selected Server identity and Beacon four private slots/root/initial Beacon materials protected except named control; "
            "no full raw API/native-byte/computational theorem; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return target.cls, scope
    if name == "check-tasking-origin":
        claim = {
            "S2b-origin": "ordinary later successful-publication origin; injectivity additionally uses reviewed single-worker uniqueness, not a solver verdict",
            "S2b-initial": "same-process initial-finish origin supplies the omitted-direction root provenance",
            "S2b-identity": "auxiliary selected-identity seed secrecy",
            "S2b-C-chain": "Server chain2 disclosure negative control with unchanged ordinary-origin formula",
            "S2b-cache": "selected honest-context sequence3 then cached2 reachability; Kr2 prefix embeds into Kr3",
        }[target.name]
        scope = (
            f"exact T0 source-profile Server-to-Beacon near-event projection; {claim}; "
            f"K_s=2, K_r={target.bound}; near positions2/3 after consumed registration1; "
            "AnyPin selected fresh Beacon, protected Server signing identity required by origin antecedents; "
            "replicated arbitrary-candidate accepts and delayed one-use builds; actual Server own ID distinct from assigned event ID; "
            "actual near optional plaintext; literal b2s chain1 and s2b chain4 disclosed, nonselected-identity roots disclosed; "
            "selected private identity/prekey/onetime/KEM and Server identity/root/s2b ancestors protected except named control; "
            "no unrestricted plaintext secrecy or full raw API/native-byte/computational theorem; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return target.cls, scope
    if name == "check-exact-interface-strong":
        claim = {
            "equivalence": "active chosen-message observational equivalence",
            "origin": "auxiliary same-process exact public response/root finish origin",
            "leak": "fresh-secret test publication leaked; confirmed reachability counterexample",
            "ungated": "test eligibility removed; confirmed fresh-secret reachability counterexample",
        }[target.kind]
        scope = (
            f"exact T0 paired private-application selected-source profile; {claim}; "
            f"direction={target.direction}; K_s=2, K_r={target.bound}; b2s near1/2, s2b near2/3 after registration1; "
            "AnyPin, selected fresh Beacon and protected Server signing identity; "
            "eligible b2s iff exact protected pin, eligible s2b iff exact selected peer identity; "
            "ordinary/ineligible calls left-left, eligible alternatives equal-length nonempty; "
            "private application/no echo or secret-dependent action, actual result bits; "
            "delayed one-use builds, arbitrary candidates, literal own/assigned IDs, failed-seal allocations; "
            "opposite/post-near chains and other-identity roots disclosed; "
            "single paired host context, exact T0 constructor idealizations explicit; "
            "no public optional-plaintext, reveals, unbounded schedule or global computational claim; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return target.cls, scope
    if name == "check-application-secrecy":
        claim = {
            "App-b2s": "selected fresh successful Beacon publication secrecy",
            "App-s2b": "selected fresh successful Server publication secrecy",
            "App-b2s-C-leak": "identical b2s query with explicit fresh-plaintext disclosure and confirmed trace",
            "App-s2b-C-leak": "identical s2b query with explicit fresh-plaintext disclosure and confirmed trace",
        }[target.name]
        scope = (
            f"exact T0 trusted-application source-profile; {claim}; "
            f"direction={target.direction}; K_s=2, K_r={target.bound}; b2s near1/2, s2b near2/3 after registration1; "
            "AnyPin selected fresh Beacon, exact protected Server signing identity in query; "
            "private application plaintext/no echo or target-dependent public action; actual optional-result bits; "
            "arbitrary-candidate replicated accepts, one-use delayed builds, actual own/assigned IDs and failed-seal allocations; "
            "literal opposite/post-near chains and other-identity roots disclosed; "
            "target application name preserved by reviewed source paper; "
            "no public-plaintext confidentiality, strong secrecy, finite-byte guessing or global computational theorem; "
            f"process={target.process}; query={target.query}; libraries="
            + ";".join(target.libraries())
        )
        return target.cls, scope
    if name == "check-exact-far":
        profile = "AnyPin" if target.base == "b2s-C4" else "honest pins"
        start = driver.first_far(target.direction)
        claim = (
            "same fresh honest identity far-event witness"
            if target.name == "far-b2s-C-public"
            else "exact C4 or attacker-owned reachability"
        )
        scope = (
            f"T0 exact public HKDF recipes at first-far targets {start}..{start + 50}; "
            f"K_reg=1, K_s=2, K_r=1; {profile}; {claim}; "
            f"public_chain_control={target.public_chain}; hidden receive replies; "
            "reviewed event/knowledge projection only, no global source/API/computational theorem; "
            f"query={target.query}; libraries=" + ";".join(target.libraries())
        )
        return target.cls, scope
    raise ValueError(f"unreviewed extension scope: {name}")


def mldsa_class_scope(target, position, driver):
    """Exact scope for the separate assumed-interface profile and its controls."""
    common = (
        "focused assumed-interface ML-DSA authentication profile; "
        "one honest agent ML key and one pinned server ML key unrevealed; "
        "classical identity/DH secrets exposed; attacker-owned ML registrations admitted without enrollment; "
        "independent key-reveal and closed separation/AD fixtures; "
        "ideal ML-signature unforgeability and collision-free hash assumed; "
        "no computational/QPT, full-protocol, parser/compiler or native-library theorem; "
    )
    claims = (
        (
            "security",
            "noninjective Init origin scoped to the exact honest ML public key",
        ),
        (
            "security",
            "pinned-server origin of request digest and all unsigned decoded response fields, including raw C||T||U and assigned ID, excluding signature bytes",
        ),
        ("witness", "honest request/response verification is reachable"),
        (
            "limitation",
            "attacker-owned ML key with the recovered honest Ed identity is admitted; no Ed-identity-only post-quantum authentication claim",
        ),
        (
            "negative-control",
            "independent exposed agent ML signing key permits acceptance without an honest-sign event",
        ),
        (
            "negative-control",
            "independent exposed server ML signing key permits acceptance without an honest-sign event",
        ),
        (
            "definitional",
            "closed shared-material fixture opens with ordered server/agent ML-key hashes in AD281",
        ),
        (
            "definitional",
            "closed shared-material fixture rejects a changed server ML-key hash in AD281",
        ),
        (
            "definitional",
            "closed shared-material fixture rejects a changed agent ML-key hash in AD281",
        ),
        ("definitional", "closed signature fixture rejects a changed role label"),
        (
            "definitional",
            "closed signature fixture rejects a changed FIPS signing context",
        ),
        ("definitional", "closed signature fixture rejects a different request digest"),
    )
    if target == "mldsa-registration-auth" and 1 <= position <= len(claims):
        cls, claim = claims[position - 1]
    elif target in {control[0] for control in driver.CONTROLS} and position == 1:
        cls = "negative-control"
        claim = (
            "reconstructed origin counterexample after bypassing only the "
            + {
                "without-init-verifier": "Init ML verifier",
                "without-response-verifier": "response ML verifier",
            }[target]
        )
    else:
        raise ValueError("unknown ML-DSA verdict identity")
    return cls, common + claim + "; libraries=" + ";".join(
        (*driver.LIBRARIES, "mldsa-registration-auth.pvl")
    )


def validate_mldsa_scope(rows):
    driver = INVENTORY.module("check-mldsa-registration-auth")
    for row in rows:
        if row["checker"] != "check-mldsa-registration-auth.py":
            continue
        cls, scope = mldsa_class_scope(row["target"], int(row["position"]), driver)
        if row["class"] != cls or row["scope"] != scope:
            raise ValueError("ML-DSA assumed-interface class or exact scope differs")


def validate_scope(rows):
    """Pin reviewed exclusions and each fs target's actual bounds and libraries."""
    validate_mldsa_scope(rows)
    for row in rows:
        checker, target, position = row["checker"], row["target"], int(row["position"])
        if row["status"] == "unknown":
            continue
        if checker == "check-general-registration.py":
            initial, query = map(
                int, re.search(r"target-(\d+)-query-(\d+)", target).groups()
            )
            inactive = (initial != 1 and query != 3) or (
                initial == 1 and query in {10, 12, 14, 15, 16}
            )
            if inactive and row["class"] != "definitional":
                raise ValueError(
                    f"unreachable antecedent promoted to evidence: {target}"
                )
        fixture = checker in {
            "check-registration-response.py",
            "check-registration-beacon.py",
        }
        fixture |= checker == "check-results.awk" and (
            target == "hkdf-prefix-conformance"
            or (target == "failed-receive-compromise" and position in {7, 8})
        )
        if fixture and row["class"] != "definitional":
            raise ValueError(
                f"reviewed fixture promoted to evidence: {checker}/{target}/{position}"
            )
    for name in ("check-free-schedule", "check-primitive-fidelity"):
        driver = INVENTORY.module(name)
        targets = {target.name: target for target in driver.TARGETS}
        for row in rows:
            if row["checker"] != name + ".py":
                continue
            target = targets[row["target"]]
            cls = {
                "security": "security",
                "definitional": "definitional",
                "witness": "witness",
                "limitation": "limitation",
                "control": "negative-control",
            }[target.cls]
            if target.cls == "control" and row["status"] == "true":
                cls = "differential-control"
            scope = (
                f"bounded {target.bounds()}; query={target.query}; libraries="
                + ";".join(target.libraries())
            )
            if row["class"] != cls or row["scope"] != scope:
                raise ValueError(
                    f"fs class, bounds or profile differs: {row['target']}"
                )
    for name in (
        "check-pending-registration",
        "check-aead-differential",
        "check-active-strong-secrecy",
        "check-registration-provenance",
        "check-delayed-response",
        "check-exact-far",
        "check-record-origin",
        "check-tasking-origin",
        "check-application-secrecy",
        "check-exact-interface-strong",
    ):
        driver = INVENTORY.module(name)
        targets = {target.name: target for target in driver.TARGETS}
        for row in rows:
            if row["checker"] != name + ".py":
                continue
            cls, scope = extension_class_scope(name, targets[row["target"]], driver)
            if row["class"] != cls or row["scope"] != scope:
                raise ValueError(
                    f"operational/control class or exact scope differs: {row['target']}"
                )


def read_rows(path):
    with path.open(newline="") as source:
        reader = csv.DictReader(source, delimiter="\t")
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise ValueError("classification header changed")
        return list(reader)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=HERE / "verdict-classes.tsv")
    parser.add_argument(
        "--show", action="store_true", help="print exact formulas and classes"
    )
    args = parser.parse_args()
    expected = INVENTORY.expected_verdicts()
    rows = read_rows(args.manifest)
    counts = validate(rows, expected)
    validate_scope(rows)
    if args.show:
        by_key = {(row["checker"], row["target"], row["position"]): row for row in rows}
        for entry in expected:
            row = by_key[entry.key]
            print(
                "\t".join(
                    (
                        *entry.key,
                        entry.status,
                        row["class"],
                        entry.formula,
                        row["scope"],
                    )
                )
            )
    print(
        f"Classified {len(expected)} expected verdicts: "
        + ", ".join(f"{name}={counts[name]}" for name in sorted(CLASSES))
    )
    print(
        "These are classified expectations, not new ProVerif validation receipts or independent theorem counts."
    )


if __name__ == "__main__":
    main()
