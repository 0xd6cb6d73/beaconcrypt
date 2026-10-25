#!/usr/bin/env python3
"""Read existing cargo-mutants artifacts; never run cargo or change source files.

Exit 0 means complete reconciliation, including compiler-verified unviable cases.
Exit 1 means findings require attention. Exit 2 means unreadable/invalid inputs.
An optional NEW --output directory receives reproducible compressed snapshots,
the full findings, log hashes, unviable diagnostics, and SHA256SUMS.
"""

import argparse
import collections
import datetime
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
DEFAULT_RUN = HERE.parent / "native-audit/mutants.out"
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
SOURCE_ERROR = re.compile(r"^error\[(E\d{4})\]: (.+)$")
SOURCE_PLAIN = re.compile(
    r"^error: (?:lifetime may not live long enough|"
    r"expected (?:one of|expression|identifier|item|type|pattern|`;`|`,`|`\{`)|"
    r"mismatched closing delimiter|unexpected closing delimiter|"
    r"this file contains an unclosed delimiter|"
    r"return type notation not allowed in this position|"
    r"unconstrained opaque type|"
    r"implementation of .+ is not general enough)"
)
# Exact Rust diagnostics confirmed against the 11 original review findings.
# Keep these literal: broad "cannot find"/"overflow" matching could mask tool failures.
REVIEWED_SOURCE_HEADERS = {
    "error: cannot find macro `vec` in this scope",
    "error: this arithmetic operation will overflow",
    "error: `<` is interpreted as a start of generic arguments for `usize`, not a comparison",
}
WRAPPER_ERROR = re.compile(
    r"^error: (?:could not compile |command `.+` exited with code |"
    r"aborting due to \d+ previous error)"
)
INFRASTRUCTURE = {
    "disk": re.compile(r"no space left on device|disk quota exceeded|read-only file system", re.I),
    "memory": re.compile(r"out of memory|cannot allocate memory|memory allocation of \d+ bytes failed|"
                         r"allocation failed|oom-kill|oom_kill|bad_alloc", re.I),
    "compiler_crash": re.compile(r"internal compiler error|the compiler unexpectedly panicked|"
                                 r"thread ['\"]rustc[^'\"]*['\"] panicked|"
                                 r"LLVM ERROR:|LLVM error:|rustc-ice-", re.I),
    "build_signal": re.compile(r"signal: (?:9|11)|SIGKILL|SIGSEGV|killed signal terminated program", re.I),
    "linker_or_tool": re.compile(r"error: linking with |linker .+ not found|"
                                 r"failed to run custom build command|could not execute process|"
                                 r"failed to spawn|failed to execute|too many open files|"
                                 r"resource temporarily unavailable|permission denied", re.I),
    "dependency_or_network": re.compile(r"failed to (?:download|fetch|get) |"
                                        r"could not resolve host|network is unreachable|"
                                        r"failed to select a version|checksum.*(?:failed|mismatch)", re.I),
}
KNOWN_STATUSES = {"CaughtMutant", "MissedMutant", "Unviable", "Timeout"}
FIELDS = ("name", "package", "file", "function", "span", "replacement", "genre")


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    raw = path.read_bytes()
    data = gzip.decompress(raw) if path.suffix == ".gz" else raw
    return json.loads(data), data


def identity(mutant):
    return {key: mutant.get(key) for key in FIELDS}


def safe_artifact(run, relative):
    if not isinstance(relative, str) or not relative:
        raise ValueError("missing artifact path")
    path = (run / relative).resolve()
    if not path.is_relative_to(run):
        raise ValueError("artifact path escapes run directory: " + relative)
    return path


def diagnostic_text(raw):
    """Drop the embedded diff, whose string literals are not diagnostics."""
    text = ANSI.sub("", raw.decode("utf-8", errors="replace"))
    commands = list(re.finditer(r"^\*\*\* .*(?:/cargo|\bcargo) (?:nextest|test|check|build)\b", text, re.M))
    return text[commands[0].start():] if commands else text


def diagnostics(text, phases):
    source = []
    unknown = []
    infrastructure = []
    lines = text.splitlines()
    # In test output a mutant can legitimately crash; a compiler crash cannot.
    build_only = "\n".join(lines)
    boundaries = [i for i, line in enumerate(lines) if line.startswith("*** ") and " nextest run " in line and "--no-run" not in line]
    if boundaries:
        build_only = "\n".join(lines[:boundaries[0]])
    for category, pattern in INFRASTRUCTURE.items():
        search_lines = build_only.splitlines() if category in {"build_signal", "compiler_crash", "linker_or_tool"} else lines
        matches = [line[:1000] for line in search_lines if pattern.search(line)]
        if matches:
            infrastructure.append({"category": category, "lines": list(dict.fromkeys(matches))[:12]})
    for line in lines:
        match = SOURCE_ERROR.match(line)
        if match:
            source.append({"code": match[1], "message": match[2]})
        elif SOURCE_PLAIN.match(line) or line in REVIEWED_SOURCE_HEADERS:
            source.append({"code": None, "message": line.removeprefix("error: ")})
        elif line.startswith("error:") and not WRAPPER_ERROR.match(line):
            unknown.append(line[:1000])
    source = list({(item["code"], item["message"]): item for item in source}.values())
    has_source_location = bool(re.search(r"^\s*(?:-->|:::) .+\.rs:\d+:\d+", text, re.M))
    failed = [phase for phase in phases if phase.get("process_status") != "Success"]
    valid_build_failure = bool(failed) and all(
        phase.get("phase") in {"Build", "Check"}
        and phase.get("process_status") == {"Failure": 101}
        for phase in failed
    ) and not any(phase.get("phase") == "Test" for phase in phases)
    if infrastructure:
        classification = "infrastructure_failure"
    elif source and has_source_location and valid_build_failure and not unknown:
        classification = "source_compile_error"
    else:
        classification = "unclassified_requires_review"
    return {
        "classification": classification,
        "source_errors": source,
        "has_rust_source_location": has_source_location,
        "expected_compile_failure_status": valid_build_failure,
        "unrecognized_error_headers": list(dict.fromkeys(unknown)),
        "infrastructure": infrastructure,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, default=DEFAULT_RUN)
    parser.add_argument("--catalog", type=Path, default=HERE / "expected-catalog.json.gz")
    parser.add_argument("--expected-count", type=int, default=1672)
    parser.add_argument("--output", type=Path, help="Create this new directory; never overwrite an existing receipt")
    args = parser.parse_args()
    run = args.run.resolve()
    catalog, catalog_raw = read_json(args.catalog)
    run_catalog, run_catalog_raw = read_json(run / "mutants.json")
    outcomes, outcomes_raw = read_json(run / "outcomes.json")
    if not isinstance(catalog, list) or not isinstance(run_catalog, list) or not isinstance(outcomes, dict):
        raise ValueError("unexpected catalog or outcomes schema")
    rows = outcomes["outcomes"]
    if not isinstance(rows, list):
        raise ValueError("outcomes must be a list")
    issues = []

    def issue(kind, **detail):
        issues.append({"kind": kind, **detail})

    def indexed(values, label):
        result = collections.defaultdict(list)
        for index, value in enumerate(values):
            if not isinstance(value, dict) or not isinstance(value.get("name"), str):
                issue("invalid_mutant", source=label, index=index)
                continue
            result[value["name"]].append(value)
        for name, duplicates in result.items():
            if len(duplicates) != 1:
                issue("duplicate_catalog_entry", source=label, name=name, count=len(duplicates))
        return result

    expected = indexed(catalog, "expected_catalog")
    actual_catalog = indexed(run_catalog, "run_catalog")
    if len(catalog) != args.expected_count:
        issue("unexpected_catalog_count", expected=args.expected_count, actual=len(catalog))
    for name in sorted(set(expected) - set(actual_catalog)):
        issue("missing_from_run_catalog", name=name)
    for name in sorted(set(actual_catalog) - set(expected)):
        issue("unexpected_in_run_catalog", name=name)
    for name in sorted(set(expected) & set(actual_catalog)):
        if expected[name] != actual_catalog[name]:
            issue("run_catalog_content_mismatch", name=name)

    observed = collections.defaultdict(list)
    statuses = collections.Counter()
    baseline = []
    unviable = []
    artifacts = []
    for index, row in enumerate(rows):
        scenario = row.get("scenario")
        if scenario == "Baseline":
            baseline.append(row)
            if row.get("summary") != "Success":
                issue("baseline_failure", outcome_index=index, summary=row.get("summary"))
            continue
        if not isinstance(scenario, dict) or not isinstance(scenario.get("Mutant"), dict):
            issue("unknown_scenario", outcome_index=index, scenario=scenario)
            continue
        mutant = scenario["Mutant"]
        name = mutant.get("name")
        if not isinstance(name, str):
            issue("invalid_outcome_mutant", outcome_index=index)
            continue
        observed[name].append(index)
        status = row.get("summary")
        statuses[status] += 1
        if name not in expected:
            issue("unexpected_outcome", name=name, outcome_index=index)
        elif identity(mutant) != identity(expected[name][0]):
            issue("outcome_mutant_content_mismatch", name=name, outcome_index=index)
        if status not in KNOWN_STATUSES:
            issue("unknown_status", name=name, status=status, outcome_index=index)
        elif status in {"MissedMutant", "Timeout"}:
            issue(status, name=name, outcome_index=index)

        contents = {}
        for key in ("log_path", "diff_path"):
            try:
                path = safe_artifact(run, row.get(key))
                raw = path.read_bytes()
                contents[key] = raw
                artifacts.append({"path": str(path.relative_to(run)), "sha256": sha256(raw), "bytes": len(raw)})
            except (OSError, ValueError) as error:
                issue("missing_or_invalid_artifact", name=name, artifact=key, detail=str(error))
        if name in expected and "diff_path" in contents:
            expected_diff = expected[name][0].get("diff")
            if expected_diff is not None and contents["diff_path"].decode("utf-8") != expected_diff:
                issue("mutation_diff_mismatch", name=name)

        phases = row.get("phase_results", [])
        if not phases:
            issue("missing_phase_results", name=name)
        if status == "CaughtMutant":
            if not any(p.get("phase") == "Test" and p.get("process_status") != "Success" for p in phases):
                issue("caught_without_failed_test_phase", name=name)
            if any(p.get("phase") in {"Build", "Check"} and p.get("process_status") != "Success" for p in phases):
                issue("caught_with_failed_build", name=name)
        if "log_path" in contents:
            detail = diagnostics(diagnostic_text(contents["log_path"]), phases)
            if detail["infrastructure"]:
                issue("infrastructure_diagnostic", name=name, summary=status, diagnostics=detail["infrastructure"])
            if status == "Unviable":
                unviable.append({"name": name, "log_path": row["log_path"], **detail})
                if detail["classification"] != "source_compile_error":
                    issue("unviable_requires_review", name=name, classification=detail["classification"])

    for name, indexes in observed.items():
        if len(indexes) != 1:
            issue("duplicate_outcome", name=name, outcome_indexes=indexes)
    for name in sorted(set(expected) - set(observed)):
        issue("uncovered", name=name)
    if len(baseline) > 1:
        issue("duplicate_baseline", count=len(baseline))
    for key, status in (("caught", "CaughtMutant"), ("missed", "MissedMutant"), ("timeout", "Timeout"), ("unviable", "Unviable")):
        if outcomes.get(key) != statuses[status]:
            issue("counter_mismatch", counter=key, declared=outcomes.get(key), observed=statuses[status])
    if outcomes.get("total_mutants") != sum(statuses.values()):
        issue("counter_mismatch", counter="total_mutants", declared=outcomes.get("total_mutants"), observed=sum(statuses.values()))
    if not outcomes.get("end_time"):
        issue("run_not_finalized", detail="outcomes.end_time is null or absent")
    if (run / "outcomes.json").read_bytes() != outcomes_raw:
        issue("outcomes_changed_during_read")
    if (run / "mutants.json").read_bytes() != run_catalog_raw:
        issue("run_catalog_changed_during_read")

    by_class = collections.Counter(item["classification"] for item in unviable)
    error_codes = collections.Counter(error["code"] or "unnumbered" for item in unviable for error in item["source_errors"])
    summary = {
        "audit_passed": not issues,
        "created_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "run_directory": str(run),
        "catalog_path": str(args.catalog.resolve()),
        "catalog_sha256": sha256(catalog_raw),
        "outcomes_sha256": sha256(outcomes_raw),
        "expected_mutants": args.expected_count,
        "catalog_entries": len(catalog),
        "run_catalog_entries": len(run_catalog),
        "unique_outcomes": len(observed),
        "outcome_entries": sum(statuses.values()),
        "statuses": dict(statuses),
        "verified_unviable": by_class["source_compile_error"],
        "unviable_requiring_review": statuses["Unviable"] - by_class["source_compile_error"],
        "baseline_entries": len(baseline),
        "baseline_policy": "Baseline skipped in this run; preceding validation is separate evidence." if not baseline else "Baseline present in outcomes.",
        "unviable_classifications": dict(by_class),
        "unviable_error_codes": dict(error_codes),
        "issue_counts": dict(collections.Counter(item["kind"] for item in issues)),
        "issue_count": len(issues),
        "start_time": outcomes.get("start_time"),
        "end_time": outcomes.get("end_time"),
        "cargo_mutants_version": outcomes.get("cargo_mutants_version"),
        "limits": "Compiler-error classification checks diagnostics and process outcomes. It is deliberately conservative: unknown diagnostics and any infrastructure marker require manual review. This helper does not regenerate a catalog, attest source stability, or establish the separately run baseline.",
    }
    if args.output:
        output = args.output.resolve()
        if output == run or output.is_relative_to(run):
            raise ValueError("output must be outside the cargo-mutants input directory")
        output.mkdir(parents=True, exist_ok=False)
        summary["receipt_directory"] = str(output)
        payloads = {"catalog.json": catalog_raw, "outcomes.json": outcomes_raw, "run-catalog.json": run_catalog_raw}
        for name, value in (("summary.json", summary), ("findings.json", issues), ("unviable-diagnostics.json", unviable), ("artifact-manifest.json", artifacts)):
            payloads[name] = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
        for name, raw in payloads.items():
            if name not in {"catalog.json", "outcomes.json", "run-catalog.json"}:
                (output / name).write_bytes(raw)
            (output / (name + ".gz")).write_bytes(gzip.compress(raw, mtime=0))
        manifest = []
        for path in sorted(output.iterdir()):
            manifest.append(sha256(path.read_bytes()) + "  " + path.name + "\n")
        (output / "SHA256SUMS").write_text("".join(manifest))
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if not issues else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("audit input error: " + str(error), file=sys.stderr)
        sys.exit(2)
