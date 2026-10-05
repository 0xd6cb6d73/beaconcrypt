#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Enumerate checker expectations without invoking ProVerif.

The legacy AWK expectation builder is evaluated with observation-only replacements
for its two reporting functions. The original checker then validates a synthetic
transcript of those expectations. Python fixture drivers are observed at their
existing run/check_output boundary, in isolated module instances and temporary
directories. Synthetic outputs are metadata tests, never proof evidence.
"""

import contextlib
from dataclasses import dataclass
import hashlib
import importlib.util
import io
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Verdict:
    checker: str
    target: str
    position: int
    formula: str
    status: str

    @property
    def key(self):
        return self.checker, self.target, str(self.position)

    @property
    def digest(self):
        return hashlib.sha256(self.formula.encode()).hexdigest()


def module(name, directory=HERE):
    spec = importlib.util.spec_from_file_location(
        "verdict_inventory_" + name.replace("-", "_"), directory / (name + ".py")
    )
    value = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = value
    spec.loader.exec_module(value)
    return value


def verdict(checker, target, position, result):
    result = re.sub(r"^(?:RESULT |Query )", "", result)
    if result.startswith(("(even ", "(but ")) and result.endswith(".)"):
        result = (
            result[:-2].rsplit(" is ", 1)[0]
            + ") is "
            + result[:-2].rsplit(" is ", 1)[1]
            + "."
        )
    match = re.fullmatch(r"(.+) is (true|false)\.", result)
    if match:
        formula, status = match.groups()
    elif result.endswith(" cannot be proved."):
        formula, status = result.removesuffix(" cannot be proved."), "unknown"
    else:
        raise ValueError(f"not an exact expected verdict: {result}")
    return Verdict(checker, target, position, formula, status)


def awk_expectations(directory=HERE):
    path = directory / "check-results.awk"
    source = path.read_text()
    # Observe the existing expectation calculations, including all loops and
    # instantiated long chain/cache terms. There is no new mode in the gate.
    probe = re.sub(
        r"function reject\(message\) \{.*?\n\}",
        "function reject(message) {}",
        source,
        count=1,
        flags=re.S,
    )
    probe = re.sub(
        r"function require_exact\(wanted, label, query_index, found\) \{.*?\n\}",
        "function require_exact(wanted, label, query_index, found) { print wanted }",
        probe,
        count=1,
        flags=re.S,
    )
    anchor = (
        '      wanted = "Query not attacker(" secret "[]) is " expected[secret] "."'
    )
    if probe.count(anchor) != 1:
        raise ValueError("legacy compromise expectation anchor changed")
    probe = probe.replace(anchor, anchor + "\n      print wanted")
    baseline = '      wanted = "Query not attacker(" baseline_secret[secret_index] "[]) is true."'
    if probe.count(baseline) != 1:
        raise ValueError("legacy baseline expectation anchor changed")
    probe = probe.replace(baseline, baseline + "\n      print wanted")
    scenarios = sorted(set(re.findall(r'scenario == "([^"]+)"', source)))
    rows = []
    for scenario in scenarios:
        found = subprocess.run(
            ["awk", "-v", "scenario=" + scenario, probe],
            input="Verification summary:\n",
            text=True,
            capture_output=True,
            check=True,
        ).stdout.splitlines()
        expected = [line for line in found if line.startswith("Query ")]
        if scenario.endswith("-equivalence"):
            expected = ["Query Observational equivalence is true."]
        if not expected:
            raise ValueError(f"no legacy expectations extracted: {scenario}")
        # AWK's compromise map iteration is unordered, as is that result gate.
        if scenario == "compromise":
            expected.sort()
        primary = ["RESULT " + line[6:] for line in expected]
        if scenario.endswith("-equivalence"):
            synthetic = primary[0] + "\nVerification summary:\n"
        else:
            traces = sum(line.endswith(" is false.") for line in expected)
            synthetic = (
                "\n".join(
                    primary
                    + ["A trace has been found."] * traces
                    + ["Verification summary:"]
                    + expected
                )
                + "\n"
            )
        checked = subprocess.run(
            ["awk", "-v", "scenario=" + scenario, "-f", str(path)],
            input=synthetic,
            text=True,
            capture_output=True,
        )
        if checked.returncode:
            raise ValueError(
                f"legacy enumeration rejected for {scenario}: {checked.stderr}"
            )
        rows.extend(
            verdict(path.name, scenario, i, line) for i, line in enumerate(expected, 1)
        )
    return rows


def fixture_expectations(name, directory=HERE):
    driver = module(name, directory)
    rows = []

    def observe_run(*args):
        # Each maintained driver places its output log immediately before timeout.
        return Path(args[-2]).stem

    def observe_check(target, queries, verdicts, traces):
        for i, (formula, status) in enumerate(zip(queries, verdicts, strict=True), 1):
            if status not in {"true", "false", "unknown"}:
                raise ValueError("unrecognized expected status")
            rows.append(Verdict(name + ".py", target, i, formula, status))

    driver.run = observe_run
    if name == "check-registration-response":
        driver.ADMISSION.check_output = observe_check
    else:
        driver.check_output = observe_check
    with tempfile.TemporaryDirectory(prefix="beaconcrypt-verdict-metadata-") as tmp:
        with contextlib.redirect_stdout(io.StringIO()):
            driver.check("PROVERIF_MUST_NOT_RUN", Path(tmp), 1)
    return rows


def expected_verdicts(directory=HERE):
    rows = awk_expectations(directory)
    for name in (
        "check-registration-set",
        "check-registration-response",
        "check-registration-beacon",
    ):
        rows.extend(fixture_expectations(name, directory))
    for name in (
        "check-free-schedule",
        "check-primitive-fidelity",
        "check-pending-registration",
        "check-aead-differential",
    ):
        driver = module(name, directory)
        if name != "check-primitive-fidelity":
            driver.validate_targets(directory=directory)
        for target in driver.TARGETS:
            rows.extend(
                verdict(name + ".py", target.name, i, line)
                for i, line in enumerate(target.results, 1)
            )
    driver = module("check-kem-controller-auth", directory)
    for target, results in driver.EXPECTED.items():
        rows.extend(
            verdict("check-kem-controller-auth.py", target, i, line)
            for i, line in enumerate(results, 1)
        )
    # The controller gate also checks the non-injective secondary lines.
    rows.extend(
        verdict(
            "check-kem-controller-auth.py",
            "exposed",
            i + 4,
            line.replace("RESULT ", "RESULT (even ").replace("inj-event", "event")[:-1]
            + ".)",
        )
        for i, line in enumerate(driver.EXPOSED, 1)
    )
    driver = module("check-phase2-x25519-alias", directory)
    for target, status in (("canonical", "true"), ("alias", "false")):
        queries = re.findall(
            r"\bquery\b.*?\.", driver.selected_queries(directory), re.S
        )
        for i, query in enumerate(queries, 1):
            formula = re.sub(
                r"\s+", " ", query.split(";", 1)[1].strip().removesuffix(".")
            )
            rows.append(
                Verdict("check-phase2-x25519-alias.py", target, i, formula, status)
            )
    for target in ("projected-canonical", "projected-alias"):
        rows.extend(
            verdict("check-phase2-x25519-alias.py", target, i, line)
            for i, line in enumerate(driver.PROJECTED_RESULTS, 1)
        )
    driver = module("check-general-registration", directory)
    queries = re.findall(
        r"(?ms)^query .*?\.$",
        (directory / "general-registration-admission-queries.pvl").read_text(),
    )
    indices = list(range(1, 24))
    for target in range(53):
        identities = [
            (index, cached)
            for index in driver.query_execution_order(indices)
            for cached in driver.cached_query_cases(index, target)
        ]
        expected = driver.expected_results(target, indices, queries)
        for (index, cached), (formula, status) in zip(
            identities, expected, strict=True
        ):
            case = f"target-{target}-query-{index}"
            if cached is not None:
                case += f"-cached-{cached}"
            rows.append(
                Verdict("check-general-registration.py", case, 1, formula, status)
            )
    keys = [row.key for row in rows]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate expected verdict identity")
    supported = {row.checker for row in rows}
    actual = {p.name for p in directory.glob("check-*.py")} - {
        "check-verdict-classes.py"
    }
    if actual != supported - {"check-results.awk"}:
        raise ValueError(f"unclassified checker entry point: {actual ^ supported}")
    return rows
