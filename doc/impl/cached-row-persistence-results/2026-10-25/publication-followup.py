"""Archive lightweight publication checks without compiling or collecting timings."""

import datetime
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


base = Path(__file__).resolve().parent
repo = Path("/home/user/worktrees/beaconcrypt-row-persistence")
publication = base / "publication-draft"
log_path = base / "publication-followup.log"
receipt_path = base / "publication-followup.json"
env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", BLACK_NUM_WORKERS="1")
sys.dont_write_bytecode = True
receipt = {
    "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
    "scope": "Formatting checks and summarizer correctness/legacy compatibility only. No compilation or benchmark collection.",
    "environment": {"PYTHONDONTWRITEBYTECODE": "1", "BLACK_NUM_WORKERS": "1"},
    "commands": [],
    "legacy_reports": [],
}
hash_bytes = lambda raw: hashlib.sha256(raw).hexdigest()


def command(argv, cwd, log, require_empty=False):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    log.write("COMMAND " + json.dumps(argv) + "\nCWD " + str(cwd) + "\n")
    log.flush()
    result = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    log.write(result.stdout)
    log.write("EXIT " + str(result.returncode) + "\n")
    log.flush()
    okay = result.returncode == 0 and (not require_empty or not result.stdout.strip())
    receipt["commands"].append({
        "argv": argv,
        "cwd": str(cwd),
        "started": start,
        "finished": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "exit": result.returncode,
        "require_empty_output": require_empty,
        "output_sha256": hash_bytes(result.stdout.encode()),
        "passed": okay,
    })
    if not okay:
        raise RuntimeError("check failed: " + json.dumps(argv))


with log_path.open("x") as log:
    python = str(repo / ".venv/bin/python")
    python_files = [
        "beaconcrypt.pyi",
        "tests/test_row_cached.py",
        "tests/test_row_persistence.py",
        "tests/test_row_transactions.py",
        "beaconcrypt/examples/persistence_bench/summarize.py",
        "beaconcrypt/examples/persistence_bench/test_summarize.py",
    ]
    command([python, "-m", "black", "--check", "--target-version", "py314", *python_files], repo, log)
    go_files = subprocess.check_output(
        ["git", "diff", "--name-only", "278204b921ae31a3e900cf21f690184173e531f5..HEAD", "--", "*.go"],
        cwd=repo, text=True,
    ).splitlines()
    command(["gofmt", "-l", *go_files], repo, log, require_empty=True)
    command([python, "-B", "-m", "unittest", "-v", "test_summarize"], repo / "beaconcrypt/examples/persistence_bench", log)

    source = repo / "beaconcrypt/examples/persistence_bench/summarize.py"
    spec = importlib.util.spec_from_file_location("publication_summarize", source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    archive = repo / "doc/impl/row-persistence-results/2026-10-25"
    for filename in ["persistence-reduced.json.gz", "persistence-peers-1.json.gz", "persistence-peers-100.json.gz", "persistence-peers-1000.json.gz"]:
        path = archive / filename
        compressed = path.read_bytes()
        raw = gzip.decompress(compressed)
        report = json.loads(raw)
        assert report["schema_version"] == 1, filename
        summary = module.summarize(report)
        assert summary["input_schema_version"] == 1, filename
        item = {
            "path": str(path.relative_to(repo)),
            "compressed_sha256": hash_bytes(compressed),
            "input_sha256": hash_bytes(raw),
            "schema_version": 1,
            "groups": len(summary["groups"]),
            "passed": True,
        }
        receipt["legacy_reports"].append(item)
        log.write("LEGACY_SCHEMA1 " + json.dumps(item, sort_keys=True) + "\n")
    receipt["summarizer_source_sha256"] = hash_bytes(source.read_bytes())
    log.write("PASS Black, gofmt, seven synthetic summarizer tests, and four archived schema-1 reports. No new timings inspected.\n")

receipt["finished"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
receipt["passed"] = True
receipt["log_sha256"] = hash_bytes(log_path.read_bytes())
receipt["driver_sha256"] = hash_bytes(Path(__file__).read_bytes())
receipt["synthetic_summarizer_tests"] = 7
receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
for path in [Path(__file__), log_path, receipt_path]:
    destination = publication / path.name
    if destination.exists():
        raise RuntimeError("will not overwrite: " + str(destination))
    shutil.copyfile(path, destination)
print(json.dumps({"passed": True, "commands": len(receipt["commands"]), "synthetic_tests": 7, "legacy_reports": len(receipt["legacy_reports"]), "receipt": str(receipt_path)}, indent=2))
