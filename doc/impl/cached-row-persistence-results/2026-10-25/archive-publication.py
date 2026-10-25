"""Copy immutable evidence into the publication draft; never touch source evidence."""

import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil


BASE = Path(__file__).resolve().parent
DEST = BASE / "publication-draft"
entries = []
excluded = []


def fingerprint(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def archive(source, relative, compress=False, category="support"):
    require_regular = source.is_file() and not source.is_symlink()
    if not require_regular:
        raise RuntimeError("not a regular source file: " + str(source))
    before = fingerprint(source)
    destination = DEST / (str(relative) + (".gz" if compress else ""))
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        existing = gzip.decompress(destination.read_bytes()) if compress else destination.read_bytes()
        if hashlib.sha256(existing).hexdigest() != before:
            raise RuntimeError("refusing different existing evidence: " + str(destination))
    elif compress:
        with source.open("rb") as input_file, destination.open("xb") as output_file:
            with gzip.GzipFile(filename="", mode="wb", fileobj=output_file, mtime=0, compresslevel=6) as compressed:
                shutil.copyfileobj(input_file, compressed, length=1024 * 1024)
    else:
        with source.open("rb") as input_file, destination.open("xb") as output_file:
            shutil.copyfileobj(input_file, output_file, length=1024 * 1024)
    if fingerprint(source) != before:
        raise RuntimeError("source evidence changed during copy: " + str(source))
    entries.append({
        "source_path": str(source), "source_relative_to_hybrid": str(source.relative_to(BASE)),
        "archive_path": str(destination.relative_to(DEST)), "category": category,
        "encoding": "gzip" if compress else "identity", "source_bytes": source.stat().st_size,
        "archive_bytes": destination.stat().st_size, "decompressed_sha256": before,
        "archive_sha256": fingerprint(destination),
    })


for campaign, category in (("collection-20261025-v2", "retained_v2_campaign"), ("collection-20261025", "superseded_strict_pilot")):
    source_root = BASE / campaign
    for root, directories, filenames in os.walk(source_root):
        root = Path(root)
        for name in list(directories):
            if name in {"fixtures", "__pycache__"}:
                excluded.append({"source_path": str(root / name), "reason": "database fixtures" if name == "fixtures" else "Python bytecode cache", "directory_not_traversed": True})
                directories.remove(name)
        for name in sorted(filenames):
            source = root / name
            if name.endswith((".lock", ".pyc")) or name in {"runner", "persistence_bench"}:
                excluded.append({"source_path": str(source), "reason": "lock, bytecode, or executable artifact"})
                continue
            if source.suffix in {".db", ".sqlite", ".sqlite3"} or name.endswith(("-wal", "-shm")):
                raise RuntimeError("unexpected database outside excluded fixtures: " + str(source))
            relative = Path("collections") / campaign / source.relative_to(source_root)
            compress = name in {"report.json", "summary.json", "quiet-window.jsonl", "collection-events.jsonl"} or name.endswith(".log")
            archive(source, relative, compress, category)

for source in sorted((BASE / "analysis-v2").iterdir()):
    archive(source, Path("analysis") / source.name, category="validated_v2_analysis")

support = [
    "build-final-v2.json", "validation-final-v2.json", "quiet-vm-review.json",
    "quiet-vm-guard-tests.log", "quiet-vm-policy.json", "collection-policy-revision.json",
    "analysis-plan.json", "export-completed-v2.py", "export-completed-v2-README.md",
    "export-review.json", "publication-followup.py", "publication-followup.json", "publication-followup.log",
    "hybrid_guard.py", "prepare-quiet-hybrid.py", "run-quiet-hybrid.py", "wait-quiet-hybrid.py", "test_hybrid_guard.py",
    "mutate-native.py", "native-final-source-catalog.json", "validate.py", "focused.py", "bindings.py",
    "revalidate-pg.py", "final-lint.py", "build-release.py", "archive-publication.py",
]
for name in support:
    archive(BASE / name, name, compress=name.endswith(".log") or name == "native-final-source-catalog.json")

manifest = {
    "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "method": "Byte-preserving copy or deterministic gzip with mtime=0, no filename header, and compression level 6. Original evidence is unchanged. The decompressed SHA256 verifies each copied source file.",
    "campaign_selection": "Only collection-20261025-v2 supplies comparison results. The original collection-20261025 is a preserved superseded strict pilot; policy revision preceded inspection of timing values, and none of its timings entered the v2 comparison.",
    "excluded_content": "Database fixture directories, Python bytecode caches, binaries, and lock files are omitted. No attempt, report, log, provenance, or collection script is selected by timing.",
    "files": entries, "excluded": excluded,
}
path = DEST / "archive-paths.json"
with path.open("x") as output:
    json.dump(manifest, output, indent=2)
    output.write("\n")
print(json.dumps({"files_copied_or_verified": len(entries), "omitted_paths": len(excluded), "source_bytes": sum(e['source_bytes'] for e in entries), "archive_bytes": sum(e['archive_bytes'] for e in entries)}, indent=2))
