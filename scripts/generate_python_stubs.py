#!/usr/bin/env python3
"""Check the curated Python stub against the stub generated from the PyO3 extension.

`beaconcrypt.pyi` is maintained by hand: the generated stub omits the exception classes made
with `pyo3::create_exception!` (and their `code`/`phase` attributes), the typing-only store
protocols, and the precise argument types. Copying the generated stub over the curated one
would silently drop that public typing, so this script regenerates the raw stub under
`target/generated-stubs` and fails if the curated stub's public API differs from it.
"""

from __future__ import annotations

import ast
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STUB_NAME = "beaconcrypt.pyi"
EXCEPTION_SOURCES = ("beaconcrypt/src/pybinds.rs", "beaconcrypt/src/row_pybinds.rs")
EXCEPTION = re.compile(
    r"create_exception!\(\s*beaconcrypt\s*,\s*(\w+)\s*,\s*(\w+)\s*\)"
)
PYTHON_BASES = {"PyValueError": "ValueError"}
# Generated-only placeholders: the fallback for the uninspected exceptions, and `__ne__`,
# which type checkers derive from `__eq__`.
GENERATED_ONLY = frozenset({"def __getattr__", "SnapshotHead.__ne__"})


def api_surface(text: str) -> set[str]:
    """Return the module's classes with their bases and members, functions and attributes."""
    surface = set()
    for node in ast.parse(text).body:
        if isinstance(node, ast.ClassDef):
            bases = ", ".join(ast.unparse(base) for base in node.bases)
            surface.add(f"class {node.name}({bases})")
            for item in node.body:
                if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    surface.add(f"{node.name}.{item.name}")
                elif isinstance(item, ast.AnnAssign):
                    surface.add(f"{node.name}.{ast.unparse(item.target)}")
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            surface.add(f"def {node.name}")
        elif isinstance(node, ast.AnnAssign):
            surface.add(f"var {ast.unparse(node.target)}")
    return surface


def exception_classes(sources: list[str]) -> dict[str, str]:
    """Map each extension exception class to its Python base class."""
    return {
        name: PYTHON_BASES.get(base, base)
        for source in sources
        for name, base in EXCEPTION.findall(source)
    }


def curated_only_allowed(entry: str, exceptions: dict[str, str]) -> bool:
    """Accept typing-only private protocols and members of the uninspected exceptions."""
    if entry.startswith("class "):
        owner = entry.removeprefix("class ").split("(", 1)[0]
        return (
            owner.startswith("_") or entry == f"class {owner}({exceptions.get(owner)})"
        )
    owner = entry.split(".", 1)[0]
    return owner.startswith("_") or owner in exceptions


def compare(curated: str, generated: str, exceptions: dict[str, str]) -> list[str]:
    """Return the public API differences between the curated and generated stubs."""
    curated_surface = api_surface(curated)
    generated_surface = api_surface(generated)
    problems = [
        f"missing from {STUB_NAME}: {entry}"
        for entry in sorted(generated_surface - curated_surface - GENERATED_ONLY)
    ]
    problems.extend(
        f"not exported by the extension: {entry}"
        for entry in sorted(curated_surface - generated_surface)
        if not curated_only_allowed(entry, exceptions)
    )
    problems.extend(
        f"missing from {STUB_NAME}: class {name}({base})"
        for name, base in sorted(exceptions.items())
        if f"class {name}({base})" not in curated_surface
    )
    return problems


def main() -> int:
    maturin = shutil.which("maturin")
    if maturin is None:
        print("maturin was not found on PATH", file=sys.stderr)
        return 1

    out_dir = ROOT / "target" / "generated-stubs"
    out_dir.mkdir(parents=True, exist_ok=True)
    candidates = (out_dir / STUB_NAME, out_dir / "beaconcrypt" / "__init__.pyi")
    for candidate in candidates:
        candidate.unlink(missing_ok=True)
    subprocess.run(
        [
            maturin,
            "generate-stubs",
            "--manifest-path",
            str(ROOT / "beaconcrypt-ffi" / "Cargo.toml"),
            "--features",
            "pybinds",
            # Introspection needs unstripped symbols; pyproject.toml selects a stripped profile.
            "--profile",
            "dev",
            "--out",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    generated = [candidate for candidate in candidates if candidate.is_file()]
    if len(generated) != 1:
        print("expected exactly one generated extension stub", file=sys.stderr)
        return 1

    exceptions = exception_classes(
        [(ROOT / source).read_text() for source in EXCEPTION_SOURCES]
    )
    problems = compare(
        (ROOT / STUB_NAME).read_text(), generated[0].read_text(), exceptions
    )
    if problems:
        print(f"{STUB_NAME} differs from {generated[0]}:", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
