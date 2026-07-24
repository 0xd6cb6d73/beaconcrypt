#!/usr/bin/env python3
"""Generate Python stubs for the PyO3 extension."""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STUB_NAME = "beaconcrypt.pyi"


def main() -> int:
    maturin = shutil.which("maturin")
    if maturin is None:
        print("maturin was not found on PATH", file=sys.stderr)
        return 1

    out_dir = ROOT / "target" / "generated-stubs"
    out_dir.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [
            maturin,
            "generate-stubs",
            "--features",
            "pybinds",
            "--out",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    generated = out_dir / STUB_NAME
    if not generated.is_file():
        print(f"expected stub was not generated: {generated}", file=sys.stderr)
        return 1

    shutil.copyfile(generated, ROOT / STUB_NAME)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
