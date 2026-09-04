#!/usr/bin/env python3
"""Reproduce the full extracted-operation totality contract surface.

The JSON inventory supplies only theorem names, not propositions. Each proposition is reconstructed from the current generated definition's argument binders. Lean then checks that its certificate proves an unconditional normal return.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9.]*\Z")
DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?def\s+([\w.]+)", re.M)
IDEAL_MODEL_DIGEST = "1666ba5ce4e353f9fecc011dda6f60ae1af9bdd48f66252dc80356adf408e684"


def check_models(proof_root: Path) -> None:
    """Honor the user's immutable-model constraint from starting commit 27ff282."""
    model_root = proof_root / "BeaconcryptCore/Model"
    digest = hashlib.sha256()
    for path in sorted(model_root.rglob("*.lean")):
        digest.update(
            str(path.relative_to(model_root)).encode()
            + b"\0"
            + path.read_bytes()
            + b"\0"
        )
    if digest.hexdigest() != IDEAL_MODEL_DIGEST:
        raise ValueError(
            "ideal PQXDH/ratchet model files changed from the agreed baseline"
        )


def declarations(source: str) -> dict[str, dict[str, str]]:
    matches = list(DECLARATION.finditer(source))
    result = {}
    for index, match in enumerate(matches):
        name = match[1]
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        block = source[match.end() : end].split("/--", 1)[0]
        if ":=" not in block:
            raise ValueError(f"missing body for {name}")
        header = block.split(":=", 1)[0]
        depth = 0
        colon = None
        for offset, character in enumerate(header):
            if character in "({[":
                depth += 1
            elif character in ")}]":
                depth -= 1
            elif character == ":" and depth == 0:
                colon = offset
                break
        if colon is None:
            raise ValueError(f"missing return type for {name}")
        binders, return_type = header[:colon].strip(), header[colon + 1 :].strip()
        monadic = return_type.startswith("RustM ")
        helper = bool(re.search(r"\.closure(?:_\d+)?\.Insts\.", name)) or bool(
            re.search(r"@\[rust_loop(?:_body)?\]", match[0])
        )
        kind = "helper" if helper else "operation" if monadic else "pure"
        arguments = []
        remaining = binders
        while remaining.strip():
            remaining = remaining.lstrip()
            opening = remaining[0]
            if opening not in "({":
                raise ValueError(f"unsupported binder for {name}: {remaining}")
            depth = 0
            for offset, character in enumerate(remaining):
                if character in "({[":
                    depth += 1
                elif character in ")}]":
                    depth -= 1
                    if depth == 0:
                        break
            else:
                raise ValueError(f"unclosed binder for {name}")
            group, remaining = remaining[1:offset], remaining[offset + 1 :]
            variables = group.split(":", 1)[0].split()
            for variable in variables:
                if not NAME.fullmatch(variable):
                    raise ValueError(f"unsupported binder name for {name}: {variable}")
                arguments.append(
                    f"({variable} := {variable})" if opening == "{" else variable
                )
        if name in result:
            raise ValueError(f"duplicate extracted definition: {name}")
        result[name] = {
            "kind": kind,
            "binders": binders,
            "arguments": " ".join(arguments),
        }
    # Generated files currently have no private or mutual declarations. A new
    # format must be reviewed, rather than silently narrowing the inventory.
    code = re.sub(r"/--.*?-/", "", source, flags=re.S)
    if len(re.findall(r"\bdef\s", code)) != len(matches):
        raise ValueError("unparsed generated definition; review the inventory parser")
    return result


def render(definitions: dict, certificates: dict) -> str:
    operations = {
        name
        for name, declaration in definitions.items()
        if declaration["kind"] == "operation"
    }
    if set(certificates) != operations:
        missing = sorted(operations - set(certificates))
        extra = sorted(set(certificates) - operations)
        raise ValueError(
            f"operation coverage differs: missing={missing}, extra={extra}"
        )
    imports = set()
    for name, certificate in certificates.items():
        if set(certificate) != {"module", "theorem", "form"}:
            raise ValueError(f"invalid certificate fields for {name}")
        if not NAME.fullmatch(certificate["module"]) or not NAME.fullmatch(
            certificate["theorem"]
        ):
            raise ValueError(f"invalid certificate name for {name}")
        if certificate["form"] not in {"exists", "equation"}:
            raise ValueError(f"invalid certificate form for {name}")
        imports.add(certificate["module"])
    lines = [f"import {module}" for module in sorted(imports)]
    lines += [
        "",
        "/-! Generated by scripts/check_lean_panic_freedom.py. Every contract is reconstructed from the current extraction. -/",
        "",
        "open CoreModels Aeneas",
        "open Aeneas.Std hiding namespace core alloc",
        "open RustM beaconcrypt_core",
        "",
        "namespace BeaconcryptCore.PanicFreedom.API",
        "",
    ]
    for index, name in enumerate(sorted(operations)):
        declaration, certificate = definitions[name], certificates[name]
        lines += [
            f"-- Extracted operation: {name}",
            f'theorem operation_{index:03d} {declaration["binders"]} :',
            f'    ∃ result, {name} {declaration["arguments"]} = ok result := by',
        ]
        if certificate["form"] == "exists":
            lines += [f'  apply {certificate["theorem"]}']
        else:
            lines += [f'  exact ⟨_, {certificate["theorem"]}⟩']
        lines += [""]
    lines += ["end BeaconcryptCore.PanicFreedom.API", ""]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the reconstructed Lean contract module",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="list the extracted boundary without claiming coverage",
    )
    args = parser.parse_args()
    proof_root = args.root / "beaconcrypt-core/proofs/lean"
    check_models(proof_root)
    definitions = declarations(
        (proof_root / "BeaconcryptCore/Extraction/Funs.lean").read_text()
    )
    if args.list:
        for name, declaration in sorted(definitions.items()):
            print(f'{declaration["kind"]}\t{name}')
        return 0
    certificates = json.loads((proof_root / "panic-freedom.json").read_text())
    expected = render(definitions, certificates)
    target = proof_root / "BeaconcryptCore/PanicFreedom/API.lean"
    if args.write:
        target.write_text(expected)
    elif not target.exists() or target.read_text() != expected:
        raise ValueError(
            "panic-freedom API contracts differ; review and regenerate with --write"
        )
    print(
        f"Checked contract inventory for {len(certificates)} extracted operations; Lean compilation checks the certificates."
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        sys.exit(f"Lean panic-freedom inventory failed: {error}")
