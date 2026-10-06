#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Finite syntactic audit supporting the separate protected-term induction.

This is not a ProVerif or computational proof. The accompanying argument proves
why the checked variable conditions imply closure under arbitrary substitution.
"""

from pathlib import Path
import hashlib
import json
import re

PV = Path(__file__).resolve().parent
FILES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
    "registration-set-admission.pvl",
    "registration-provenance.pvl",
    "registration-provenance-wrong-purpose.pvl",
)
BARRIERS = {
    "ed_public": {0},
    "x25519_public": {0},
    "x25519_shared": {0, 1},
    "sign": {1},
}


def term(text):
    tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[(),]", text)
    if "".join(tokens) != re.sub(r"\s+", "", text):
        raise ValueError("unsupported term syntax")
    pos = 0

    def walk():
        nonlocal pos
        if pos >= len(tokens) or not re.fullmatch(
            r"[A-Za-z_][A-Za-z_0-9]*", tokens[pos]
        ):
            raise ValueError("term expected")
        name = tokens[pos]
        pos += 1
        args = []
        if pos < len(tokens) and tokens[pos] == "(":
            pos += 1
            if pos < len(tokens) and tokens[pos] != ")":
                args.append(walk())
                while pos < len(tokens) and tokens[pos] == ",":
                    pos += 1
                    args.append(walk())
            if pos >= len(tokens) or tokens[pos] != ")":
                raise ValueError("unclosed term")
            pos += 1
        return name, tuple(args)

    result = walk()
    if pos != len(tokens):
        raise ValueError("trailing term syntax")
    return result


def exposed_variables(node, variables):
    name, args = node
    if not args and name in variables:
        return {name}
    found = set()
    for position, child in enumerate(args):
        if position not in BARRIERS.get(name, set()):
            found.update(exposed_variables(child, variables))
    return found


def symbols(node):
    name, args = node
    return {name}.union(*(symbols(child) for child in args))


def audit(directory=PV):
    rows = []
    data = []
    hashes = {}
    for filename in FILES:
        raw = (directory / filename).read_bytes()
        hashes[filename] = hashlib.sha256(raw).hexdigest()
        text = re.sub(r"\(\*.*?\*\)", " ", raw.decode(), flags=re.S)
        if re.search(r"\bequation\b", text):
            raise ValueError("new equations require independent analysis")
        declarations = list(
            re.finditer(
                r"\bfun\s+(\w+)\s*\(([^()]*)\)\s*:\s*(\w+)(?:\s*\[([^\]]*)\])?\.?", text
            )
        )
        if len(declarations) != len(re.findall(r"\bfun\s+", text)):
            raise ValueError("unparsed function declaration")
        for decl in declarations:
            attributes = set(re.findall(r"\w+", decl[4] or ""))
            if "data" in attributes:
                if decl[1] in BARRIERS:
                    raise ValueError(
                        "a protected argument must not have a data projection"
                    )
                data.append(
                    {
                        "file": filename,
                        "constructor": decl[1],
                        "arity": len([x for x in decl[2].split(",") if x.strip()]),
                    }
                )
        reductions = list(re.finditer(r"\breduc\s+(.*?)\.", text, flags=re.S))
        if len(reductions) != len(re.findall(r"\breduc\b", text)):
            raise ValueError("unparsed reduction")
        for red in reductions:
            body = red[1].strip()
            variables = set()
            if body.startswith("forall "):
                bindings, body = body[7:].split(";", 1)
                for binding in bindings.split(","):
                    match = re.fullmatch(r"\s*(\w+)\s*:\s*(\w+)\s*", binding)
                    if not match or match[1] in variables:
                        raise ValueError("unsupported or repeated variable binding")
                    variables.add(match[1])
            sides = body.split("=")
            if len(sides) != 2:
                raise ValueError("unsupported reduction equation")
            left, right = map(term, sides)
            if left[0] in BARRIERS:
                raise ValueError("barrier rewritten at its root")
            lhs = exposed_variables(left, variables)
            rhs = exposed_variables(right, variables)
            if not rhs <= lhs:
                raise ValueError(
                    f"{left[0]} exposes formerly protected variables: {rhs-lhs}"
                )
            if "sign" in symbols(right):
                raise ValueError("a reduction creates a signature constructor")
            rows.append(
                {
                    "file": filename,
                    "head": left[0],
                    "lhs_exposed": sorted(lhs),
                    "rhs_exposed": sorted(rhs),
                }
            )
    return {
        "files": hashes,
        "barriers": {k: sorted(v) for k, v in BARRIERS.items()},
        "reductions": rows,
        "data_constructors": data,
        "scope": "Finite syntax conditions only; arbitrary-substitution and source-ledger arguments are separate.",
    }


if __name__ == "__main__":
    result = audit()
    assert len(result["reductions"]) == 28
    print(
        "Checked",
        len(result["reductions"]),
        "reduction rules and",
        len(result["data_constructors"]),
        "data constructors; no equation or signature-creating RHS.",
    )
