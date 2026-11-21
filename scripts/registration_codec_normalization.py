#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Checked finite control normalization of the original generated registration codec.

Every helper keeps the original operation body. Boolean continuation distribution
uses the explicit source control certificate; singleton copy-in/out forwards the
updated cell even when its Boolean result is ignored. This module does not assume
any parser, serializer, primitive-security or readback law.
"""

from __future__ import annotations
from dataclasses import dataclass
import hashlib, json, re


@dataclass
class Binding:
    source: str
    name: str
    ty: str
    expression: str
    mutable: bool


@dataclass
class Block:
    bindings: list[Binding]
    tail: str


def mask(source):
    out = list(source)
    i = 0
    quoted = False
    line = False
    depth = 0
    while i < len(source):
        pair = source[i : i + 2]
        c = source[i]
        if line:
            if c == "\n":
                line = False
            else:
                out[i] = " "
        elif depth:
            if pair == "/*":
                out[i : i + 2] = "  "
                depth += 1
                i += 1
            elif pair == "*/":
                out[i : i + 2] = "  "
                depth -= 1
                i += 1
            elif c != "\n":
                out[i] = " "
        elif quoted:
            if c == "\\" and i + 1 < len(source):
                out[i : i + 2] = "  "
                i += 1
            elif c == '"':
                out[i] = " "
                quoted = False
            elif c != "\n":
                out[i] = " "
        elif pair == "//":
            out[i : i + 2] = "  "
            line = True
            i += 1
        elif pair == "/*":
            out[i : i + 2] = "  "
            depth = 1
            i += 1
        elif c == '"':
            out[i] = " "
            quoted = True
        i += 1
    if quoted or depth:
        raise ValueError("unterminated source literal/comment")
    return "".join(out)


def close(source, start):
    opening = source[start]
    ending = {"{": "}", "(": ")", "[": "]"}[opening]
    level = 0
    for i in range(start, len(source)):
        if source[i] == opening:
            level += 1
        elif source[i] == ending:
            level -= 1
            if level == 0:
                return i
    raise ValueError("unbalanced delimiter")


def block(source):
    lexical = mask(source)
    brackets = []
    cuts = []
    for i, c in enumerate(lexical):
        if c in "({[":
            brackets.append(c)
        elif c in ")}]":
            if not brackets or brackets.pop() != {")": "(", "]": "[", "}": "{"}[c]:
                raise ValueError("bad delimiter")
        elif c == ";" and not brackets:
            cuts.append(i + 1)
    if brackets:
        raise ValueError("unbalanced block")
    result = []
    start = 0
    for end in cuts:
        text = source[start:end]
        match = re.fullmatch(
            r"\s*let\s+(mut\s+)?([^\s:]+)\s*:\s*(.*?)\s*=\s*(.*);\s*", text, re.S
        )
        if not match:
            result.append(Binding(text, "", "", "", False))
        else:
            result.append(
                Binding(
                    text, match[2], "".join(match[3].split()), match[4], bool(match[1])
                )
            )
        start = end
    tail = source[start:].strip()
    if not tail:
        raise ValueError("missing Boolean tail")
    return Block(result, tail)


def as_block(expression):
    text = expression.strip()
    lex = mask(text)
    if text.startswith("{") and close(lex, 0) == len(text) - 1:
        return block(text[1:-1])
    return block(text)


def conditional(expression):
    text = expression.strip()
    if not re.match(r"^if\b", text):
        return None
    lexical = mask(text)
    depth = 0
    opening = None
    for i in range(2, len(text)):
        c = lexical[i]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif c == "{" and depth == 0:
            opening = i
            break
    if opening is None:
        raise ValueError("missing if branch")
    if text[2:].lstrip().startswith("match "):
        match_end = close(lexical, opening)
        opening = lexical.find("{", match_end + 1)
        if opening < 0:
            raise ValueError("match condition without if branch")
    end = close(lexical, opening)
    condition = text[2:opening].strip()
    yes = text[opening + 1 : end]
    rest = text[end + 1 :].strip()
    if not rest.startswith("else"):
        raise ValueError("Boolean if without else")
    rest = rest[4:].strip()
    if rest.startswith("if"):
        no = rest
    elif rest.startswith("{") and close(mask(rest), 0) == len(rest) - 1:
        no = rest[1:-1]
    else:
        raise ValueError("unsupported else")
    return condition, block(yes), block(no)


class Compiler:
    def __init__(self, parameters=None, result_type="bool", failure="return false;"):
        self.index = 0
        self.certificate = []
        self.parameters = parameters or [
            (
                "pi",
                "[crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1]",
                True,
            )
        ]
        self.result_type = result_type
        self.failure = failure

    def emit(self, current, success="return true;"):
        bindings = list(current.bindings)
        tail = current.tail
        aliases = []
        while (
            bindings and bindings[-1].ty == "bool" and bindings[-1].name == tail.strip()
        ):
            aliases.append(bindings[-1].name)
            tail = bindings.pop().expression
        nested = conditional(tail)
        if nested:
            condition, yes, no = nested
            if (
                bindings
                and bindings[-1].ty == "bool"
                and bindings[-1].name == condition
                and not no.bindings
                and no.tail == "false"
            ):
                binding = bindings.pop()
                token = r"(?<![\w])" + re.escape(binding.name) + r"(?![\w])"
                if re.search(
                    token,
                    mask(yes.tail + "\n" + "".join(x.source for x in yes.bindings)),
                ):
                    raise ValueError("tested binding escapes into continuation")
                name = "extraction_continue_" + str(self.index)
                self.index += 1
                onward = self.emit(yes, success)
                declaration = (
                    "\nlet "
                    + name
                    + " = move |"
                    + ", ".join(
                        ("mut " if mutable else "") + parameter + ": " + ty
                        for parameter, ty, mutable in self.parameters
                    )
                    + "| -> "
                    + self.result_type
                    + " {\n"
                    + onward
                    + "\n};\n"
                )
                result = (
                    "".join(x.source for x in bindings)
                    + declaration
                    + self.emit(
                        as_block(binding.expression),
                        "return "
                        + name
                        + "("
                        + ", ".join(parameter for parameter, _, _ in self.parameters)
                        + ");",
                    )
                )
                self.certificate.append(
                    {
                        "rule": "bind-branch-distribution",
                        "typed_leaf": {
                            "name": binding.name,
                            "type": binding.ty,
                            "source": binding.expression,
                        },
                        "state_parameters": self.parameters,
                        "continuation": name,
                        "aliases": aliases,
                        "output_sha256": hashlib.sha256(result.encode()).hexdigest(),
                    }
                )
                return result
            yes_code = self.emit(yes, success)
            no_code = self.emit(no, success)
            return (
                "".join(x.source for x in bindings)
                + "\nif "
                + condition
                + " {\n"
                + yes_code
                + "\n} else {\n"
                + no_code
                + "\n}\n"
            )
        prefix = "".join(x.source for x in bindings)
        if tail.strip() == "false":
            return prefix + "\n" + self.failure + "\n"
        if tail.strip() == "true":
            return prefix + "\n" + success + "\n"
        return (
            prefix
            + "\nif "
            + tail
            + " {\n"
            + success
            + "\n} else {\n"
            + self.failure
            + "\n}\n"
        )


def normalize_function(source, name):
    found = re.search(r"pub fn " + re.escape(name) + r"\(", source)
    if found is None:
        raise ValueError("missing generated validator")
    start = mask(source).index("{", found.end())
    end = close(mask(source), start)
    original = source[start + 1 : end]
    if "extraction_continue_" in original:
        raise ValueError("reserved source name")
    compiler = Compiler()
    parsed = block(original)
    compiled = compiler.emit(parsed)
    mutable = re.findall(r"\blet\s+mut\s+(\w+)", mask(original))
    if mutable != ["pi"]:
        raise ValueError("unexpected mutable validator state")
    manifest = {
        "function": name,
        "original_sha256": hashlib.sha256(original.encode()).hexdigest(),
        "normalized_sha256": hashlib.sha256(compiled.encode()).hexdigest(),
        "typed_state": "[cbor_raw_iterator;1]",
        "certificate": compiler.certificate,
        "original_body": original,
        "normalized_body": compiled,
    }
    return source[: start + 1] + compiled + source[end:], manifest


def normalize(source):
    manifests = []
    for name in ["validate_initkex", "validate_kexresponse"]:
        source, item = normalize_function(source, name)
        manifests.append(item)
    return source, manifests


def named_dispatcher(source, name):
    found = re.search(r"pub fn " + re.escape(name) + r"\b", source)
    if found is None:
        raise ValueError("missing dispatcher")
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    helpers = []
    counter = 0
    manifest = []

    def fresh(prefix):
        nonlocal counter
        result = "extraction_destruct_" + prefix + "_" + str(counter)
        counter += 1
        return result

    def scalar(expression, ty):
        if re.search(r"(?<!\w)c(?!\w)", mask(expression)):
            raise ValueError("Raw capture in scalar condition")
        helper = fresh("scalar")
        helpers.append(
            "fn " + helper + "(ty: u8) -> " + ty + " {\n" + expression + "\n}\n"
        )
        manifest.append(
            {"kind": "scalar-eta", "function": helper, "type": ty, "source": expression}
        )
        return helper + "(ty)"

    def emit(current, as_helper):
        statements = []
        environment = {"c": "crate::cbordetveraux::cbor_raw<'a>", "ty": "u8"}
        for binding in current.bindings:
            if conditional(binding.expression):
                call = scalar(binding.expression, binding.ty)
                statements.append(
                    binding.source[: binding.source.index("=") + 1] + " " + call + ";\n"
                )
            elif binding.expression.strip().startswith("match "):
                matched = re.match(r"match\s+([^\s{]+)", binding.expression.strip())
                if not matched:
                    raise ValueError("unsupported match operand")
                argument = matched[1]
                argument_type = environment.get(argument)
                if argument_type not in (
                    "crate::cbordetveraux::cbor_raw",
                    "crate::cbordetveraux::cbor_raw<'a>",
                ):
                    raise ValueError(
                        "unsupported outlined match type " + str(argument_type)
                    )
                helper = fresh("match")
                result_type = binding.ty.replace("&[", "&'a [")
                helpers.append(
                    "fn "
                    + helper
                    + "<'a>("
                    + argument
                    + ": crate::cbordetveraux::cbor_raw<'a>) -> "
                    + result_type
                    + " {\n"
                    + binding.expression
                    + "\n}\n"
                )
                manifest.append(
                    {
                        "kind": "typed-match-eta",
                        "function": helper,
                        "parameter": argument,
                        "type": result_type,
                        "source": binding.expression,
                    }
                )
                statements.append(
                    binding.source[: binding.source.index("=") + 1]
                    + " "
                    + helper
                    + "("
                    + argument
                    + ");\n"
                )
            else:
                statements.append(binding.source)
            environment[binding.name] = binding.ty
        prefix = "".join(statements)
        branch = conditional(current.tail)
        if branch:
            condition, yes, no = branch
            body = (
                prefix
                + "\nif "
                + scalar(condition, "bool")
                + " {\n"
                + emit(yes, True)
                + "\n} else {\n"
                + emit(no, True)
                + "\n}\n"
            )
        else:
            body = prefix + "\n" + current.tail + "\n"
        if not as_helper:
            return body
        helper = fresh("branch")
        c = "c" if re.search(r"(?<!\w)c(?!\w)", mask(body)) else "_c"
        ty = "ty" if re.search(r"(?<!\w)ty(?!\w)", mask(body)) else "_ty"
        helpers.append(
            "fn "
            + helper
            + "<'a>("
            + c
            + ": crate::cbordetveraux::cbor_raw<'a>, "
            + ty
            + ": u8) -> cbor_det_view<'a> {\n"
            + body
            + "\n}\n"
        )
        manifest.append(
            {
                "kind": "typed-branch-eta",
                "function": helper,
                "type": "Raw<'a> * u8 -> View<'a>",
                "source": body,
            }
        )
        return helper + "(c, ty)"

    old = source[start + 1 : end]
    new = emit(block(old), False)
    if re.search(r"\blet\s+mut\b", mask(old)):
        raise ValueError("mutable dispatcher capture")
    return source[: start + 1] + new + source[end:] + "\n" + "".join(helpers), {
        "function": name,
        "rule": "typed-named-copy-eta-expansion",
        "original_body": old,
        "normalized_body": new,
        "helpers": manifest,
    }


def outline_parse_checks(source, name):
    found = re.search(
        r"pub\s+fn\s+" + re.escape(name) + r"\s*(?:<[^>]*>)?\s*\(", source
    )
    if found is None:
        raise ValueError("missing parser function")
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    body = source[start + 1 : end]
    masked = mask(body)
    changes = []
    helpers = []
    certificate = []
    for number, match in enumerate(
        re.finditer(r"\blet\s+(_tmp[0-9]*)\s*:\s*bool\s*=", masked)
    ):
        begin = match.end()
        stack = []
        stop = None
        for i in range(begin, len(body)):
            c = masked[i]
            if c in "({[":
                stack.append(c)
            elif c in ")}]":
                stack.pop()
            elif c == ";" and not stack:
                stop = i
                break
        if stop is None:
            raise ValueError("unterminated parse check")
        expression = body[begin:stop]
        branch = conditional(expression)
        if branch is None:
            raise ValueError("nonconditional parse check")
        done = branch[0]
        if not re.fullmatch(r"is_done[0-9]*", done):
            raise ValueError("unexpected parse predicate")
        cells = set(re.findall(r"\b(pc[0-9]*)\s*\[\s*0\s*\]\s*=", mask(expression)))
        if len(cells) != 1:
            raise ValueError("parse check must update exactly one singleton cell")
        cell = cells.pop()
        helper = "extraction_" + name + "_check_" + str(number)
        helpers.append(
            "pub fn "
            + helper
            + "<'a>(mut "
            + cell
            + ": [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw<'a>;1], "
            + done
            + ": bool) -> (bool, [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw<'a>;1]) {\nlet result: bool = "
            + expression
            + ";\n(result, "
            + cell
            + ")\n}\n"
        )
        replacement = (
            "let (extraction_result_"
            + str(number)
            + ", extraction_after_"
            + str(number)
            + ") = crate::transport::"
            + helper
            + "("
            + cell
            + ", "
            + done
            + ");\n"
            + cell
            + " = extraction_after_"
            + str(number)
            + ";\nlet "
            + match[1]
            + ": bool = extraction_result_"
            + str(number)
            + ";"
        )
        changes.append((match.start(), stop + 1, replacement))
        certificate.append(
            {
                "rule": "singleton-copy-in-out-check",
                "function": helper,
                "state_cell": cell,
                "predicate": done,
                "original_expression": expression,
                "original_type": "bool",
                "helper_return_type": "(bool,[Iterator;1])",
            }
        )
    if len(changes) != (5 if name == "parse_initkex" else 7):
        raise ValueError("unexpected parser check count " + str(len(changes)))
    prepared = body
    for left, right, replacement in reversed(changes):
        prepared = prepared[:left] + replacement + prepared[right:]
    return (
        source[: start + 1] + prepared + source[end:],
        helpers,
        {
            "function": name,
            "rule": "typed-parse-check-outlining",
            "original_body": body,
            "normalized_body": prepared,
            "checks": certificate,
        },
    )


def scalarize_shared_cells(source):
    certificates = []
    for function in [
        "cbor_raw_sorted",
        "cbor_validate_det·",
        "cbor_serialized_array_item",
    ]:
        found = re.search(
            r"\bfn\s+" + re.escape(function) + r"\s*(?:<[^>]*>)?\s*\(", source
        )
        if found is None:
            raise ValueError("missing singleton-owner function")
        lexical = mask(source)
        start = lexical.index("{", found.end())
        end = close(lexical, start)
        body = source[start + 1 : end]
        normalized = body
        items = []
        declarations = list(
            re.finditer(
                r"let\s+mut\s+(\w+)\s*:\s*\[&\[u8\];\s*1\]\s*=\s*\[([^;\n]+);\s*1usize\]\s*;",
                body,
            )
        )
        if not declarations:
            raise ValueError("missing singleton shared-slice cells")
        for declaration in declarations:
            cell = declaration[1]
            value = "extraction_scalar_" + cell
            token = r"(?<![\w])" + re.escape(cell) + r"(?![\w])"
            use = r"\(\s*&\s*(?:mut\s+)?" + re.escape(cell) + r"\s*\)\s*\[\s*0\s*\]"
            remaining = body[: declaration.start()] + body[declaration.end() :]
            if re.search(token, re.sub(use, "", mask(remaining))):
                raise ValueError("singleton cell escapes/index differs")
            original = declaration[0]
            replacement = "let mut " + value + ": &[u8] = " + declaration[2] + ";"
            normalized = normalized.replace(original, replacement, 1)
            normalized, count = re.subn(use, value, normalized)
            items.append(
                {
                    "rule": "local-singleton-scalarization",
                    "cell": cell,
                    "scalar": value,
                    "element_type": "&[u8]",
                    "initial": declaration[2],
                    "access_count": count,
                }
            )
        source = source[: start + 1] + normalized + source[end:]
        certificates.append(
            {
                "function": function,
                "original_body": body,
                "normalized_body": normalized,
                "cells": items,
            }
        )
    return source, certificates


def outline_canonical_scans(source):
    function = "cbor_validate_det·"
    found = re.search(
        r"\bfn\s+" + re.escape(function) + r"\s*(?:<[^>]*>)?\s*\(", source
    )
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    body = source[start + 1 : end]
    lexical = mask(body)
    changes = []
    helpers = []
    certificate = []
    for number in range(2):
        suffix = "" if number == 0 else "0"
        pn = "pn" + suffix
        pres = "pres" + suffix
        cond = "cond" + suffix
        check = "check" + str(number + 1)
        begin = lexical.index("let mut " + pn + ":")
        loop = re.search(r"\bwhile\s+" + cond + r"\s*\{", lexical[begin:])
        opening = lexical.index("{", begin + loop.start())
        closing = close(lexical, opening)
        finish = re.match(
            r";\s*let\s+" + check + r"\s*:\s*bool\s*=\s*\(&" + pres + r"\)\[0\];",
            body[closing + 1 :],
        )
        if finish is None:
            raise ValueError("canonical scan terminal changed")
        stop = closing + 1 + finish.end()
        original = body[begin:stop]
        helper = "extraction_canonical_scan_" + str(number)
        helpers.append(
            "fn "
            + helper
            + "(input1: &[u8]) -> bool {\n"
            + original
            + "\n"
            + check
            + "\n}\n"
        )
        changes.append(
            (begin, stop, "let " + check + ": bool = " + helper + "(input1);")
        )
        certificate.append(
            {
                "function": helper,
                "rule": "shared-input-whole-scan-eta",
                "original_body": original,
                "input_type": "&[u8]",
                "return_type": "bool",
            }
        )
    prepared = body
    for left, right, replacement in sorted(changes, reverse=True):
        prepared = prepared[:left] + replacement + prepared[right:]
    return (
        source[: start + 1] + prepared + source[end:] + "\n" + "".join(helpers),
        certificate,
    )


def outline_effectful_branches(source, function, result_type, parameters):
    found = re.search(
        r"\bfn\s+" + re.escape(function) + r"\s*(?:<[^>]*>)?\s*\(", source
    )
    if found is None:
        raise ValueError("missing effectful dispatcher")
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    original = source[start + 1 : end]
    helpers = []
    certificates = []
    index = 0

    def outline(body, environment, top=False):
        nonlocal index
        try:
            parsed = block(body)
            branch = conditional(parsed.tail)
        except ValueError:
            parsed = None
            branch = None
        if branch:
            local = dict(environment)
            for binding in parsed.bindings:
                local[binding.name] = (binding.ty, binding.mutable)
            condition, yes, no = branch
            if condition.startswith("match "):
                predicate_name = (
                    "extraction_predicate_"
                    + re.sub(
                        r"[^A-Za-z0-9_]",
                        lambda match: "u" + match[0].encode().hex(),
                        function,
                    )
                    + "_"
                    + str(index)
                )
                index += 1
                predicate_parameters, predicate_arguments = [], []
                for variable, (ty, mutable) in local.items():
                    if re.search(
                        r"(?<![\w])" + re.escape(variable) + r"(?![\w])",
                        mask(condition),
                    ):
                        if mutable or "&mut" in ty or "&'b mut" in ty:
                            raise ValueError("match predicate captures mutable state")
                        predicate_parameters.append(variable + ": " + ty)
                        predicate_arguments.append(variable)
                helpers.append(
                    "fn "
                    + predicate_name
                    + "<'a, 'b>("
                    + ", ".join(predicate_parameters)
                    + ") -> bool {\n"
                    + condition
                    + "\n}\n"
                )
                certificates.append(
                    {
                        "function": predicate_name,
                        "rule": "typed-pure-match-condition-eta",
                        "original_expression": condition,
                        "parameter_types": predicate_parameters,
                        "return_type": "bool",
                    }
                )
                condition = predicate_name + "(" + ", ".join(predicate_arguments) + ")"
            text = (
                "".join(x.source for x in parsed.bindings)
                + "\nif "
                + condition
                + " {\n"
                + outline("".join(x.source for x in yes.bindings) + yes.tail, local)
                + "\n} else {\n"
                + outline("".join(x.source for x in no.bindings) + no.tail, local)
                + "\n}\n"
            )
        else:
            text = body
        if top:
            return text
        number = index
        index += 1
        name = (
            "extraction_"
            + re.sub(
                r"[^A-Za-z0-9_]", lambda match: "u" + match[0].encode().hex(), function
            )
            + "_branch_"
            + str(number)
        )
        lexical = mask(body)
        arguments = []
        declarations = []
        for variable, (ty, mutable) in environment.items():
            if re.search(r"(?<![\w])" + re.escape(variable) + r"(?![\w])", lexical):
                arguments.append(variable)
                declarations.append(("mut " if mutable else "") + variable + ": " + ty)
        helpers.append(
            "fn "
            + name
            + "<'a, 'b>("
            + ", ".join(declarations)
            + ") -> "
            + result_type
            + " {\n"
            + text
            + "\n}\n"
        )
        certificates.append(
            {
                "function": name,
                "rule": "typed-tail-branch-eta",
                "parameter_types": declarations,
                "source_body": body,
                "normalized_body": text,
                "return_type": result_type,
            }
        )
        return name + "(" + ", ".join(arguments) + ")"

    normalized = outline(original, parameters, True)
    return (
        source[: start + 1] + normalized + source[end:] + "\n" + "".join(helpers),
        certificates,
    )


def eta_canonical_offsets(source):
    certificates = []
    changes = []
    lexical = mask(source)
    for found in re.finditer(r"\blet\s+i\s*:\s*usize\s*=\s*(?=if\b)", lexical):
        begin = found.end()
        depth = []
        stop = None
        for i in range(begin, len(source)):
            c = lexical[i]
            if c in "({[":
                depth.append(c)
            elif c in ")}]":
                depth.pop()
            elif c == ";" and not depth:
                stop = i
                break
        if stop is None:
            raise ValueError("canonical scalar eta expression")
        expression = source[begin:stop]
        for forbidden in ["&mut", "split_at", "[", "let mut"]:
            if forbidden in mask(expression):
                raise ValueError("noncopy scalar eta")
        changes.append((begin, stop, "(move || {\n" + expression + "\n})()"))
        certificates.append(
            {
                "rule": "scalar-usize-eta",
                "original_expression": expression,
                "result_type": "usize",
            }
        )
    if len(changes) != 2:
        raise ValueError("canonical scalar eta roster")
    for begin, end, replacement in reversed(changes):
        source = source[:begin] + replacement + source[end:]
    return source, certificates


def eta_raw_guard(source):
    function = "validate_raw_data_item"
    found = re.search(r"\bfn\s+" + function + r"\s*\(", source)
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    body = source[start + 1 : end]
    found = re.search(r"\blet\s+__anf0\s*:\s*bool\s*=\s*(?=if\b)", mask(body))
    if found is None:
        raise ValueError("missing raw guard")
    begin = found.end()
    text = mask(body)
    stack = []
    stop = None
    for i in range(begin, len(body)):
        c = text[i]
        if c in "({[":
            stack.append(c)
        elif c in ")}]":
            stack.pop()
        elif c == ";" and not stack:
            stop = i
            break
    expression = body[begin:stop]
    if any(x in mask(expression) for x in ["&mut", "poffset", "pres", "pn", "let mut"]):
        raise ValueError("raw guard captures mutable state")
    new = body[:begin] + "(move || {\n" + expression + "\n})()" + body[stop:]
    return source[: start + 1] + new + source[end:], {
        "function": function,
        "rule": "scalar-bool-eta",
        "original_expression": expression,
        "result_type": "bool",
    }


def eta_option_size_matches(source):
    changes = []
    certificates = []
    lexical = mask(source)
    for found in re.finditer(r"\bmatch\s+(?:ser|res)\s*\{", lexical):
        opening = lexical.index("{", found.start())
        ending = close(lexical, opening)
        expression = source[found.start() : ending + 1]
        if "crate::cbordetver::option__size_t::" not in expression:
            continue
        if "crate::cbordetver::option__CBOR" in expression:
            continue
        changes.append(
            (found.start(), ending + 1, "(move || {\n" + expression + "\n})()")
        )
        certificates.append(
            {
                "rule": "option-usize-match-eta",
                "original_expression": expression,
                "result_type": "usize",
            }
        )
    if not changes:
        raise ValueError("missing option-size match eta")
    if any(left[1] > right[0] for left, right in zip(changes, changes[1:])):
        raise ValueError("overlapping scalar match eta")
    for begin, end, replacement in reversed(changes):
        source = source[:begin] + replacement + source[end:]
    return source, certificates


def outline_sorted_scan(source):
    function = "cbor_raw_sorted"
    found = re.search(r"\bfn\s+" + function + r"\s*\(", source)
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    body = source[start + 1 : end]
    first = re.search(r"let mut (?:pkey|extraction_scalar_pkey)\s*:", body)
    if first is None:
        raise ValueError("missing sorted scan state")
    begin = first.start()
    loop = re.search(r"\bwhile\s+cond\s*\{", mask(body[begin:]))
    opening = mask(body).index("{", begin + loop.start())
    closing = close(mask(body), opening)
    finish = re.match(r";\s*\(&pres\)\[0\]", body[closing + 1 :])
    if finish is None:
        raise ValueError("sorted scan terminal changed")
    stop = closing + 1 + finish.end()
    original = body[begin:stop]
    helper = "extraction_sorted_map_scan"
    new = "extraction_sorted_map_scan(hd4, input5, nbpairs)"
    addition = (
        "\nfn "
        + helper
        + "(hd4: &[u8], input5: &[u8], nbpairs: u64) -> bool {\n"
        + original
        + "\n}\n"
    )
    return source[: start + 1] + body[:begin] + new + body[stop:] + source[
        end:
    ] + addition, {
        "rule": "whole-sorted-map-scan-eta",
        "function": helper,
        "original_body": original,
        "parameter_types": ["&[u8]", "&[u8]", "u64"],
        "return_type": "bool",
    }


def normalize_serializer(source, name):
    found = re.search(r"\bfn\s+" + re.escape(name) + r"\s*\(", source)
    lexical = mask(source)
    start = lexical.index("{", found.end())
    end = close(lexical, start)
    body = source[start + 1 : end]
    parsed = block(body)
    if (
        not parsed.bindings
        or parsed.bindings[-1].name != "res"
        or parsed.bindings[-1].ty != "bool"
    ):
        raise ValueError("serializer root Boolean binding changed")
    condition, yes, no = conditional(parsed.tail)
    if condition != "res" or no.bindings or no.tail != "0usize":
        raise ValueError("serializer root rejection changed")
    parameters = [
        ("pcount", "[u64;1]", True),
        ("psize", "[usize;1]", True),
        ("out", "&mut [u8]", False),
    ]
    compiler = Compiler(parameters, "usize", "return 0usize;")
    yesbody = "".join(x.source for x in yes.bindings) + yes.tail
    continuation = (
        "\nlet extraction_serializer_success = move |mut pcount: [u64;1], mut psize: [usize;1], out: &mut [u8]| -> usize {\n"
        + yesbody
        + "\n};\n"
    )
    normalized = (
        "".join(x.source for x in parsed.bindings[:-1])
        + continuation
        + compiler.emit(
            as_block(parsed.bindings[-1].expression),
            "return extraction_serializer_success(pcount, psize, out);",
        )
    )
    return source[: start + 1] + normalized + source[end:], {
        "function": name,
        "rule": "effectful-serializer-Boolean-cps",
        "original_body": body,
        "normalized_body": normalized,
        "state_parameters": parameters,
        "certificate": compiler.certificate,
        "root_expression": parsed.bindings[-1].expression,
        "continuation": yesbody,
    }


def outline_serializer_field_sizes(source):
    certificates = []
    helpers = []
    for function in ["serialize_initkex", "serialize_kexresponse"]:
        found = re.search(r"\bfn\s+" + function + r"\s*\(", source)
        lexical = mask(source)
        start = lexical.index("{", found.end())
        end = close(lexical, start)
        body = source[start + 1 : end]
        lexical = mask(body)
        changes = []
        for number, found in enumerate(
            re.finditer(r"\blet\s+(\w+)\s*:\s*usize\s*=\s*(?=if\b)", lexical)
        ):
            begin = found.end()
            stack = []
            stop = None
            for i in range(begin, len(body)):
                c = lexical[i]
                if c in "({[":
                    stack.append(c)
                elif c in ")}]":
                    stack.pop()
                elif c == ";" and not stack:
                    stop = i
                    break
            expression = body[begin:stop]
            candidates = set(re.findall(r"\bc[0-9]+\b", mask(expression))) - {"c3"}
            if len(candidates) != 1 or conditional(expression)[0] != "lo_ok && hi_ok":
                raise ValueError("serializer field-size environment changed")
            payload = candidates.pop()
            helper = "extraction_" + function + "_size_" + str(number)
            helpers.append(
                "fn "
                + helper
                + "<'a, 'b>("
                + payload
                + ": &'a [u8], out1: &'b mut [u8], lo_ok: bool, hi_ok: bool) -> usize {\n"
                + expression
                + "\n}\n"
            )
            changes.append(
                (begin, stop, helper + "(" + payload + ", out1, lo_ok, hi_ok)")
            )
            certificates.append(
                {
                    "rule": "mutable-output-field-size-eta",
                    "function": helper,
                    "payload": payload,
                    "original_expression": expression,
                    "parameter_types": ["&'a[u8]", "&'b mut[u8]", "bool", "bool"],
                    "return_type": "usize",
                }
            )
        if len(changes) != 4:
            raise ValueError("serializer fixed-field-size roster changed")
        for left, right, replacement in reversed(changes):
            body = body[:left] + replacement + body[right:]
        source = source[: start + 1] + body + source[end:]
    return source + "\n" + "".join(helpers), certificates


def outline_rotation_indices(source):
    changes, helpers, certificates = [], [], []
    lexical = mask(source)
    for number, found in enumerate(
        re.finditer(r"\blet\s+idx·\s*:\s*usize\s*=\s*(?=if\b)", lexical)
    ):
        begin = found.end()
        stack = []
        for end in range(begin, len(source)):
            c = lexical[end]
            if c in "({[":
                stack.append(c)
            elif c in ")}]":
                stack.pop()
            elif c == ";" and not stack:
                break
        expression = source[begin:end]
        lengths = set(re.findall(r"\b(\w+)\.len\(\)", expression))
        if len(lengths) != 1:
            raise ValueError("rotation slice-length roster changed")
        buffer = lengths.pop()
        normalized = expression.replace(buffer + ".len()", "length")
        offsets = sorted(set(re.findall(r"\b(?:off[0-9]*|soff|i[0-9]+)\b", normalized)))
        if not offsets:
            raise ValueError("rotation offset roster changed")
        helper = "extraction_rotation_index_" + str(number)
        helpers.append(
            "fn "
            + helper
            + "(idx: usize, length: usize, "
            + ", ".join(offset + ": usize" for offset in offsets)
            + ") -> usize {\n"
            + normalized
            + "\n}\n"
        )
        changes.append(
            (
                begin,
                end,
                helper + "(idx, " + buffer + ".len(), " + ", ".join(offsets) + ")",
            )
        )
        certificates.append(
            {
                "rule": "scalar-rotation-index-eta",
                "function": helper,
                "original_expression": expression,
                "normalized_body": normalized,
                "parameter_types": ["usize", "usize", "usize"],
                "return_type": "usize",
            }
        )
    if len(changes) != 5:
        raise ValueError("rotation arithmetic roster changed")
    for begin, end, replacement in reversed(changes):
        source = source[:begin] + replacement + source[end:]
    return source + "\n" + "".join(helpers), certificates


def outline_rotation_inner_loops(source):
    lexical = mask(source)
    changes, helpers, certificates = [], [], []
    for number, found in enumerate(
        re.finditer(r"let\s+mut\s+pj\s*:\s*\[usize;\s*1\]\s*=", lexical)
    ):
        begin = found.start()
        loop = re.search(r"\bwhile\s+(cond[0-9]*)\s*\{", lexical[begin:])
        if loop is None:
            raise ValueError("missing inner rotation loop")
        opening = lexical.index("{", begin + loop.start())
        closing = close(lexical, opening)
        finish = re.match(
            r";\s*let\s+idx\s*:\s*usize\s*=\s*\(&pidx\)\[0\];", source[closing + 1 :]
        )
        if finish is None:
            raise ValueError("rotation loop terminal changed")
        stop = closing + 1 + finish.end()
        original = source[begin:stop]
        arrays = sorted(set(re.findall(r"\b(\w+)\[idx(?:·)?\]", original)))
        if len(arrays) != 1:
            raise ValueError("rotation mutable-output roster changed")
        buffer = arrays.pop()
        scalars = sorted(
            set(re.findall(r"\b(?:off[0-9]*|soff|i[0-9]*|q[0-9]*)\b", original))
        )
        helper = "extraction_rotation_inner_" + str(number)
        element_type = "cbor_map_entry<'a>" if buffer == "ac1" else "u8"
        parameters = [buffer + ": &mut [" + element_type + "]"] + [
            value + ": usize" for value in scalars
        ]
        helpers.append(
            "fn "
            + helper
            + "<'a>("
            + ", ".join(parameters)
            + ") -> usize {\n"
            + original
            + "\nidx\n}\n"
        )
        replacement = (
            "let idx: usize = " + helper + "(" + ", ".join([buffer] + scalars) + ");"
        )
        changes.append((begin, stop, replacement))
        certificates.append(
            {
                "rule": "mutable-output-whole-inner-loop-eta",
                "function": helper,
                "parameter_types": parameters,
                "original_body": original,
                "return_type": "usize",
            }
        )
    if len(changes) != 5:
        raise ValueError("inner rotation loop roster changed")
    for begin, end, replacement in reversed(changes):
        source = source[:begin] + replacement + source[end:]
    return source + "\n" + "".join(helpers), certificates


def compose_option_projection_matches(source):
    changes, certificates = [], []
    lexical = mask(source)
    for found in re.finditer(r"\bmatch\s+match\s+", lexical):
        inner_start = lexical.index("match", found.start() + len("match"))
        inner_open = lexical.index("{", inner_start)
        inner_end = close(lexical, inner_open)
        outer_open = lexical.find("{", inner_end + 1)
        if outer_open < 0:
            raise ValueError("missing outer option projection match")
        outer_end = close(lexical, outer_open)
        inner = source[inner_start : inner_end + 1]
        match = re.fullmatch(
            r"match\s+([^\s{]+)\s*\{\s*(cbor_raw::CBOR_Case_(?:Array|Map)\s*\{\s*v:\s*[A-Za-z_0-9·]+\s*\})\s*=>\s*([A-Za-z_0-9·]+)::Some\s*\{\s*v:\s*([^{}]+)\s*\},\s*_\s*=>\s*\3::None\s*\}",
            inner,
            re.S,
        )
        if match is None:
            continue
        outer = source[outer_open + 1 : outer_end]
        arms = re.fullmatch(
            r"\s*"
            + re.escape(match[3])
            + r'::Some\s*\{\s*v\s*\}\s*=>\s*v\s*,\s*_\s*=>\s*(panic!\("Incomplete pattern matching"\))\s*',
            outer,
            re.S,
        )
        if arms is None:
            raise ValueError("option projection outer arms changed")
        original = source[found.start() : outer_end + 1]
        normalized = (
            "match "
            + match[1]
            + " {\n"
            + match[2]
            + " => "
            + match[4].strip()
            + ",\n_ => "
            + arms[1]
            + "\n}"
        )
        changes.append((found.start(), outer_end + 1, normalized))
        certificates.append(
            {
                "rule": "pure-option-projection-match-composition",
                "original_expression": original,
                "normalized_expression": normalized,
                "source_constructor": match[2],
                "projection": match[4].strip(),
                "otherwise": arms[1],
            }
        )
    if len(changes) != 4:
        raise ValueError(
            "option array/map projection roster changed: " + str(len(changes))
        )
    for begin, end, replacement in reversed(changes):
        source = source[:begin] + replacement + source[end:]
    return source, certificates
