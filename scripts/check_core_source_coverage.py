#!/usr/bin/env python3
"""Fail closed when handwritten core library code is absent from its LLBC extraction.

This checks source coverage, not the correctness of Charon/Aeneas or native generated trait implementations. Native-only derives are an explicit, pinned boundary. Unit-test-only items are outside the published library; the test-utils library feature is included.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int


@dataclass(frozen=True)
class Function:
    name: str
    start: int
    name_start: int
    end: int


def tokens(source: str) -> list[Token]:
    """Tokenize relevant Rust syntax without interpreting comments or literals as code."""
    result = []
    offset = 0
    while offset < len(source):
        start = offset
        if source[offset].isspace():
            offset += 1
            continue
        if source.startswith("//", offset):
            newline = source.find("\n", offset)
            offset = len(source) if newline < 0 else newline + 1
            continue
        if source.startswith("/*", offset):
            depth = 1
            offset += 2
            while depth and offset < len(source):
                if source.startswith("/*", offset):
                    depth += 1
                    offset += 2
                elif source.startswith("*/", offset):
                    depth -= 1
                    offset += 2
                else:
                    offset += 1
            if depth:
                raise ValueError("unterminated Rust block comment")
            continue
        raw = re.match(r'(?:br|cr|r)(#{0,255})"', source[offset:])
        if raw:
            end = source.find('"' + raw[1], offset + raw.end())
            if end < 0:
                raise ValueError("unterminated Rust raw string")
            offset = end + 1 + len(raw[1])
        elif source[offset] == '"' or source.startswith(('b"', 'c"'), offset):
            offset += 1 if source[offset] == '"' else 2
            while offset < len(source):
                if source[offset] == "\\":
                    offset += 2
                elif source[offset] == '"':
                    offset += 1
                    break
                else:
                    offset += 1
            else:
                raise ValueError("unterminated Rust string")
        elif character := re.match(
            r"(?:b)?'(?:\\(?:u\{[0-9a-fA-F_]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'",
            source[offset:],
        ):
            offset += character.end()
        elif word := re.match(
            r"(?:r#)?[A-Za-z_][A-Za-z_0-9]*|[0-9][A-Za-z_0-9]*", source[offset:]
        ):
            offset += word.end()
        else:
            offset += 1
        result.append(Token(source[start:offset], start, offset))
    return result


def fingerprint(items: list[Token]) -> str:
    return hashlib.sha256("\0".join(token.text for token in items).encode()).hexdigest()


# Filled from reviewed, native-only generated implementations. These are not Lean certificates.
# Key: source path and declared type (or native import); value: complete item token digest.
NATIVE_BOUNDARY: dict[tuple[str, str], str] = {
    (
        "beaconcrypt-core/src/authentication.rs",
        "AuthRole",
    ): "bae6574b64fc72d0941a4e623c38e21fe5b6be743c114469b113e7e451130bf1",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconAborted",
    ): "84efbef48f1e424855ed851b8a6c01d4db29c57c0155ae6e4d29a810d40af738",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconCoins",
    ): "347fa7bde7d858ca27d164d2a8297791a18fdbe476553f921d37d1e2cd635506",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconEstablished",
    ): "ba1283185d31123c19701b63d1b9cbe923c7f3d3cff5b71946bf961fe7daf059",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconFresh",
    ): "84367488e405c493240ebd7d8b9d2483108983b7642bb8a775d13e357d20de60",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconInitSent",
    ): "c95091a5343fa8a576cd44d7e7fd4e7f3ff3dcf01c2311075937af1b874800f7",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconStart",
    ): "5e001f4d8b173609f6e2e0d5809be6f400e53e12b2b4a46d5de62014baa494c9",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "BeaconStartInputs",
    ): "e2001f1cb675600b9351f62bb20bed28bd6a88d3a6484ec2081cd4f62de2b818",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "InitKex",
    ): "6d4f92334886ea147fd1417a1cb37a4059bfff32cf0938896694070a9225f734",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "KeyIdAvailability",
    ): "9f520c80c3667d8f880e81d6bc0a2791d5fc87a66b555c95a88828ac1f423e45",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "PqxdhSharedSecrets",
    ): "edfa675daeb5a0ce021febdcd977a5994f583cae84ccfc55494704b958710bc3",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "RatchetInitialization",
    ): "c48570367782c7389d5da12712272a2341b8d9adcddf450c6613398120e5d907",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "RegistrationError",
    ): "ec2eebefca43773fa2caefc979e8350ef4b4106584bdfcb2c3b7584d0087a9e3",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "RegistrationId",
    ): "01ef0632b1fe369071f5f4388f10cc48dd3e2a4afbc30a181a4f1fa03a8cb3dd",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "RegistrationKeyIdBinding",
    ): "d71ac36865ae924b99e77f838935078ee9a26c20ff929a7ca794124d3a3bd02d",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "RegistrationStatus",
    ): "56fd8affda0b4c0eb0380fba8135f79d773f5cc10eb8f92a7f707379fb690bcb",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "RootKeyInput",
    ): "8d392bc02c03f798e14692cbba28a68b031e5c5f9753659080e34c4a9e325e38",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "ServerBinding",
    ): "06433749888f607ca2b755b91d2752822c3804e8ba4c76f942b5b1212bf83d63",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "ServerCoins",
    ): "abe324e087281cc959d874a9521cd1cfc84ad8acbc7d92e53186f9aa28a7fc15",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "ServerState",
    ): "0349fd51b18057c35c6dea1ede790578c85cc65552b29544d6ef778ef316826a",
    (
        "beaconcrypt-core/src/pqxdh.rs",
        "VerifiedInitKex",
    ): "d425d1acceeeb06c1b234c253294c2e1fd092084310421968e4997b1b37007c1",
    (
        "beaconcrypt-core/src/pqxdh/concrete.rs",
        "InitialRatchetKdfResponse",
    ): "3298fe94da1210ed62e0d91b57f0f2d94e926012359a688b2e7ca83607bbddbe",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "RatchetChain",
    ): "f7756e246e392611479b6ee79bd2619f9ad9cdb05bcbdd294218c0335198bd06",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "RatchetKdfResponse",
    ): "b96cc940e161839edfa87d232fd9d1a9510531af5c36a768d3ffbabf9647ff08",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "RatchetKey",
    ): "b6596f86eec00d91d5880537e7709de2f5c7b7fdd284a9e3089ac8a9df723b3e",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "RatchetMaterial",
    ): "538371784fda191d79a9923a074929340505e54016db6e3e3d5fdb3783f249fc",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "RatchetNonce",
    ): "fe2a68465ff1d08039afc277fadea639e01265ade8904f81d20cb8c620911813",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "SymmetricRatchetKdfRequest",
    ): "a8ec4815465ae944375af84a895f13a5b3a0a0abfc4ea0d823655ccf69e2083f",
    (
        "beaconcrypt-core/src/ratchet.rs",
        "native-import",
    ): "17e14dc473840289485d5024ed5c9e6d4f3a14bbedf82c572d6b43fcba117e08",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "PeerRatchetState",
    ): "8c339703e353dfa1f6484c3cda674b2036696ccde20d84e8826877020a5c2993",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "PeerSendAdvance",
    ): "965e7304edb665228536e18a35627b3f6f13f6d48ebb39bcddfd85c67e7a7658",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "RatchetRestore",
    ): "a46a9e5dedbfca8184e95364f7b2f6d2c3bf11c8fe687d1dd13db03f45c93d8f",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "RatchetState",
    ): "16f36e4a7a745006c30d340a779c1c041635a01ab3d4f77eaddc84eed0ed9601",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveAdvance",
    ): "a2fe0e350144e0cfb7b0fba7ba3f5da5509b7ee163be169c4465f68b96b31d50",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveDisposition",
    ): "da3bcce2a697972a8bbb83142c93116130ee2a7323bef522d29c7f0af963ae26",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveFinish",
    ): "913fc50bb039f957af1518315508844b53aa9fae15048f83586b3c54d099f0bf",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveFinishWithRemoval",
    ): "932c9d9a33ae057d72abe4577a00b44e51e33c474803d9b9e6924776747a8b59",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceivePlan",
    ): "ea285f882600ab1a8039ecbe87f9ee430a87d70c355147cfbf1085c5bbbc058c",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveRemoval",
    ): "fc5d75dd713707d39a229555fa83b063878eff2c8d16b91dcfd81cc979a24a06",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveRestoreStep",
    ): "cc3f0fbf4664d11c9b847a4788da17e4d1385b0c57272fc974dc43f45bbde633",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "ReceiveTargetAdvance",
    ): "4c3417f77c56d280dea4b4125ab568294d7a0ae6bc5a5c9ed534178c63596db7",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "SendAdvance",
    ): "cda16f6c91f7bb2f8f5fad12eef1b5b31dc7a050e3f60f48339a72612338d97f",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "SendFinish",
    ): "9bbb7f1d2727d1361927e0cadfe9df1444e4bea54b42c173a67925067d15dfff",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "SendKey",
    ): "6b1862cbbbccc0c1e38287382a261b8a01f443939c47afaa1724ddc4ba9b4780",
    (
        "beaconcrypt-core/src/ratchet/control.rs",
        "SequenceCache",
    ): "4c02d2e90b45cd92b3ff3ac63e40445fe261a67747656adab475b66b633fefd4",
}


class Scanner:
    def __init__(self, source: str, path: str):
        self.source = source
        self.path = path
        self.tokens = tokens(source)
        self.pairs: dict[int, int] = {}
        stack = []
        for index, token in enumerate(self.tokens):
            if token.text in {"(", "[", "{"}:
                stack.append(index)
            elif token.text in {")", "]", "}"}:
                if (
                    not stack
                    or self.tokens[stack[-1]].text
                    != {")": "(", "]": "[", "}": "{"}[token.text]
                ):
                    raise ValueError(f"unbalanced Rust delimiters in {path}")
                opening = stack.pop()
                self.pairs[opening] = index
        if stack:
            raise ValueError(f"unclosed Rust delimiter in {path}")
        self.functions: list[Function] = []
        self.native: dict[tuple[str, str], str] = {}

    def text(self, start: int, end: int) -> str:
        return "".join(token.text for token in self.tokens[start:end])

    def attributes(self, index: int, end: int) -> tuple[int, list[str]]:
        attributes = []
        while index < end and self.tokens[index].text == "#":
            index += 1
            if self.tokens[index].text == "!":
                index += 1
            if self.tokens[index].text != "[":
                raise ValueError(f"unsupported Rust attribute in {self.path}")
            close = self.pairs[index]
            attributes.append(self.text(index + 1, close))
            index = close + 1
        return index, attributes

    def conditions(self, attributes: list[str]) -> tuple[bool, bool]:
        native = False
        for attribute in attributes:
            if attribute == "cfg(test)":
                return False, False
        for attribute in attributes:
            if attribute == 'cfg(any(test,feature="test-utils"))':
                continue
            if attribute == "cfg(not(hax_compilation))":
                native = True
            elif attribute.startswith("cfg_attr(not(hax_compilation),derive("):
                native = True
            elif attribute == (
                'cfg_attr(feature="proverif",hax_lib::decreases('
                "hax_lib::int::ToInt::to_int(remaining)))"
            ) or re.fullmatch(
                r'cfg_attr\(feature="proverif",hax_lib::proverif::replace\("(?:[^"\\]|\\.)*"\)\)',
                attribute,
                flags=re.S,
            ):
                # These attributes affect the separate ProVerif backend only.
                continue
            elif attribute in {"no_std", "forbid(unsafe_code)", "must_use"}:
                continue
            elif attribute.startswith(("doc(", "doc=", "allow(", "must_use=")):
                continue
            elif attribute in {"derive(Clone,Copy)", "derive(Clone)"}:
                continue
            else:
                raise ValueError(
                    f"unreviewed Rust attribute in {self.path}: {attribute}"
                )
        return True, native

    def terminator(self, index: int, end: int) -> int:
        """Find an item's top-level body or semicolon, ignoring nested binders."""
        while index < end:
            text = self.tokens[index].text
            if text in {"{", ";"}:
                return index
            if text in {"(", "["}:
                index = self.pairs[index] + 1
            else:
                index += 1
        raise ValueError(f"unterminated Rust item in {self.path}")

    def body(self, index: int, end: int, *, constant: bool = False) -> None:
        """Inspect attributes/macros and nested functions in expression scopes."""
        while index < end:
            text = self.tokens[index].text
            if text == "#":
                after, attrs = self.attributes(index, end)
                if attrs != ['cfg(feature="proverif")']:
                    raise ValueError(
                        f"unreviewed body attribute in {self.path}: {attrs}"
                    )
                terminator = next(
                    (i for i in range(after, end) if self.tokens[i].text == ";"), end
                )
                invocation = self.text(after, terminator)
                if not re.fullmatch(
                    r"hax_lib::loop_decreases!\((?:left|remaining)asusize\)", invocation
                ):
                    raise ValueError(f"unreviewed conditional body in {self.path}")
                index = terminator + 1
                continue
            if (
                text == "fn"
                and index + 1 < end
                and re.fullmatch(r"(?:r#)?[A-Za-z_]\w*", self.tokens[index + 1].text)
            ):
                close = self.terminator(index + 2, end)
                if self.tokens[close].text != "{":
                    raise ValueError(f"bodyless nested function in {self.path}")
                last = self.pairs[close]
                self.functions.append(
                    Function(
                        self.tokens[index + 1].text,
                        self.tokens[index].start,
                        self.tokens[index + 1].start,
                        self.tokens[last].end,
                    )
                )
                self.body(close + 1, last)
                index = last + 1
                continue
            if (
                text == "!"
                and index > 0
                and re.fullmatch(r"(?:r#)?[A-Za-z_]\w*", self.tokens[index - 1].text)
                and index + 1 < end
                and self.tokens[index + 1].text in {"(", "[", "{"}
            ):
                name = self.tokens[index - 1].text
                if name not in {"matches", "if", "while", "return"} and not (
                    constant and name == "assert"
                ):
                    raise ValueError(f"unreviewed Rust macro in {self.path}")
            index += 1

    def items(self, index: int, end: int) -> None:
        modules = set()
        while index < end:
            item_start = index
            index, attrs = self.attributes(index, end)
            if index == end:
                self.conditions(attrs)
                return
            # Crate inner attributes are followed by another item/attribute.
            if attrs and self.tokens[item_start + 1].text == "!":
                self.conditions(attrs)
                continue
            enabled, native = self.conditions(attrs)
            start = index
            if self.tokens[index].text == "pub":
                index += 1
                if self.tokens[index].text == "(":
                    index = self.pairs[index] + 1
            kind = self.tokens[index].text
            if kind == "const" and self.tokens[index + 1].text == "fn":
                index += 1
                kind = "fn"
            if kind not in {
                "fn",
                "impl",
                "mod",
                "struct",
                "enum",
                "use",
                "const",
                "static",
                "type",
                "extern",
            }:
                raise ValueError(f"unparsed Rust item in {self.path}: {kind}")
            terminator = self.terminator(index + 1, end)
            has_body = self.tokens[terminator].text == "{"
            last = self.pairs[terminator] if has_body else terminator
            # Use imports can contain a brace group before their semicolon.
            if kind in {"use", "const", "static", "type", "extern"} and has_body:
                cursor = last + 1
                while cursor < end and self.tokens[cursor].text != ";":
                    if self.tokens[cursor].text in {"{", "(", "["}:
                        cursor = self.pairs[cursor] + 1
                    else:
                        cursor += 1
                if cursor == end:
                    raise ValueError(f"unterminated Rust {kind} item in {self.path}")
                last = cursor
            if enabled:
                if kind == "extern":
                    raise ValueError(f"unreviewed external Rust item in {self.path}")
                if kind == "mod":
                    modules.add(self.tokens[index + 1].text)
                if kind == "use" and not native:
                    root = self.tokens[index + 1].text
                    public = self.tokens[start].text == "pub"
                    allowed = {"crate"} | modules
                    if not public:
                        allowed |= {"self", "super"}
                    if root not in allowed:
                        raise ValueError(
                            f"unreviewed external import or reexport in {self.path}: {root}"
                        )
                if kind in {"const", "static"} and self.tokens[start].text == "pub":
                    if any(
                        token.text == "fn"
                        for token in self.tokens[index + 1 : terminator]
                    ):
                        raise ValueError(
                            f"unreviewed exported function pointer in {self.path}"
                        )
                if kind == "type" and any(
                    token.text == "fn" for token in self.tokens[index + 1 : last]
                ):
                    raise ValueError(
                        f"unreviewed function-pointer type alias in {self.path}"
                    )
                if native:
                    name = (
                        self.tokens[index + 1].text
                        if kind in {"struct", "enum"}
                        else "native-import"
                    )
                    if kind not in {"struct", "enum", "use"}:
                        raise ValueError(f"native-only handwritten item in {self.path}")
                    key = self.path, name
                    if key in self.native:
                        raise ValueError(f"duplicate native boundary item: {key}")
                    self.native[key] = fingerprint(self.tokens[item_start : last + 1])
                if kind == "fn":
                    if not has_body:
                        raise ValueError(f"bodyless library function in {self.path}")
                    name = self.tokens[index + 1]
                    self.functions.append(
                        Function(
                            name.text,
                            self.tokens[start].start,
                            name.start,
                            self.tokens[last].end,
                        )
                    )
                    self.body(index + 2, terminator)
                    self.body(terminator + 1, last)
                elif kind in {"impl", "mod"} and has_body:
                    self.body(index + 1, terminator)
                    self.items(terminator + 1, last)
                elif kind in {"struct", "enum", "type", "use", "extern"}:
                    self.body(index + 1, last)
                elif kind in {"const", "static"}:
                    self.body(index + 1, last, constant=True)
            index = last + 1
            if index < end and self.tokens[index].text == ";":
                index += 1

    def scan(self) -> tuple[list[Function], dict[tuple[str, str], str]]:
        self.items(0, len(self.tokens))
        return self.functions, self.native


def source_offset(source: str, position: dict) -> int:
    lines = source.splitlines(keepends=True)
    line, col = position["line"], position["col"]
    if not 1 <= line <= len(lines) or col < 0:
        raise ValueError("invalid LLBC source position")
    # Charon's emitted columns expand a hard tab to four columns.
    current = 0
    for offset, character in enumerate(lines[line - 1]):
        if current == col:
            return sum(map(len, lines[: line - 1])) + offset
        current += 4 if character == "\t" else 1
        if current > col:
            raise ValueError("LLBC source position is inside a tab")
    if current == col:
        return sum(map(len, lines[: line - 1])) + len(lines[line - 1])
    raise ValueError("invalid LLBC source position")


def sources_and_functions(
    root: Path,
) -> tuple[dict[str, str], dict[str, list[Function]]]:
    sources = {
        str(path.relative_to(root)): path.read_bytes().decode("utf-8")
        for path in sorted((root / "beaconcrypt-core/src").rglob("*.rs"))
    }
    functions = {}
    native = {}
    for path, source in sources.items():
        functions[path], boundaries = Scanner(source, path).scan()
        native.update(boundaries)
    if native != NATIVE_BOUNDARY:
        raise ValueError(
            "native generated trait/import boundary changed; review its pinned inventory"
        )
    return sources, functions


def artifact_hashes(root: Path) -> dict[str, str]:
    proof_root = root / "beaconcrypt-core/proofs/lean"
    paths = [proof_root / "BeaconcryptCore/Extraction.lean"]
    paths += sorted((proof_root / "BeaconcryptCore/Extraction").rglob("*.lean"))
    if len(paths) < 3:
        raise ValueError("missing Lean extraction artifacts")
    return {
        str(path.relative_to(proof_root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in paths
    }


def function_inventory(functions: dict[str, list[Function]]) -> list[dict]:
    return [
        {
            "file": path,
            "name": function.name,
            "start": function.start,
            "name_start": function.name_start,
            "end": function.end,
        }
        for path, entries in functions.items()
        for function in entries
    ]


def lean_definition_spans(source: str) -> list[tuple[str, str, dict, dict]]:
    """Bind genuine generated doc comments to immediately following definitions."""
    code = list(source)
    comments = []
    offset = 0
    while offset < len(source):
        start = offset
        if source.startswith("--", offset):
            newline = source.find("\n", offset)
            offset = len(source) if newline < 0 else newline
        elif source.startswith("/-", offset):
            depth = 1
            offset += 2
            while depth and offset < len(source):
                if source.startswith("/-", offset):
                    depth += 1
                    offset += 2
                elif source.startswith("-/", offset):
                    depth -= 1
                    offset += 2
                else:
                    offset += 1
            if depth:
                raise ValueError("unterminated Lean comment in extraction")
            if source.startswith("/--", start):
                comments.append((start, offset, source[start:offset]))
        elif source[offset] == '"':
            offset += 1
            while offset < len(source):
                if source[offset] == "\\":
                    offset += 2
                elif source[offset] == '"':
                    offset += 1
                    break
                else:
                    offset += 1
            else:
                raise ValueError("unterminated Lean string in extraction")
        else:
            offset += 1
            continue
        for index in range(start, offset):
            if code[index] != "\n":
                code[index] = " "
    masked = "".join(code)
    result = []
    for definition in re.finditer(
        r"^(?:@\[[^\]]*\]\s*)?def\s+([\w.]+)", masked, flags=re.M
    ):
        previous = [comment for comment in comments if comment[1] <= definition.start()]
        if not previous:
            continue
        _, end, comment = previous[-1]
        if source[end : definition.start()].strip():
            continue
        metadata = re.search(
            r"Source: '([^']+)', lines (\d+):(\d+)-(\d+):(\d+)", comment
        )
        if metadata:
            path, first, first_col, last, last_col = metadata.groups()
            result.append(
                (
                    definition[1],
                    path,
                    {"line": int(first), "col": int(first_col)},
                    {"line": int(last), "col": int(last_col)},
                )
            )
    return result


def check_lean_spans(
    root: Path, sources: dict[str, str], functions: dict[str, list[Function]]
) -> None:
    source = (
        root / "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean"
    ).read_text()
    spans = []
    for name, path, first, last in lean_definition_spans(source):
        if path in sources:
            start = source_offset(sources[path], first)
            end = source_offset(sources[path], last)
            spans.append((name.split(".")[-1], path, start, end))
    for path, entries in functions.items():
        for function in entries:
            if not any(
                function.name == name
                and path == p
                and function.start <= start <= function.name_start
                and function.end == end
                for name, p, start, end in spans
            ):
                raise ValueError(
                    f"handwritten library function absent from Lean extraction: {path} {function.name}"
                )


# All semantic extraction settings are reviewed; only the output filename may vary.
EXPECTED_OPTIONS = {
    "abort_on_error": False,
    "consts": None,
    "deallocate_all_locals": True,
    "dest_dir": None,
    "desugar_drops": False,
    "duplicate_defaulted_methods": False,
    "error_on_warnings": False,
    "exclude": [],
    "extract_opaque_bodies": False,
    "format": None,
    "hide_allocator": True,
    "hide_marker_traits": True,
    "include": [],
    "index_to_function_calls": True,
    "lift_associated_types": ["*"],
    "mir": None,
    "monomorphize": False,
    "monomorphize_mut": None,
    "no_dedup_serialized_ast": False,
    "no_gen_tuple_structs": True,
    "no_normalize": False,
    "no_reorder_decls": False,
    "no_serialize": False,
    "no_typecheck": False,
    "opaque": [],
    "ops_to_function_calls": True,
    "precise_drops": False,
    "preset": "Aeneas",
    "print_built_llbc": False,
    "print_llbc": False,
    "print_original_ullbc": False,
    "print_ullbc": False,
    "raw_consts": False,
    "reconstruct_asserts": True,
    "reconstruct_fallible_operations": True,
    "reconstruct_matches": True,
    "remove_adt_clauses": True,
    "remove_unused_clauses": False,
    "remove_unused_self_clauses": True,
    "rustc_args": [
        "--cfg=hax_compilation",
        "--cfg=hax_backend_lean",
        '--cfg=feature="test-utils"',
    ],
    "skip_borrowck": False,
    "start_from": [
        "crate",
        "core::clone::Clone::clone_from",
        "core::cmp::PartialEq::ne",
        "core::cmp::PartialOrd::lt",
        "core::cmp::PartialOrd::le",
        "core::cmp::PartialOrd::gt",
        "core::cmp::PartialOrd::ge",
        "core::iter::range::Step::forward",
        "core::iter::range::Step::forward_unchecked",
        "core::iter::range::Step::backward",
        "core::iter::range::Step::backward_unchecked",
    ],
    "start_from_attribute": [],
    "start_from_if_exists": [],
    "start_from_pub": False,
    "sysroot": None,
    "targets": [],
    "translate_all_methods": False,
    "treat_box_as_builtin": True,
    "ullbc": False,
    "unbind_item_vars": True,
    "unsized_strings": False,
}


def check_options(options: dict) -> None:
    actual = {key: value for key, value in options.items() if key != "dest_file"}
    if actual != EXPECTED_OPTIONS:
        changed = sorted(
            key
            for key in set(actual) | set(EXPECTED_OPTIONS)
            if actual.get(key) != EXPECTED_OPTIONS.get(key)
        )
        raise ValueError(f"unreviewed LLBC extraction options: {changed}")


def build_receipt(root: Path, llbc: dict) -> dict:
    translated = llbc["translated"]
    if (
        llbc["has_errors"] is not False
        or translated["crate_name"] != "beaconcrypt_core"
    ):
        raise ValueError("LLBC extraction has errors or the wrong crate")
    if llbc["charon_version"] != "0.1.247":
        raise ValueError("unreviewed Charon version")
    options = translated["options"]
    check_options(options)
    files = {}
    for item in translated["files"]:
        if item["crate_name"] == "beaconcrypt_core":
            name = item["name"].get("Local")
            if not name or name in {entry["name"]["Local"] for entry in files.values()}:
                raise ValueError("invalid or duplicate local LLBC source file")
            files[item["id"]] = item
    sources, functions = sources_and_functions(root)
    if set(sources) != {item["name"]["Local"] for item in files.values()}:
        raise ValueError(
            "LLBC source file inventory differs from the complete core source tree"
        )
    for item in files.values():
        name = item["name"]["Local"]
        if item["contents"] != sources[name]:
            raise ValueError(f"stale LLBC embedded source: {name}")
    declarations = []
    for declaration in translated["fun_decls"]:
        if declaration is None or not declaration["item_meta"]["is_local"]:
            continue
        meta = declaration["item_meta"]
        if (
            meta["opacity"] != "Transparent"
            or not isinstance(declaration["body"], dict)
            or "Structured" not in declaration["body"]
        ):
            raise ValueError("opaque or missing local LLBC function body")
        data = meta["span"]["data"]
        if data["file_id"] not in files:
            raise ValueError("local LLBC function has an unknown source file")
        path = files[data["file_id"]]["name"]["Local"]
        names = [part["Ident"][0] for part in meta["name"] if "Ident" in part]
        declarations.append(
            (
                path,
                names[-1],
                source_offset(sources[path], data["beg"]),
                source_offset(sources[path], data["end"]),
            )
        )
    for path, entries in functions.items():
        for function in entries:
            if not any(
                path == p
                and function.name == name
                and function.start <= start <= function.name_start
                and function.end == end
                for p, name, start, end in declarations
            ):
                raise ValueError(
                    f"handwritten library function absent from LLBC: {path} {function.name}"
                )
    check_lean_spans(root, sources, functions)
    return {
        "schema": 1,
        "charon_version": llbc["charon_version"],
        "source_sha256": {
            path: hashlib.sha256(source.encode()).hexdigest()
            for path, source in sources.items()
        },
        "extraction_sha256": artifact_hashes(root),
        "functions": function_inventory(functions),
        "extraction_options": {
            key: value for key, value in options.items() if key != "dest_file"
        },
    }


def check(root: Path) -> int:
    receipt = json.loads(
        (root / "beaconcrypt-core/proofs/lean/source-coverage.json").read_text()
    )
    sources, functions = sources_and_functions(root)
    if receipt["schema"] != 1:
        raise ValueError("unsupported core source coverage receipt schema")
    if receipt["charon_version"] != "0.1.247":
        raise ValueError("unreviewed Charon version in coverage receipt")
    check_options(receipt["extraction_options"])
    expected_sources = {
        path: hashlib.sha256(source.encode()).hexdigest()
        for path, source in sources.items()
    }
    if receipt["source_sha256"] != expected_sources:
        raise ValueError(
            "core source changed since validated LLBC extraction; regenerate its coverage receipt"
        )
    if receipt["extraction_sha256"] != artifact_hashes(root):
        raise ValueError(
            "Lean extraction changed since validated LLBC coverage receipt"
        )
    if receipt["functions"] != function_inventory(functions):
        raise ValueError(
            "core handwritten function inventory differs from its validated LLBC receipt"
        )
    check_lean_spans(root, sources, functions)
    return sum(map(len, functions.values()))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="validate the fresh LLBC extraction and write its compact coverage receipt",
    )
    args = parser.parse_args()
    if args.write:
        path = args.root / "beaconcrypt-core/proofs/lean/llbc/beaconcrypt_core.llbc"
        receipt = build_receipt(args.root, json.loads(path.read_text()))
        (args.root / "beaconcrypt-core/proofs/lean/source-coverage.json").write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n"
        )
    count = check(args.root)
    print(
        f"Checked {count} handwritten library functions against complete, current LLBC source coverage."
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, IndexError, TypeError) as error:
        sys.exit(f"Core source coverage failed: {error}")
