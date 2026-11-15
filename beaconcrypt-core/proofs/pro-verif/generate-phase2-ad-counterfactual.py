#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Derive the counterfactual Phase-2 control whose transcript AD omits the assigned ID.

This is a counterfactual control, never a production profile. Registration
version 3 binds the response assigned ID twice: as the LE64 last field of the
transcript T inside AD151, and as the authenticated eight-byte prefix of the
initial payload. With the production control the relabeled-ID fixture is
already rejected by AEAD/CTX opening under AD151, so the prefix gate is not
reached. This derivation replaces only the assigned-ID transcript field of the
two AD151 derivations in phase2-response-binding-control.pvl (the Beacon finish
gate and the fixture Server) by one fixed public constant. Every other
transcript field, gate, event, fixture and query is unchanged, so the Phase-2
runs show that the authenticated assigned-ID prefix gate alone still rejects
the relabeled response (strong theory) and is load-bearing (weak theory).
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re

CONSTANT = "phase2_counterfactual_ad_omitted_assigned_id"
CALL = "transcript_associated_data("
DECLARATION = (
    "(* Counterfactual control only: the transcript AD omits the assigned ID. *)\n"
    f"const {CONSTANT}: key_id.\n"
)


def counterfactual(source: str) -> str:
    if CONSTANT in source:
        raise ValueError("counterfactual constant already present")
    starts = [match.start() for match in re.finditer(re.escape(CALL), source)]
    if len(starts) != 2:
        raise ValueError("expected exactly two Phase-2 transcript-AD derivations")
    edits = []
    for start in starts:
        open_index = start + len(CALL) - 1
        depth = 0
        commas = []
        for index in range(open_index, len(source)):
            character = source[index]
            if character == "(":
                depth += 1
            elif character == ")":
                depth -= 1
                if depth == 0:
                    close_index = index
                    break
            elif character == "," and depth == 1:
                commas.append(index)
        else:
            raise ValueError("unterminated transcript-AD derivation")
        if len(commas) != 7:
            raise ValueError("transcript-AD derivation must have eight fields")
        field_start = commas[-1] + 1
        if source[field_start:close_index].strip() != "assigned_key_id":
            raise ValueError("assigned ID is not the last transcript-AD field")
        offset = field_start + source[field_start:close_index].index("assigned_key_id")
        edits.append(offset)
    for offset in reversed(edits):
        source = source[:offset] + CONSTANT + source[offset + len("assigned_key_id"):]
    header = "(* SPDX-License-Identifier: 0BSD *)\n"
    if not source.startswith(header):
        raise ValueError("Phase-2 control header changed")
    return header + "\n" + DECLARATION + source[len(header):]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("control", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(counterfactual(args.control.read_text()))


if __name__ == "__main__":
    main()
