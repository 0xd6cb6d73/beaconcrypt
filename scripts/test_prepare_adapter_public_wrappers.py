#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for the public-wrapper source/control transformations."""

import copy
import re
from pathlib import Path
import tempfile
import unittest

import prepare_adapter_public_wrappers as preparation

ROOT = Path(__file__).resolve().parents[1]


def statement(kind, identity=0):
    return {"id": identity, "span": {}, "kind": kind}


def block(*statements):
    return {"id": 0, "span": {}, "statements": list(statements)}


def crate(body):
    return {
        "translated": {
            "fun_decls": [
                {
                    "item_meta": {"name": [{"Ident": ["fixture", 0]}]},
                    "body": {"Structured": {"body": body}},
                }
            ]
        }
    }


class Preparation(unittest.TestCase):
    def setUp(self):
        self.branch = statement(
            {
                "Switch": {
                    "discr": {"Copy": "condition"},
                    "targets": [True, False],
                    "branches": [
                        block(statement({"Assign": "yes"})),
                        block(statement({"Assign": "no"})),
                    ],
                }
            }
        )
        self.input = crate(
            block(self.branch, statement({"Call": "tail"}), statement("Return"))
        )

    def test_switch_distribution_preserves_each_order(self):
        output, certificate = preparation.prepare_llbc(self.input)
        preparation.check_llbc(self.input, output, certificate)
        result = output["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
            "statements"
        ]
        self.assertEqual(len(result), 1)
        branches = result[0]["kind"]["Switch"]["branches"]
        self.assertEqual(
            [s["kind"] for s in branches[0]["statements"]],
            [{"Assign": "yes"}, {"Call": "tail"}, "Return"],
        )
        self.assertEqual(
            [s["kind"] for s in branches[1]["statements"]],
            [{"Assign": "no"}, {"Call": "tail"}, "Return"],
        )
        self.assertEqual(len(certificate["distributions"]), 1)
        self.assertEqual(
            self.input["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
                "statements"
            ][0],
            self.branch,
        )

    def test_terminal_exit_discards_only_unreachable_tail(self):
        for exit in (
            "Return",
            "UnwindResume",
            {"Break": 0},
            {"Continue": 1},
            {"Abort": "panic"},
        ):
            source = crate(block(statement(exit), statement({"Call": "unreachable"})))
            output, certificate = preparation.prepare_llbc(source)
            result = output["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
                "statements"
            ]
            self.assertEqual([s["kind"] for s in result], [exit])
            self.assertEqual(
                certificate["terminal_tails"][0]["discarded"][0]["kind"],
                {"Call": "unreachable"},
            )

    def test_returning_branch_does_not_run_tail(self):
        source = copy.deepcopy(self.input)
        source["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
            "statements"
        ][0]["kind"]["Switch"]["branches"][0] = block(statement("Return"))
        output, _ = preparation.prepare_llbc(source)
        yes = output["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
            "statements"
        ][0]["kind"]["Switch"]["branches"][0]
        self.assertEqual([s["kind"] for s in yes["statements"]], ["Return"])

    def test_loop_depth_and_outside_tail_preserved(self):
        source = crate(
            block(
                statement(
                    {
                        "Loop": block(
                            statement({"Continue": 0}),
                            statement({"Call": "unreachable"}),
                        )
                    }
                ),
                statement({"Call": "outside"}),
            )
        )
        output, _ = preparation.prepare_llbc(source)
        result = output["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
            "statements"
        ]
        self.assertEqual(
            result[0]["kind"]["Loop"]["statements"][0]["kind"], {"Continue": 0}
        )
        self.assertEqual(result[1]["kind"], {"Call": "outside"})

    def test_reject_unknown_statement(self):
        with self.assertRaises(ValueError):
            preparation.prepare_llbc(crate(block(statement({"Unchecked": "body"}))))

    def test_reject_changed_selected_branch(self):
        output, certificate = preparation.prepare_llbc(self.input)
        output["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
            "statements"
        ][0]["kind"]["Switch"]["targets"] = [False, True]
        with self.assertRaises(ValueError):
            preparation.check_llbc(self.input, output, certificate)

    def test_reject_reordered_effect(self):
        output, certificate = preparation.prepare_llbc(self.input)
        branch = output["translated"]["fun_decls"][0]["body"]["Structured"]["body"][
            "statements"
        ][0]["kind"]["Switch"]["branches"][1]["statements"]
        branch[0], branch[1] = branch[1], branch[0]
        with self.assertRaises(ValueError):
            preparation.check_llbc(self.input, output, certificate)

    def test_reject_changed_certificate(self):
        output, certificate = preparation.prepare_llbc(self.input)
        certificate["distributions"] = []
        with self.assertRaises(ValueError):
            preparation.check_llbc(self.input, output, certificate)

    def test_hashcons_definition_restored_after_original_site_erased(self):
        pool = preparation.hashcons_pool(
            [{"HashConsedValue": [3, {"payload": 7}]}, {"Deduplicated": 3}]
        )
        self.assertEqual(
            preparation.recode_hashcons(
                [{"Deduplicated": 3}, {"Deduplicated": 3}], pool
            ),
            [{"HashConsedValue": [3, {"payload": 7}]}, {"Deduplicated": 3}],
        )

    def test_reject_inconsistent_hashcons(self):
        with self.assertRaises(ValueError):
            preparation.hashcons_pool(
                [{"HashConsedValue": [3, "first"]}, {"HashConsedValue": [3, "second"]}]
            )
        with self.assertRaises(ValueError):
            preparation.recode_hashcons({"Deduplicated": 8}, {})

    def test_actual_source_changes_are_exact(self):
        beacon = (ROOT / preparation.RUST_CHANGED[0]).read_text()
        output, certificate = preparation.factor_beacon(beacon)
        self.assertEqual(certificate["original_sha256"], preparation.BEACON_LOOP_SHA256)
        self.assertIn("_proof_beacon_init_ready(self, effect)?", output)
        self.assertEqual(
            re.sub(
                r"\bbeacon\b",
                "self",
                certificate["helper_body"].replace("return Some(ready)", "break ready"),
            ),
            certificate["original"].split("loop {", 1)[1].rsplit("};", 1)[0],
        )
        dh = (ROOT / preparation.RUST_CHANGED[1]).read_text()
        output, certificate = preparation.distribute_dh(dh)
        self.assertEqual(
            certificate["original_sha256"], preparation.DH_SELECTION_SHA256
        )
        self.assertEqual(
            certificate["prepared"].count("crypto_scalarmult::scalarmult"), 4
        )

    def test_reject_changed_source_operation(self):
        beacon = (
            (ROOT / preparation.RUST_CHANGED[0])
            .read_text()
            .replace("pending.resume(signed.as_deref())", "pending.resume(None)")
        )
        with self.assertRaises(ValueError):
            preparation.factor_beacon(beacon)
        dh = (
            (ROOT / preparation.RUST_CHANGED[1])
            .read_text()
            .replace(
                "scalarmult(secret, request.public_key)", "scalarmult(secret, secret)"
            )
        )
        with self.assertRaises(ValueError):
            preparation.distribute_dh(dh)

    def test_fixture_preserves_generated_parser(self):
        with tempfile.TemporaryDirectory(
            prefix="bc-public-preparation-test-"
        ) as temporary:
            destination = Path(temporary) / "source"
            certificate = preparation.prepare_source(ROOT, destination)
            for name in (ROOT / "beaconcrypt-parse/src/generated").glob("*.rs"):
                relative = name.relative_to(ROOT).as_posix()
                self.assertEqual(
                    name.read_bytes(), (destination / relative).read_bytes()
                )
                self.assertIn(relative, certificate["unchanged_sha256"])
            self.assertEqual(
                set(certificate["source_changes"]), set(preparation.RUST_CHANGED)
            )


if __name__ == "__main__":
    unittest.main()
