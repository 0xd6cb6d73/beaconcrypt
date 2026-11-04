#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for exact public-wrapper request rebinding."""

import copy
import json
import unittest
from unittest.mock import patch

import lift_adapter_public_wrapper_requests as lift


class PublicWrapperLiftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (lift.ROOT / lift.SOURCE).read_bytes()
        cls.bindings = (lift.ROOT / lift.BINDINGS).read_bytes()
        cls.control = json.loads(cls.bindings)

    def transformed_control(self, control):
        encoded = (json.dumps(control, indent=2) + "\n").encode()
        with patch.object(lift, "BINDINGS_SHA256", lift.digest(encoded)):
            return lift.transform(self.source, encoded)

    def test_checked_artifact(self):
        self.assertEqual(
            lift.transform(self.source, self.bindings),
            (lift.ROOT / lift.DESTINATION).read_bytes(),
        )

    def test_all_declarations_retained(self):
        result = lift.transform(self.source, self.bindings).decode()
        self.assertEqual(len(self.control["definitions"]), 49)
        self.assertEqual(
            sum(row["mode"] == "static" for row in self.control["definitions"]), 4
        )
        self.assertEqual(result.count("AdapterPublicWrapperLiftFunction.loopFuel"), 3)
        self.assertIn("ChildOperations.authenticateInit", result)
        self.assertIn("ChildOperations.authenticateResponse", result)
        self.assertIn("ContainerOperations.setReserve", result)
        self.assertIn("ContainerOperations.vacantInsert", result)

    def test_source_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError, "source changed"):
            lift.transform(self.source.replace(b"if b", b"if true", 1), self.bindings)

    def test_source_order_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError, "source changed"):
            lift.transform(self.source + b"\n", self.bindings)

    def test_binding_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError, "bindings changed"):
            lift.transform(self.source, self.bindings + b"\n")

    def test_declaration_roster_rejected(self):
        control = copy.deepcopy(self.control)
        control["definitions"].reverse()
        with self.assertRaisesRegex(ValueError, "declaration roster"):
            self.transformed_control(control)

    def test_declaration_hash_rejected(self):
        control = copy.deepcopy(self.control)
        control["definitions"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "declaration changed"):
            self.transformed_control(control)

    def test_leaf_multiplicity_rejected(self):
        control = copy.deepcopy(self.control)
        control["definitions"][0]["body"][0]["count"] += 1
        with self.assertRaisesRegex(ValueError, "multiplicity"):
            self.transformed_control(control)

    def test_duplicate_leaf_rejected(self):
        control = copy.deepcopy(self.control)
        row = control["definitions"][0]["body"]
        row.append(copy.deepcopy(row[0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.transformed_control(control)

    def test_header_leaf_multiplicity_rejected(self):
        control = copy.deepcopy(self.control)
        control["definitions"][0]["signature"][0]["count"] += 1
        with self.assertRaisesRegex(ValueError, "multiplicity"):
            self.transformed_control(control)

    def test_comments_and_strings_not_rebound(self):
        source = 'call.foo "call.foo" /- call.foo -/ -- call.foo\ncall.foo'
        result = lift.replace_leaves(
            source, [{"before": "call.foo", "after": "new.foo", "count": 2}]
        )
        self.assertEqual(
            result, 'new.foo "call.foo" /- call.foo -/ -- call.foo\nnew.foo'
        )

    def test_token_prefix_not_rebound(self):
        result = lift.replace_leaves(
            "a.fun a.function a.fun_extra",
            [{"before": "a.fun", "after": "b.fun", "count": 1}],
        )
        self.assertEqual(result, "b.fun a.function a.fun_extra")

    def test_omitted_effect_detected(self):
        with self.assertRaisesRegex(ValueError, "multiplicity"):
            lift.replace_leaves(
                "pure result",
                [{"before": "reserve", "after": "reserveShared", "count": 1}],
            )


if __name__ == "__main__":
    unittest.main()
