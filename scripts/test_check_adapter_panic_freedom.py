#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression checks for the signature-derived conditional adapter boundary."""

from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

import check_adapter_panic_freedom as checker


class LeanControlCoordinationTests(unittest.TestCase):
    def test_absent_coordinator_preserves_the_direct_control_command(self):
        with tempfile.TemporaryDirectory() as directory:
            command = ["lake", "env", "lean", "Control.lean"]
            self.assertEqual(
                checker.lean_control_command(
                    "control", command, Path(directory) / "absent", {}
                ),
                command,
            )

    def test_available_coordinator_wraps_the_identical_command(self):
        with tempfile.TemporaryDirectory() as directory:
            helper = Path(directory) / "coord.sh"
            helper.write_text("#!/usr/bin/env bash\nexit 0\n")
            helper.chmod(0o755)
            command = ["lake", "env", "lean", "Control.lean"]
            self.assertEqual(
                checker.lean_control_command("control", command, helper, {}),
                [str(helper), "lean", "codex", "control", "--", *command],
            )

    def test_inherited_lease_or_slot_does_not_nest_coordination(self):
        with tempfile.TemporaryDirectory() as directory:
            helper = Path(directory) / "coord.sh"
            helper.write_text("coordinator must not be invoked\n")
            helper.chmod(0o755)
            command = ["lake", "env", "lean", "Control.lean"]
            for environment in (
                {"COORD_LEASE_TICKET": "00000042"},
                {"COORD_LEAN_SLOT": "0"},
                {"COORD_LEAN_SLOT_LOCK": "/tmp/example-lean.lock"},
            ):
                with self.subTest(environment=environment):
                    self.assertEqual(
                        checker.lean_control_command(
                            "control", command, helper, environment
                        ),
                        command,
                    )

    def test_nonexecutable_coordinator_is_reported(self):
        with tempfile.TemporaryDirectory() as directory:
            helper = Path(directory) / "coord.sh"
            helper.write_text("not executable\n")
            with self.assertRaisesRegex(ValueError, "not executable"):
                checker.lean_control_command(
                    "control", ["lean", "Control.lean"], helper, {}
                )

    def test_broken_coordinator_is_not_treated_as_an_absent_runner(self):
        with tempfile.TemporaryDirectory() as directory:
            helper = Path(directory) / "coord.sh"
            helper.symlink_to(Path(directory) / "missing")
            with self.assertRaisesRegex(ValueError, "not executable"):
                checker.lean_control_command(
                    "control", ["lean", "Control.lean"], helper, {}
                )


class LeanControlGateTests(unittest.TestCase):
    """Exercise the actual Make recipes with fake compilers, never proof engines."""

    prerequisites = {
        "prepare-lean-dependencies",
        "check-lean-policy",
        "check-lean-root",
        "check-lean-panic-freedom",
        "check-adapter-panic-freedom",
        "check-adapter-record-source",
        "check-frame-codec-source",
        "check-adapter-authentication-source",
        "check-adapter-record-request-source",
        "check-registration-codec-checkpoint",
        "check-computational-completion-source",
    }
    targets = ("check-lean", "check-adapter-panic-freedom-controls")

    def run_gate(self, target, *, fail_build=False, fail_controls=False):
        make = shutil.which("make")
        if make is None:
            self.skipTest(
                "GNU Make is required for the Make-recipe integration controls"
            )
        makefile = Path(__file__).resolve().parents[1] / "beaconcrypt-core/Makefile"
        source = makefile.read_text()
        for gate in self.targets:
            match = re.search(r"^" + re.escape(gate) + r":([^\n]*)$", source, re.M)
            self.assertIsNotNone(match, gate)
            # Fail before invoking Make if a new prerequisite needs isolation.
            self.assertLessEqual(set(match[1].split()), self.prerequisites)
        with tempfile.TemporaryDirectory(prefix="beaconcrypt-lean-gate-") as directory:
            temporary = Path(directory)
            fakebin = temporary / "bin"
            fakebin.mkdir()
            lean = temporary / "lean"
            lean.mkdir()
            events = temporary / "events.jsonl"
            tool = (
                f"#!{sys.executable}\n"
                "import json, os, pathlib, sys\n"
                "name = pathlib.Path(sys.argv[0]).name\n"
                "with open(os.environ['BC_ADAPTER_GATE_LOG'], 'a') as output:\n"
                "    output.write(json.dumps([name, sys.argv[1:]]) + '\\n')\n"
                "if name == 'lake' and os.environ.get('BC_ADAPTER_GATE_FAIL_BUILD') == '1':\n"
                "    raise SystemExit(23)\n"
                "if name == 'python3' and '--check-lean-controls' in sys.argv and os.environ.get('BC_ADAPTER_GATE_FAIL_CONTROLS') == '1':\n"
                "    raise SystemExit(29)\n"
            )
            for name in ("lake", "python3"):
                path = fakebin / name
                path.write_text(tool)
                path.chmod(0o755)
            overrides = temporary / "prerequisites.mk"
            overrides.write_text(
                ".PHONY: "
                + " ".join(sorted(self.prerequisites))
                + "\n"
                + " ".join(sorted(self.prerequisites))
                + ": ; @:\n"
            )
            environment = os.environ.copy()
            for key in ("MAKEFLAGS", "MFLAGS", "MAKEOVERRIDES", "MAKELEVEL"):
                environment.pop(key, None)
            environment.update(
                {
                    "PATH": str(fakebin) + os.pathsep + environment.get("PATH", ""),
                    "BC_ADAPTER_GATE_LOG": str(events),
                    "BC_ADAPTER_GATE_FAIL_BUILD": str(int(fail_build)),
                    "BC_ADAPTER_GATE_FAIL_CONTROLS": str(int(fail_controls)),
                }
            )
            result = subprocess.run(
                [
                    make,
                    "--no-print-directory",
                    "-f",
                    str(makefile),
                    "-f",
                    str(overrides),
                    "SHELL=" + shutil.which("bash"),
                    "LEAN_DIR=" + str(lean),
                    target,
                ],
                cwd=temporary,
                env=environment,
                text=True,
                capture_output=True,
                timeout=30,
            )
            calls = (
                [json.loads(line) for line in events.read_text().splitlines()]
                if events.exists()
                else []
            )
            return result, calls

    def test_both_gates_build_certificates_before_running_controls(self):
        for target in self.targets:
            with self.subTest(target=target):
                result, calls = self.run_gate(target)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                build = (
                    ["--rehash", "build"]
                    if target == "check-lean"
                    else ["build", "BeaconcryptCore.PanicFreedom.AdapterCoverage"]
                )
                self.assertEqual(
                    calls,
                    [
                        ["lake", build],
                        [
                            "python3",
                            [
                                "../scripts/check_adapter_panic_freedom.py",
                                "--check-lean-controls",
                            ],
                        ],
                    ],
                )

    def test_failed_build_prevents_controls_and_fails_the_gate(self):
        for target in self.targets:
            with self.subTest(target=target):
                result, calls = self.run_gate(target, fail_build=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual([call[0] for call in calls], ["lake"])

    def test_failed_controls_fail_both_gates(self):
        for target in self.targets:
            with self.subTest(target=target):
                result, calls = self.run_gate(target, fail_controls=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual([call[0] for call in calls], ["lake", "python3"])


class AdapterBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.source = (
            "namespace example\n"
            "variable [Example.Operations]\n"
            "def f {T : Type} (x : T) : RustM T := ok x\n"
            "end example\n"
        )
        namespace, instances, definitions = checker.declarations(self.source)
        self.parsed = {
            "AdapterAuthenticationExtraction": (namespace, instances, definitions)
        }
        self.certificates = {
            "example.f": {
                "module": "Proof",
                "theorem": "Proof.f_total",
                "form": "exists",
            }
        }

    def test_namespace_and_instance_parameters_are_retained(self):
        rendered = checker.render(self.parsed, self.certificates)
        self.assertIn("[_adapter_instance_00 : Example.Operations]", rendered)
        self.assertIn("open example", rendered)
        self.assertIn(
            "∃ adapter_result, example.f (T := T) x = ok adapter_result", rendered
        )

    def test_constructor_contract_selects_the_actual_rng_argument(self):
        namespace, instances, definitions = checker.declarations(
            "namespace beaconcrypt_constructor\n"
            "def beacon.Beacon.try_new_with_rng {State Error : Type} "
            "(chosen : rand_core.TryCryptoRng State Error) (rng : State) : RustM Unit := ok ()\n"
            "end beaconcrypt_constructor\n"
        )
        definition = next(iter(definitions.values()))
        self.assertEqual(checker.selected_rng(definition), "chosen")
        certificate = {
            definition.name: {
                "module": "Proof",
                "theorem": "Proof.total",
                "form": "exists",
                "preservation": {"module": "Proof", "theorem": "Proof.preserves"},
            }
        }
        rendered = checker.render(
            {"AdapterBeaconConstructorExtraction": (namespace, instances, definitions)},
            certificate,
        )
        self.assertIn("AdapterConstructors.BeaconContracts chosen", rendered)
        self.assertNotIn("AdapterConstructors.BeaconContracts)", rendered)

    def test_rng_signature_drift_cannot_select_a_missing_or_ambiguous_dictionary(self):
        for binders in (
            "{R E : Type} (rng : R)",
            "{R E : Type} (first second : rand_core.TryCryptoRng R E)",
            "{R E : Type} (first : rand_core.TryCryptoRng R E) "
            "(second : rand_core.TryCryptoRng R E)",
            "{R E : Type} (first : rand_core.TryCryptoRng (Option R) E)",
        ):
            with self.subTest(binders=binders):
                _, _, definitions = checker.declarations(
                    f"namespace example\ndef f {binders} : RustM Unit := ok ()\nend example\n"
                )
                with self.assertRaises(ValueError):
                    checker.selected_rng(next(iter(definitions.values())))

    def test_hosted_constructor_contract_selects_only_the_os_dictionary(self):
        _, _, definitions = checker.declarations(
            "namespace beaconcrypt_server_constructor\n"
            "def server.Server.try_new (identifier : Nat) : RustM Unit := ok ()\n"
            "end beaconcrypt_server_constructor\n"
        )
        premises = checker.assumptions(
            "AdapterServerConstructorExtraction", next(iter(definitions.values()))
        )
        self.assertEqual(len(premises), 1)
        self.assertIn(
            "ServerContracts BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard.os",
            premises[0],
        )

    def test_entropy_free_loops_do_not_inherit_rng_or_unrelated_phase_contracts(self):
        for operation, expected in (
            ("beacon._proof_beacon_init_ready_loop.body", "InitContracts"),
            (
                "beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop",
                "AdapterRecordReceive.Contracts",
            ),
        ):
            with self.subTest(operation=operation):
                _, _, definitions = checker.declarations(
                    f"namespace beaconcrypt_public_wrapper\ndef {operation} "
                    ": RustM Unit := ok ()\nend beaconcrypt_public_wrapper\n"
                )
                premises = checker.assumptions(
                    "AdapterPublicWrapperExtraction", next(iter(definitions.values()))
                )
                self.assertEqual(len(premises), 1)
                self.assertIn(expected, premises[0])
                self.assertNotIn("Rng", premises[0])
                self.assertNotIn("LoopContracts", premises[0])

    def test_encapsulation_closure_does_not_require_key_generation(self):
        _, _, definitions = checker.declarations(
            "namespace beaconcrypt_public_wrapper\n"
            "def pqxdh.execute_agreement.closure_2.Insts.FnMut.call_mut "
            "{R E : Type} (selected : rand_core.TryCryptoRng R E) "
            ": RustM Unit := ok ()\nend beaconcrypt_public_wrapper\n"
        )
        premises = checker.assumptions(
            "AdapterPublicWrapperExtraction", next(iter(definitions.values()))
        )
        self.assertIn("EncapsulationContracts selected", " ".join(premises))
        self.assertNotIn("AgreementRngContracts", " ".join(premises))

    def test_non_rng_agreement_closures_have_no_rng_execution_premise(self):
        _, _, definitions = checker.declarations(
            "namespace beaconcrypt_public_wrapper\n"
            "def pqxdh.execute_agreement.closure_1.Insts.FnOnce.call_once "
            "{R E : Type} (selected : rand_core.TryCryptoRng R E) "
            ": RustM Unit := ok ()\nend beaconcrypt_public_wrapper\n"
        )
        premises = checker.assumptions(
            "AdapterPublicWrapperExtraction", next(iter(definitions.values()))
        )
        self.assertEqual(len(premises), 1)
        self.assertIn("AgreementContracts)", premises[0])

    def test_public_rng_contracts_select_the_generated_argument(self):
        for namespace, cohort, operation, contract in (
            (
                "beaconcrypt_public_wrapper",
                "AdapterPublicWrapperExtraction",
                "beacon.Beacon.get_registration_bundle_with_rng",
                "GenerationContracts",
            ),
            (
                "beaconcrypt_public_wrapper",
                "AdapterPublicWrapperExtraction",
                "server.Server.get_shared_secret_from_lookup_with_rng",
                "AgreementRngContracts",
            ),
            (
                "beaconcrypt_public_server_entry",
                "AdapterPublicServerEntryExtraction",
                "server.Server.get_shared_secret_with_rng",
                "AgreementRngContracts",
            ),
        ):
            with self.subTest(operation=operation):
                _, _, definitions = checker.declarations(
                    f"namespace {namespace}\ndef {operation} "
                    "{R E : Type} (actual : rand_core.TryCryptoRng R E) "
                    f": RustM Unit := ok ()\nend {namespace}\n"
                )
                premises = checker.assumptions(cohort, next(iter(definitions.values())))
                self.assertIn(contract + " actual)", " ".join(premises))
                self.assertNotIn("LoopContracts", " ".join(premises))

    def test_beacon_agreement_selects_the_fixed_no_entropy_dictionary(self):
        _, _, definitions = checker.declarations(
            "namespace beaconcrypt_public_wrapper\n"
            "def pqxdh.execute_beacon_agreement : RustM Unit := ok ()\n"
            "end beaconcrypt_public_wrapper\n"
        )
        premises = checker.assumptions(
            "AdapterPublicWrapperExtraction", next(iter(definitions.values()))
        )
        self.assertIn(
            "AgreementRngContracts beaconcrypt_public_wrapper.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError)",
            " ".join(premises),
        )

    def test_external_models_retain_their_exact_namespace(self):
        self.assertEqual(
            checker.modeled_declarations(
                "namespace Model.One\nclass Operations where\nend Model.One\n"
                "namespace Model.Two\ndef\n  leaf : Nat := 0\nend Model.Two\n"
            ),
            ["Model.One.Operations", "Model.Two.leaf"],
        )

    def test_signature_change_changes_the_actual_checked_proposition(self):
        before = checker.render(self.parsed, self.certificates)
        ns, instances, definitions = checker.declarations(
            self.source.replace("(x : T)", "(x y : T)")
        )
        after = checker.render(
            {"AdapterAuthenticationExtraction": (ns, instances, definitions)},
            self.certificates,
        )
        self.assertNotEqual(before, after)
        self.assertIn("example.f (T := T) x y = ok adapter_result", after)

    def test_new_operation_needs_a_certificate(self):
        ns, instances, ds = checker.declarations(
            self.source.replace(
                "end example", "def g : RustM Unit := ok ()\nend example"
            )
        )
        with self.assertRaisesRegex(ValueError, "missing=.*example.g"):
            checker.render(
                {"AdapterAuthenticationExtraction": (ns, instances, ds)},
                self.certificates,
            )

    def test_removed_operation_rejects_stale_certificate(self):
        with self.assertRaisesRegex(ValueError, "extra=.*example.f"):
            checker.render({}, self.certificates)

    def test_an_arbitrary_manifest_proposition_is_rejected(self):
        self.certificates["example.f"]["proposition"] = "True"
        with self.assertRaisesRegex(ValueError, "invalid certificate fields"):
            checker.render(self.parsed, self.certificates)

    def test_manifest_cannot_add_a_controller_totality_premise(self):
        self.certificates["example.f"][
            "precondition"
        ] = "∃ result, example.f x = ok result"
        with self.assertRaisesRegex(ValueError, "invalid certificate fields"):
            checker.render(self.parsed, self.certificates)

    def test_stateful_operation_requires_the_fixed_preservation_contract(self):
        namespace, instances, definitions = checker.declarations(
            "namespace beaconcrypt_public_ordinary\n"
            "def ratchet.encrypt_message_with_ratchet (ratchet1 : Nat) : RustM (Nat × Nat) := ok (0, ratchet1)\n"
            "end beaconcrypt_public_ordinary\n"
        )
        name = "beaconcrypt_public_ordinary.ratchet.encrypt_message_with_ratchet"
        certificate = {
            name: {"module": "Proof", "theorem": "Proof.total", "form": "exists"}
        }
        parsed = {
            "AdapterPublicOrdinaryExtraction": (namespace, instances, definitions)
        }
        with self.assertRaisesRegex(ValueError, "invalid certificate fields"):
            checker.render(parsed, certificate)
        certificate[name]["preservation"] = {
            "module": "Proof",
            "theorem": "Proof.preserves",
        }
        rendered = checker.render(parsed, certificate)
        self.assertIn("ValidManager adapter_result.2", rendered)
        self.assertIn("ValidManager ratchet1", rendered)
        certificate[name]["preservation"]["postcondition"] = "True"
        with self.assertRaisesRegex(ValueError, "invalid preservation certificate"):
            checker.render(parsed, certificate)

    def source_builder_fixture(self):
        name = next(iter(checker.SOURCE_COMPOSITION))
        namespace, instances, definitions = checker.declarations(
            "namespace beaconcrypt_public_wrapper\n"
            "def server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response "
            "(self reg_out data : Nat) : RustM (Nat × Nat) := ok (0, self)\n"
            "end beaconcrypt_public_wrapper\n"
        )
        certificate = {
            name: {
                "module": "Proof",
                "theorem": "Proof.total",
                "form": "exists",
                "preservation": {"module": "Proof", "theorem": "Proof.preserves"},
            }
        }
        return (
            name,
            {"AdapterPublicWrapperExtraction": (namespace, instances, definitions)},
            certificate,
        )

    def test_public_builder_requires_both_source_composition_certificates(self):
        name, parsed, certificate = self.source_builder_fixture()
        with self.assertRaisesRegex(ValueError, "invalid certificate fields"):
            checker.render(parsed, certificate)
        certificate[name]["source_composition"] = {
            "module": "Proof",
            "theorem": "Proof.source_total",
            "preservation": {"module": "Proof", "theorem": "Proof.source_preserves"},
        }
        rendered = checker.render(parsed, certificate)
        self.assertIn("theorem operation_000_source ", rendered)
        self.assertIn("theorem operation_000_source_preserves ", rendered)
        source = rendered.split("theorem operation_000_source ", 1)[1]
        self.assertIn("AdapterPublicServerBuildSource.sourceLocalOperations", source)
        self.assertIn("AdapterPublicServerBuildSource.Contracts", source)
        self.assertNotIn("AdapterPublicServerBuild.Contracts", source)
        self.assertIn("ValidServer adapter_result.2", source)

    def test_source_composition_manifest_cannot_introduce_a_premise(self):
        name, parsed, certificate = self.source_builder_fixture()
        certificate[name]["source_composition"] = {
            "module": "Proof",
            "theorem": "Proof.source_total",
            "preservation": {"module": "Proof", "theorem": "Proof.source_preserves"},
            "precondition": "False",
        }
        with self.assertRaisesRegex(
            ValueError, "invalid source composition certificate"
        ):
            checker.render(parsed, certificate)

    def test_source_composition_manifest_cannot_weaken_the_returned_state(self):
        name, parsed, certificate = self.source_builder_fixture()
        certificate[name]["source_composition"] = {
            "module": "Proof",
            "theorem": "Proof.source_total",
            "preservation": {
                "module": "Proof",
                "theorem": "Proof.source_preserves",
                "postcondition": "True",
            },
        }
        with self.assertRaisesRegex(
            ValueError, "invalid source preservation certificate"
        ):
            checker.render(parsed, certificate)

    def test_lift_inventory_covers_multiline_definitions_and_rejects_new_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            proof = Path(directory)
            for name in checker.INTERPRETER_LIFTS:
                (proof / (name + ".lean")).write_text(
                    "namespace Example\ndef\n  lifted : Nat := 0\nend Example\n"
                )
            inventory = checker.interpreter_lifts(proof)
            self.assertTrue(
                all(
                    row["declarations"] == ["Example.lifted"]
                    for row in inventory.values()
                )
            )
            (proof / "AdapterUnknownExtraction.lean").write_text(
                "namespace Example\nend Example\n"
            )
            with self.assertRaisesRegex(ValueError, "interpreter-lift roster drift"):
                checker.interpreter_lifts(proof)

    def test_manifest_cannot_inject_lean(self):
        self.certificates["example.f"]["theorem"] = "Proof.f_total\ntrivial"
        with self.assertRaisesRegex(ValueError, "invalid certificate name"):
            checker.render(self.parsed, self.certificates)

    def test_transitive_axiom_audit_covers_every_exported_certificate(self):
        rendered = checker.render(self.parsed, self.certificates)
        self.assertIn("Lean.collectAxioms declaration", rendered)
        self.assertIn("``operation_000", rendered)
        self.assertIn("(← Lean.getEnv).constants.toList", rendered)
        self.assertIn('startsWith "BeaconcryptCore.PanicFreedom.Adapter"', rendered)
        self.assertIn(
            "let allowed := [``propext, ``Classical.choice, ``Quot.sound]", rendered
        )

    def test_monadic_closures_and_loops_are_covered(self):
        source = (
            "namespace example\n"
            "@[rust_loop_body]\ndef loop.body : RustM Unit := ok ()\n"
            "@[rust_loop]\ndef loop : RustM Unit := ok ()\n"
            "def f.closure.Insts.Fn.call (_ : Unit) : RustM Unit := ok ()\n"
            "@[reducible]\ndef f.closure.Insts.Fn : core.ops.function.FnOnce Unit Unit Unit := ()\n"
            "end example\n"
        )
        _, _, ds = checker.declarations(source)
        self.assertEqual(sum(d.monadic for d in ds.values()), 3)
        self.assertEqual(ds["example.loop"].role, "loop-helper")
        self.assertEqual(ds["example.f.closure.Insts.Fn"].role, "pure-instance")
        self.assertIn(
            "adapter_unit_argument", ds["example.f.closure.Insts.Fn.call"].binders
        )

    def test_repeated_anonymous_arguments_fail_closed(self):
        with self.assertRaisesRegex(ValueError, "duplicate or colliding binder"):
            checker.declarations(self.source.replace("(x : T)", "(_ : T) (_ : T)"))

    def test_anonymous_argument_name_collision_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "duplicate or colliding binder"):
            checker.declarations(
                self.source.replace("(x : T)", "(_ : T) (adapter_unit_argument : T)")
            )

    def test_unknown_namespace_format_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "exactly one reviewed namespace"):
            checker.declarations(
                self.source.replace(
                    "end example", "namespace nested\nend nested\nend example"
                )
            )

    def test_unknown_definition_format_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unparsed generated definition"):
            checker.declarations(self.source.replace("def f", "private def f"))

    def test_monadic_aliases_or_parentheses_cannot_silently_become_pure(self):
        for returned in ("(RustM T)", "Execution T", "Result T"):
            with self.subTest(returned=returned):
                with self.assertRaisesRegex(
                    ValueError, "unreviewed non-RustM return shape"
                ):
                    checker.declarations(self.source.replace("RustM T", returned))

    def test_unparsed_instance_declaration_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unparsed global instance binder"):
            checker.declarations(
                self.source.replace(
                    "variable [Example.Operations]", "variable {T : Type}"
                )
            )

    def test_output_witness_does_not_capture_inputs(self):
        ns, instances, ds = checker.declarations(
            self.source.replace("(x : T)", "(adapter_result : T)")
        )
        rendered = checker.render(
            {"AdapterAuthenticationExtraction": (ns, instances, ds)}, self.certificates
        )
        self.assertIn(
            "∃ adapter_result_, example.f (T := T) adapter_result = ok adapter_result_",
            rendered,
        )

    def test_unknown_cohort_cannot_invent_its_own_contract(self):
        ns, instances, ds = next(iter(self.parsed.values()))
        with self.assertRaisesRegex(
            ValueError, "no reviewed external-operation contract"
        ):
            checker.render({"Unknown": (ns, instances, ds)}, self.certificates)

    def test_intentional_exceptions_are_limited_to_two_named_constructors(self):
        self.assertEqual(
            checker.INTENTIONAL_PANICS,
            {
                "beaconcrypt_constructor.beacon.Beacon.new",
                "beaconcrypt_server_constructor.server.Server.new",
            },
        )

    def test_intentional_exception_requires_the_actual_expect_body(self):
        with self.assertRaisesRegex(ValueError, "exception lost its Result.expect"):
            checker.declarations(
                "namespace beaconcrypt_constructor\n"
                "def beacon.Beacon.new : RustM Unit := ok ()\n"
                "end beaconcrypt_constructor\n"
            )

    def test_checked_repository_inventory_has_exact_profiles_and_roles(self):
        root = Path(__file__).resolve().parents[1]
        reviewed, parsed = checker.inventory(root)
        self.assertEqual(len(reviewed["interpreter_lifts"]), 16)
        self.assertTrue(
            all(
                not row["native_RustM_totality_certificate"]
                for row in reviewed["interpreter_lifts"].values()
            )
        )
        reviewed = reviewed["native_cohorts"]
        self.assertEqual(sum(len(ds) for _, _, ds in parsed.values()), 130)
        self.assertEqual(
            sum(d.monadic for _, _, ds in parsed.values() for d in ds.values()), 99
        )
        self.assertEqual(
            reviewed["AdapterBeaconConstructorExtraction"]["features"],
            ["beacon", "pqxdh", "server", "std"],
        )
        self.assertEqual(
            reviewed["AdapterAuthenticationExtraction"]["features"], ["beacon", "pqxdh"]
        )
        self.assertEqual(
            reviewed["AdapterInitAuthenticationExtraction"]["features"],
            ["beacon", "pqxdh", "server"],
        )
        self.assertTrue(reviewed["AdapterRecordHelpersExtraction"]["external_models"])


if __name__ == "__main__":
    unittest.main()
