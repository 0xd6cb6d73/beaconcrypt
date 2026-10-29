-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceProjection

/-! The exact two public compiler passes used by the native G2 experiment inline to the direct key service. The generic StateT flattening law retains every intermediate flag and metadata value; the proved cold invariant then erases only private metadata. Thus the service equality applies to the whole real adaptive client, rather than assuming the wanted frontend interpretation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining
open RegistrationNativeG3KeyService (Spec State direct stacked)
open RegistrationNativeRelatedFamily (Message)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {Value : Type}

private theorem stacked_eq (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    stacked source input inside =
      ((RegistrationNativeKeyCompiler.compiler source input inside).mapStateTBase RegistrationNativeRetainedService.compiler).flattenStateT := rfl

/-- The complete inlined compiler stack is the actual nested compiler execution with only its product-state layout reassociated. -/
theorem stack_run (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) (before : State) :
    (simulateQ (stacked source input inside) work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeKeyCompiler.compiler source input inside)
          ((simulateQ RegistrationNativeRetainedService.compiler work).run before.1)).run before.2 := by
  have actual := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeKeyCompiler.compiler source input inside) RegistrationNativeRetainedService.compiler work before.1 before.2
  rw [← stacked_eq] at actual
  have mapped := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) actual
  simpa only [Functor.map_map, Function.comp_def, Prod.mk.eta, id_map'] using mapped.symm

/-- The native retained/phase/key client equals the direct protected108-byte key service from actual cold flags and metadata, without any initial-invariant premise. -/
theorem client_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) :
    RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work)
      RegistrationNativeKeyPhases.emptyMeta =
        (simulateQ (direct source input inside) work).run' (fun _ => false) := by
  have projected := RegistrationNativeG3KeyServiceProjection.program_source source input inside work
    ((fun _ => false), RegistrationNativeKeyPhases.emptyMeta) (RegistrationNativeG3KeyService.initial_valid input)
  have values := congrArg (fun distribution => Prod.fst <$> distribution) projected
  rw [stack_run] at values
  simpa only [RegistrationNativeKeyCompiler.client, RegistrationNativeRetainedService.client,
    StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using values

end BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining.stack_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining.stack_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KeyServiceInlining.client_source
