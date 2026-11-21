-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawInitializedSlot

/-! Dropping the private selected-session mark can only increase the probability of any native raw public event. Together with the initialized slot law and the public record-world handoff this gives the direction needed by cryptographic upper bounds, without an assumed mark-provenance theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMarkedBound
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open CborRawPublicState (Public)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

theorem marked_le (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp Spec Result) (event : Result × CborRawPostActive.Produced → Bool)
    (state : Public × Native KemSK) :
    𝒟[CborRawMarkedPrefix.run setup wire parse checks target parameters created work event state] {true} ≤
      𝒟[(fun value => event (value.1, value.2.2.base.produced)) <$>
        (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) work).run
          state] {true} := by
  rw [CborRawMarkedPrefix.run, ← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun result _ held => ?_
  simp only [Bool.and_eq_true] at held
  exact held.1

end BeaconcryptCore.Computational.CborRawMarkedBound

/-- info: 'BeaconcryptCore.Computational.CborRawMarkedBound.marked_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMarkedBound.marked_le
