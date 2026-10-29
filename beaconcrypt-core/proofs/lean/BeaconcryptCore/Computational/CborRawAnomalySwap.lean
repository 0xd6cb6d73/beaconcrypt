-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyPool

/-! Replacing only an owner's KEM secret leaves native CBOR normalization, size admission and complete rejection effects unchanged. These exact operational facts let the raw predictor answer the selected owner's decapsulation through its CCA oracle without changing public framing or callback ordering. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalySwap
open PqxdhDeploymentIdealKeySwap (swapOwner swapSched swapNative Holds Swaps)
open PqxdhDeploymentInterface (Spec Command)
open PqxdhDeploymentNative (State)
variable {KemSK : Type}

/-- Per-owner numeric pin normalization reads no KEM secret, including every missing and non-init-sent phase. -/
theorem normalization_swap (index : Nat) (secret : KemSK) (query : Spec.Domain) (state : State KemSK) :
    CborProductionBoundary.normalizationSender query (swapNative index secret state) =
      CborProductionBoundary.normalizationSender query state := by
  rcases query with coin | command
  · rfl
  · cases command
    all_goals first | rfl | skip
    case finish owner raw =>
      simp only [CborProductionBoundary.normalizationSender, swapNative, swapSched, List.getElem?_modify]
      cases found : state.native.owners[owner]? with
      | none => rfl
      | some current =>
          by_cases same : index = owner
          · subst index
            simp only [ite_true]
            rcases current with ⟨⟨identity, keyId, pin, phase⟩, attempts⟩
            cases phase <;> rfl
          · simp only [ite_eq_right same]
            rfl

/-- Native CBOR admission depends only on unchanged public lengths, counters and sender metadata. -/
theorem allowed_swap (index : Nat) (secret : KemSK) (query : Spec.Domain) (state : State KemSK) :
    CborProductionBoundary.allowed query (swapNative index secret state) =
      CborProductionBoundary.allowed query state := by
  rcases query with coin | command
  · rfl
  · cases command
    all_goals first | rfl | skip
    case beaconSend owner plaintext =>
      simp only [CborProductionBoundary.allowed, swapNative, swapSched, List.getElem?_modify]
      cases found : state.native.owners[owner]? with
      | none => rfl
      | some current =>
          by_cases same : index = owner
          · subst index
            simp only [ite_true]
            rcases current with ⟨⟨identity, keyId, pin, phase⟩, attempts⟩
            cases phase <;> rfl
          · simp only [ite_eq_right same]
            rfl

/-- Complete rejection, including consumed pending build tokens, commutes with the selected KEM-secret replacement. -/
theorem reject_swap (index : Nat) (secret : KemSK) (query : Spec.Domain) (state : State KemSK) :
    CborProductionBoundary.reject query (swapNative index secret state) =
      Prod.map id (swapNative index secret) (CborProductionBoundary.reject query state) := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

end BeaconcryptCore.Computational.CborRawAnomalySwap

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalySwap.normalization_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalySwap.normalization_swap
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalySwap.allowed_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalySwap.allowed_swap
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalySwap.reject_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalySwap.reject_swap
