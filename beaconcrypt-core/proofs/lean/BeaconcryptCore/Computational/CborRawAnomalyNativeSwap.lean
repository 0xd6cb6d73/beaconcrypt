-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalySwap

/-! Actual command-dependent raw CBOR operations commute with the selected KEM-secret replacement away from pool creation and the selected owner's decapsulation. Size refusal, pending-token consumption, per-owner normalization and actual optional writers remain in the operation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyNativeSwap
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealKeySwap (swapNative Holds Swaps onNative_swaps onShared_swaps)
open PqxdhDeploymentInterface (Spec Command)
open PqxdhDeploymentNative (State)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The generic native source also permits raw accepts, which touch only the shared Server state. -/
theorem fixed_other (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (old new : KemSK) (command : Command)
    (notCreate : ∀ pin keyId, command ≠ .create pin keyId) (notFinish : ∀ raw, command ≠ .finish index raw) :
    Swaps (swapNative index new) (fun state => Holds index old state.native.owners)
      (PqxdhDeploymentNative.handler setup codec checks route seed (.inr command))
      (PqxdhDeploymentNative.handler setup codec checks route seed (.inr command)) := by
  by_cases accepting : ∃ raw, command = .accept raw
  · obtain ⟨raw, rfl⟩ := accepting
    exact onNative_swaps index old new _ _ (onShared_swaps index old new _)
  · exact PqxdhDeploymentIdealKeySwap.nativeHandler_swaps setup codec checks route seed index old new command
      notCreate (fun raw same => accepting ⟨raw, same⟩) notFinish

/-- The actual per-command native codec is identical at the original and secret-replaced states. -/
theorem base_other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (old new : KemSK) (command : Command)
    (notCreate : ∀ pin keyId, command ≠ .create pin keyId) (notFinish : ∀ raw, command ≠ .finish index raw) :
    Swaps (swapNative index new) (fun state => Holds index old state.native.owners)
      (CborProductionBoundary.baseHandler setup wire parse checks seed (.inr command))
      (CborProductionBoundary.baseHandler setup wire parse checks seed (.inr command)) := by
  intro state held
  have original := fixed_other setup
    (PqxdhBoundaryRecordPrelude.withReader
      (CborProductionBoundary.commandCodec wire parse
        (CborProductionBoundary.normalizationSender (.inr command) state) (.inr command))
      (CborProductionBoundary.nativeReader parse)) checks
    (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed index old new command notCreate notFinish state held
  simpa only [CborProductionBoundary.baseHandler, CborCommandFilter.atState, StateT.run,
    CborRawAnomalySwap.normalization_swap] using original

private theorem rejected_owners (query : Spec.Domain) (state : State KemSK) :
    (CborProductionBoundary.reject query state).2.native.owners = state.native.owners := by
  rcases query with coin | command
  · rfl
  · cases command <;> rfl

/-- Admitted and rejected actual CBOR commands preserve the same public outcome and complete source state under selected-secret replacement. -/
theorem handler_other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (old new : KemSK) (command : Command)
    (notCreate : ∀ pin keyId, command ≠ .create pin keyId) (notFinish : ∀ raw, command ≠ .finish index raw) :
    Swaps (swapNative index new) (fun state => Holds index old state.native.owners)
      (CborProductionBoundary.handler setup wire parse checks seed (.inr command))
      (CborProductionBoundary.handler setup wire parse checks seed (.inr command)) := by
  intro state held
  simp only [CborProductionBoundary.handler, CborCommandFilter.handler, StateT.run,
    CborRawAnomalySwap.allowed_swap]
  split
  · exact base_other setup wire parse checks seed index old new command notCreate notFinish state held
  · refine ⟨?_, ?_⟩
    · simp only [CborRawAnomalySwap.reject_swap, map_pure]
    · intro result supported
      obtain rfl := (mem_support_pure_iff _ _).mp supported
      simpa only [rejected_owners] using held

end BeaconcryptCore.Computational.CborRawAnomalyNativeSwap

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNativeSwap.fixed_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNativeSwap.fixed_other
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNativeSwap.base_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNativeSwap.base_other
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNativeSwap.handler_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNativeSwap.handler_other
