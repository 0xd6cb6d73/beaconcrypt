-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenLinkedReceipts
import BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation

/-! The original canonical accept, actual successful open SDK call and the same run's sampled candidate phase are witnessed together. The receipt does not combine unrelated source executions or discard the original private secrecy ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State counter)
open RegistrationNativeKemOpenPhaseCounter (Safe)
open RegistrationNativeKemOpenPhaseOrder (Extends)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Original full-ledger execution derives a single actual canonical SDK call whose postphase is linked to that same full run. -/
theorem open_call (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before after : State n mlSource KemSK) (zero : counter before = 0) (safe : Safe parsed before)
    (value : Value) (ledger : RegistrationNativeLedger.State) (session : Nat)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before))
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire ledger.transcript session parsed) :
    ∃ pre raw packet post, ∃ first last : State n mlSource KemSK,
      ledger.transcript = pre ++ (RegistrationNativeInterface.Entry.mk (.inl (.inr (.accept raw))) (some session)) :: post ∧
      PqxdhDeploymentTranscript.acceptOf (ledger.transcript.map RegistrationNativeInterface.Entry.erase) session = some raw ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre = parsed ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      counter first = parsed ∧ first.2 = none ∧ Extends last.2 after.2 ∧
      (some (.ok (some session)), last) ∈ support
        (((simulateQ provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
          (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) := by
  obtain ⟨pre, raw, packet, post, trace, count, read, canonicalFirst⟩ := accepted
  have receipts := (RegistrationNativeKemOpenLinkedReceipts.program_receipts setup checks wire route representation created credential
    selected pairs publicKey real parsed bounds mode work before after safe value ledger supported).2.2
  obtain ⟨first, last, safeFirst, counted, linked, reached⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session⟩ post trace
  have countedFirst : counter first = parsed := by simpa only [zero, Nat.zero_add, count] using counted
  have noPhase : first.2 = none := safeFirst (by omega)
  have typed := RegistrationNativeKemOpenTargetCall.raw_success setup checks wire route representation created credential
    selected pairs publicKey real parsed raw packet session first last read reached
  exact ⟨pre, raw, packet, post, ((RegistrationNativeKemServerState.mask first.1.1, first.1.2), first.2), last,
    trace, canonicalFirst, count, read, countedFirst, noPhase, linked,
    RegistrationNativeKemOpenTargetCall.selected_success setup checks wire route representation created credential
      selected pairs publicKey real parsed packet session first last countedFirst typed⟩

/-- The complete actual candidate observation derives its original selected SDK call jointly with the same sampled candidate label. -/
theorem accepted_call (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (localState : RegistrationNativeKemServerState.State n mlSource) (zero : localState.parsedAccepts = 0)
    (record : RegistrationNativeKemCandidateObservation.Record (RegistrationNativeKemParsedRouting.Ambient n mlSource)
      KemSK (RegistrationNativeKemServerState.State n mlSource) (Value × RegistrationNativeLedger.State))
    (supported : record ∈ support (RegistrationNativeKemCandidateObservation.run setup.baseImpl setup.kem
      (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) selected chosen others
      (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)
      (localState, PqxdhDynamicKemRouter.empty) 0 real))
    (value : Value) (ledger : RegistrationNativeLedger.State) (returned : record.value = some (value, ledger)) (session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire ledger.transcript session parsed) :
    ∃ pre raw packet post, ∃ first last : State n mlSource KemSK,
      ledger.transcript = pre ++ (RegistrationNativeInterface.Entry.mk (.inl (.inr (.accept raw))) (some session)) :: post ∧
      PqxdhDeploymentTranscript.acceptOf (ledger.transcript.map RegistrationNativeInterface.Entry.erase) session = some raw ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre = parsed ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      counter first = parsed ∧ first.2 = none ∧
      Extends last.2 (RegistrationNativeKemSwitchObservation.phase record.cut (record.encapsulation.1, record.candidate real)) ∧
      (some (.ok (some session)), last) ∈ support
        (((simulateQ (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true)
            (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) := by
  have reached := RegistrationNativeKemSwitchObservation.observation_support setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) real selected chosen others
    (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)
    (localState, PqxdhDynamicKemRouter.empty) record supported
  rw [RegistrationNativeKemSwitchObservation.observe, returned] at reached
  exact open_call setup checks wire route representation created credential
    selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real parsed bounds mode work
    ((localState, PqxdhDynamicKemRouter.empty), none) _ zero (fun _ => rfl) value ledger session reached accepted

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall.open_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall.open_call
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateLinkedCall.accepted_call
