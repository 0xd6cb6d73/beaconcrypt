-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateCall
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseReceipts

/-! A canonical original successful accept in the candidate hybrid reaches the selected open SDK before any candidate phase exists. This fact is derived over the original adaptive full ledger; early owner creation, prechallenge decapsulation and failed accepted attempts stay eligible. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidatePhaseCall
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State counter)
open RegistrationNativeKemOpenPhaseCounter (Safe)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Literal full-ledger receipts put the canonical selected successful SDK call before the actual first candidate getter. -/
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
      RegistrationNativeEvents.parsedAcceptCount wire pre = parsed ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      counter first = parsed ∧ first.2 = none ∧
      (some (.ok (some session)), last) ∈ support
        (((simulateQ provider (simulateQ (RegistrationNativeKemOpenFrame.lower true)
          (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) := by
  obtain ⟨pre, raw, packet, post, trace, count, read, _first⟩ := accepted
  have receipts := (RegistrationNativeKemOpenPhaseReceipts.program_receipts setup checks wire route representation created credential
    selected pairs publicKey real parsed bounds mode work before after safe value ledger supported).2.2
  obtain ⟨first, last, safeFirst, counted, reached⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session⟩ post trace
  have countedFirst : counter first = parsed := by simpa only [zero, Nat.zero_add, count] using counted
  have noPhase : first.2 = none := safeFirst (by omega)
  have typed := RegistrationNativeKemOpenTargetCall.raw_success setup checks wire route representation created credential
    selected pairs publicKey real parsed raw packet session first last read reached
  exact ⟨pre, raw, packet, post, ((RegistrationNativeKemServerState.mask first.1.1, first.1.2), first.2), last,
    trace, count, read, countedFirst, noPhase,
    RegistrationNativeKemOpenTargetCall.selected_success setup checks wire route representation created credential
      selected pairs publicKey real parsed packet session first last countedFirst typed⟩

/-- Every actual candidate-hybrid canonical successful accept retains that original successful SDK call at an inactive private phase, without a no-prior-finish premise. -/
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
      RegistrationNativeEvents.parsedAcceptCount wire pre = parsed ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      counter first = parsed ∧ first.2 = none ∧
      (some (.ok (some session)), last) ∈ support
        (((simulateQ (RegistrationNativeKemOpenProvider.implementation setup checks wire route representation created credential
          selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true)
            (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) := by
  obtain ⟨phase, reached⟩ := RegistrationNativeKemSwitchProgram.observation_support setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) real selected chosen others
    (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)
    (localState, PqxdhDynamicKemRouter.empty) record supported
  rw [returned] at reached
  exact open_call setup checks wire route representation created credential
    selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real parsed bounds mode work
    ((localState, PqxdhDynamicKemRouter.empty), none) (record.finalState, phase) zero (fun _ => rfl)
    value ledger session reached accepted

end BeaconcryptCore.Computational.RegistrationNativeKemCandidatePhaseCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidatePhaseCall.open_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidatePhaseCall.open_call
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidatePhaseCall.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidatePhaseCall.accepted_call
