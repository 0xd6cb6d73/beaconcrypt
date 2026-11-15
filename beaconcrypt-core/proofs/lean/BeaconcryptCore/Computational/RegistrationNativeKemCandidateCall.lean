-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall

/-! Canonical successful accepts in the actual first-getter candidate hybrid retain their original parsed prefix and literal successful open SDK call. The source-cut observation and whole optional provider are related by a proved operational law, with no additional event premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateCall
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeWire (Wire)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

/-- The actual candidate run supplies an original successful selected accept under its open candidate provider, including its native preincrement counter. -/
theorem accepted_call (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (parsed : Nat) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) (real : Bool)
    (localState : RegistrationNativeKemServerState.State n mlSource) (zero : localState.parsedAccepts = 0)
    (record : RegistrationNativeKemCandidateObservation.Record (RegistrationNativeKemParsedRouting.Ambient n mlSource)
      KemSK (RegistrationNativeKemServerState.State n mlSource) (Value × RegistrationNativeLedger.State))
    (supported : record ∈ support (RegistrationNativeKemCandidateObservation.run setup.baseImpl setup.kem
      (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) selected chosen others
      (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)
      (localState, PqxdhDynamicKemRouter.empty) 0 real))
    (value : Value) (ledger : RegistrationNativeLedger.State) (returned : record.value = some (value, ledger)) (session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire ledger.transcript session parsed) :
    ∃ pre raw packet post, ∃ first last : RegistrationNativeKemOpenProvider.State n mlSource KemSK,
      ledger.transcript = pre ++ (RegistrationNativeInterface.Entry.mk (.inl (.inr (.accept raw))) (some session)) :: post ∧
      RegistrationNativeEvents.parsedAcceptCount wire pre = parsed ∧
      RegistrationNativeWire.readInit wire raw = some packet ∧ RegistrationNativeKemOpenProvider.counter first = parsed ∧
      (some (.ok (some session)), last) ∈ support
        (((simulateQ (RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential
          selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real)
          (simulateQ (RegistrationNativeKemOpenFrame.lower true)
            (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run first) := by
  obtain ⟨phase, reached⟩ := RegistrationNativeKemSwitchProgram.observation_support setup.baseImpl setup.kem
    (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential) real selected chosen others
    (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)
    (localState, PqxdhDynamicKemRouter.empty) record supported
  rw [returned] at reached
  exact RegistrationNativeKemOpenTargetCall.call_of_accept setup checks wire route representation created credential
    selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real parsed bounds mode work
    ((localState, PqxdhDynamicKemRouter.empty), none) (record.finalState, phase) zero value ledger session reached accepted

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateCall.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateCall.accepted_call
