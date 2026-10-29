-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! The concrete early Word execution derives an absent getter marker at every reached state whose parsed counter has not passed the selected attempt. The invariant covers actual original private secrecy draws and arbitrary raw failures. It depends on execution from an absent marker, never on a counter-only inference or a successful target mark. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Holds (selectedAccept : Nat) (state : State n KemSK source) : Prop :=
  state.1.parsedAccepts ≤ selectedAccept → state.2.kem.2 = none

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selected selectedAccept publicPrekey

/-- Every actual typed operation preserves the reached-prefix absent-marker invariant. -/
theorem typed_keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (prior : Holds selectedAccept before) (supported : result ∈ support ((typed query).run before)) :
    Holds selectedAccept result.2 := by
  intro below
  have counted := RegistrationNativeSecretWordTargetSource.typed_counter setup checks wire route sign input inside provider outer
    selected selectedAccept publicPrekey query before result supported
  have earlier : before.1.parsedAccepts ≤ selectedAccept := by omega
  have ordinary : ¬(RegistrationNativeSecretWordTargetCounter.isAccept query = true ∧ before.1.parsedAccepts = selectedAccept) := by
    rintro ⟨accepted, equal⟩
    rw [accepted, Bool.toNat_true, equal] at counted
    omega
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have unchanged := RegistrationNativeSecretWordTargetPhaseCore.program_phase setup wire route sign input inside
    selected pairs publicKey challenge outer _
    (RegistrationNativeSecretWordTargetPhaseCore.handler_free setup checks wire sign selected selectedAccept publicPrekey
      query before.1 ordinary) before.2 reached called
  cases equal
  exact unchanged.trans (prior earlier)

/-- Arbitrary actual typed continuations retain the reached-prefix marker invariant. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (prior : Holds selectedAccept before) (supported : result ∈ support ((simulateQ typed work).run before)) :
    Holds selectedAccept result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (Holds selectedAccept)
    (fun query current valid next called => typed_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
      selectedAccept publicPrekey query current next valid called) work before prior result supported

private theorem raw_keeps (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (prior : Holds selectedAccept before)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Holds selectedAccept result.2 := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedAccept publicPrekey _ before result prior supported

/-- The full original ledger step retains the same marker invariant below every real secrecy draw and refused send. -/
theorem full_step_keeps (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (prior : Holds selectedAccept before.2)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Holds selectedAccept result.2.2 := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact raw_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedAccept publicPrekey _ before.2 inner prior called

/-- Every initialized actual original-ledger run derives this invariant from its literal absent provider marker. -/
theorem run_keeps (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) (initialMarker : before.2.kem.2 = none)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds selectedAccept result.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (fun current => Holds selectedAccept current.2)
    (fun query current valid next called => full_step_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
      selectedAccept publicPrekey serverKeyId bounds query current next valid called)
    _ (RegistrationNativeLedger.empty, before) (fun _ => initialMarker) result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.typed_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.full_step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.full_step_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase.run_keeps
