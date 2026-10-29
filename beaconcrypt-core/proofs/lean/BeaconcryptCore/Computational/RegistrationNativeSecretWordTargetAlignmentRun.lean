-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentCreateSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentNoncreate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! Current public owner indices, private handles and public keys are aligned through the complete original adaptive native ledger under the early challenge provider. No creation cap, reservation availability or desired source-simulation premise is needed for this current-state invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def Holds (current : State n KemSK source) : Prop := Aligned current.1.beacons current.2.kem.1.keys

private theorem create_of_kind (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (created : RegistrationNativeRawAdapter.kind query = 1) :
    ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) := by
  cases query with
  | inl coin => cases created
  | inr command => cases command <;> first | exact ⟨_, _, _, rfl⟩ | cases created

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

/-- Every actual typed callback preserves owner/private-pair alignment, including all failed constructor branches. -/
theorem typed_keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source) (prior : Holds before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) : Holds result.2 := by
  by_cases created : RegistrationNativeRawAdapter.kind query = 1
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := create_of_kind query created
    have shape := RegistrationNativeSecretWordTargetAlignmentCreateSource.create_shape setup checks wire route sign input inside
      selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey edPin mlPin keyId before result supported
    rcases shape with same | ⟨pair, keys, owners⟩
    · unfold Holds
      rw [same.1]
      exact RegistrationNativeSecretWordTargetAlignment.same _ _ _ prior same.2
    · unfold Holds
      rw [keys]
      exact RegistrationNativeSecretWordTargetAlignment.append _ _ _ pair prior owners
  · exact RegistrationNativeSecretWordTargetAlignmentNoncreate.typed_aligned setup checks wire route sign input inside
      selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey query created before prior result supported

/-- Arbitrary adaptive typed programs preserve the same current-state alignment. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) (prior : Holds before) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ typed work).run before)) : Holds result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed Holds
    (fun query current valid next reached => typed_keeps setup checks wire route sign input inside
      selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey query current valid next reached)
    work before prior result supported

/-- The actual bounded raw adapter preserves alignment on malformed and successful registration paths. -/
theorem raw_program_keeps (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : State n KemSK source) (prior : Holds before) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Holds result.2 := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey _ before prior result supported

/-- Original private secrecy draws and internal native sends retain the same actual key/owner alignment below the unchanged ledger. -/
theorem full_step_keeps (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source) (prior : Holds before.2)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
      typed query).run before)) : Holds result.2.2 := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact raw_program_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey _ before.2 prior inner reached

/-- Every complete original native game run retains current alignment from its actual initial alignment. -/
theorem run_keeps (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) (prior : Holds before)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds result.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (fun current => Holds current.2)
    (fun query current valid next reached => full_step_keeps setup checks wire route sign input inside
      selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey serverKeyId bounds query current valid next reached)
    _ (RegistrationNativeLedger.empty, before) prior result supported

/-- With the actual empty owner and key lists, the full original game needs no supplied alignment certificate. -/
theorem initialized (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK source) (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds result.2.2 := by
  apply run_keeps setup checks wire route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before _ result supported
  simp only [Holds, ownersEmpty, keysEmpty]
  exact RegistrationNativeSecretWordTargetAlignment.empty

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.typed_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.raw_program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.raw_program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.full_step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.full_step_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.run_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAlignmentRun.initialized
