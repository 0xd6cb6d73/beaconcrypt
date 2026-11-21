-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys
/-! A source Word interpretation exposes only its individual preparation, genuine routed KEM and nonrouted KEM-frame receipts. The contract contains no source callback, roster alignment or security conclusion. Actual native birth and source prefix invariants are derived from these leaves separately, retaining arbitrary persistent World state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Private A : Type} {base : OracleSpec I}

variable (setup : Setup base KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
variable (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))


include contract in
/-- Every actual nonselected-getter Word leaf preserves its complete reached marker under the granular source KEM contract. -/
theorem query_phase (query : (Spec n KemSK).Domain)
    (quiet : ¬RegistrationNativeSecretWordTargetPhaseCore.Selected query)
    (before : Private) (result : (Spec n KemSK).Range query × Private)
    (supported : result ∈ support ((implementation query).run before)) :
    (kem result.2).2 = (kem before).2 := by
  rcases query with (message | (message | common) | routed) | record
  · exact congrArg Prod.snd (contract.quiet (.inl (.inl message)) trivial before result supported)
  · exact congrArg Prod.snd (contract.quiet (.inl (.inr (.inl (.inl message)))) trivial before result supported)
  · exact congrArg Prod.snd (contract.quiet (.inl (.inr (.inl (.inr common)))) trivial before result supported)
  · have actual := contract.routed routed before result supported
    have ordinary : ¬RegistrationNativeKemRouting.IsExposed (ambient := RegistrationNativeKemInterface.OtherSpec) (KemSK := KemSK) routed := by
      rcases routed with (other | key) | pool | key
      · trivial
      · trivial
      · trivial
      · exact quiet
    exact RegistrationNativeSecretWordKemEarlyKeys.nonexposed_phase setup.baseImpl setup.kem selected pairs publicKey challenge
      routed ordinary (kem before) (result.1,kem result.2) actual
  · exact congrArg Prod.snd (contract.quiet (.inr record) trivial before result supported)

include contract in
/-- A source continuation with no selected getter retains its current marker independently of ordinary World replies. -/
theorem program_phase (work : OracleComp (Spec n KemSK) A)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetPhaseCore.Selected (KemSK := KemSK)) 0)
    (before : Private) (result : A × Private)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    (kem result.2).2 = (kem before).2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    obtain ⟨first,later⟩ := bounded
    have quiet := first.resolve_right (by omega)
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact (ih middle.1 (by simpa using later middle.1) middle.2 result continued).trans
      (query_phase setup selected pairs publicKey challenge implementation kem input contract query quiet before middle called)

variable {Platform E : Type} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "State" => RegistrationNativePlatformLorSourceAlignment.State source Platform Private
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller

def Holds {source : RegistrationNativeMldsa.Source} (parsed : Nat)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
    (state : RegistrationNativePlatformLorSourceAlignment.State source Platform Private) : Prop :=
  state.1.1.parsedAccepts ≤ parsed → (kem state.2).2 = none

include contract in
/-- Every actual typed step retains an absent marker before the selected parsed accept, including all failures. -/
theorem typed_keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State)
    (prior : Holds selectedAccept kem before) (supported : result ∈ support ((typed query).run before)) :
    Holds selectedAccept kem result.2 := by
  intro below
  have counted := RegistrationNativePlatformLorSourceAlignment.typed_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation query before result supported
  have earlier : before.1.1.parsedAccepts ≤ selectedAccept := by omega
  have ordinary : ¬(RegistrationNativeSecretWordTargetCounter.isAccept query = true ∧ before.1.1.parsedAccepts = selectedAccept) := by
    rintro ⟨accepted,equal⟩
    rw [accepted,Bool.toNat_true,equal] at counted
    omega
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have unchanged := program_phase setup selected pairs publicKey challenge implementation kem input contract _
    (RegistrationNativePlatformSecretWordTargetPhaseSyntax.handler_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 ordinary) before.2 reached called
  cases equal
  exact unchanged.trans (prior earlier)

include contract in
/-- Adaptive actual typed execution preserves the same absent-marker prefix invariant. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : State) (result : A × State)
    (prior : Holds selectedAccept kem before) (supported : result ∈ support ((simulateQ typed work).run before)) :
    Holds selectedAccept kem result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (Holds selectedAccept kem)
    (fun query current valid next called => typed_keeps setup selected pairs publicKey challenge implementation kem input contract checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current next valid called)
    work before prior result supported

include contract in
private theorem raw_keeps (work : OracleComp RegistrationNativeInterface.Spec A) (before : State) (result : A × State)
    (prior : Holds selectedAccept kem before)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Holds selectedAccept kem result.2 := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_keeps setup selected pairs publicKey challenge implementation kem input contract checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result prior supported

include contract in
/-- Every full original ledger callback retains the reached-prefix marker invariant. -/
theorem full_step_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State) (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State))
    (prior : Holds selectedAccept kem before.2)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Holds selectedAccept kem result.2.2 := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact raw_keeps setup selected pairs publicKey challenge implementation kem input contract checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before.2 inner prior called

include contract in
/-- Every same-execution chronological prefix preserves its original selected-marker condition. -/
theorem path_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after)
    (prior : Holds selectedAccept kem before.2) : Holds selectedAccept kem after.2 :=
  RegistrationNativeSecretWordTargetPath.preserves _ (fun current => Holds selectedAccept kem current.2)
    (fun query current next valid called => full_step_keeps setup selected pairs publicKey challenge implementation kem input contract checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds query current next valid called) actual prior

include contract in
/-- Literal empty-marker initialization derives every full raw run's reached-prefix condition. -/
theorem run_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State) (initialMarker : (kem before.2).2 = none)
    (result : A × (RegistrationNativeLedger.State × State))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds selectedAccept kem result.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed)
    (fun current => Holds selectedAccept kem current.2)
    (fun query current valid next called => full_step_keeps setup selected pairs publicKey challenge implementation kem input contract checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds query current next valid called)
    _ (RegistrationNativeLedger.empty,before) (fun _ => initialMarker) result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.query_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.query_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.program_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.program_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.typed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.full_step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.full_step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.path_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.path_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePhase.run_keeps
