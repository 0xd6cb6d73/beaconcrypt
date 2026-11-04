-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveState
/-! The current symbolic source preserves the actual selected public-prekey mask. Constructors and dynamic bundles pack every reached output; corrected incoming completion preserves the exact prekey and optional scalar fields. No signing origin, callback identity or key-injectivity premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativePublicOwnerMask (Canonical At)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem packed (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A)
    (before : State source Platform) (result : A × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.beacon
      (RegistrationNativePlatformPublicOwners.executeLocal selected publicPrekey work)).run before)) :
    Canonical selected publicPrekey result.2.1.beacons := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.beacon,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have canonical := RegistrationNativePlatformPublicOwnerState.executeLocal_canonical selected publicPrekey work
    before.1.beacons before.1.environment before.2 reached native
  cases equal
  exact canonical

private theorem set_canonical (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source) (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (found : owners[index]? = some owner) (prior : Canonical selected publicPrekey owners)
    (view : RegistrationBeaconReferenceCompiler.SelectedOwner source) (same : view.prekeyPublic=owner.view.prekeyPublic) :
    Canonical selected publicPrekey (owners.set index {owner with view}) := by
  intro position current stored
  by_cases equal : position=index
  · subst position
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1,Option.some.injEq] at stored
    subst current
    simpa only [At,same] using prior index owner found
  · rw [List.getElem?_set_ne (Ne.symm equal)] at stored
    exact prior position current stored

private theorem finish_canonical (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State source Platform) (result : RustM (Option Pqxdh.Bytes) × State source Platform)
    (prior : Canonical selected publicPrekey before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) setup wire source index packet).run before)) :
    Canonical selected publicPrekey result.2.1.beacons := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish,StateT.run] at supported
  cases found : before.1.beacons[index]? with
  | none =>
    simp only [found,mem_support_pure_iff] at supported
    cases supported
    exact prior
  | some owner =>
    simp only [found,support_map] at supported
    obtain ⟨middle,reached,equal⟩ := supported
    have localSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
    have original : middle ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner.view).run before.1.environment) := by
      cases own : owner.scalar with
      | none => simpa only [own,StateT.run] using localSupport
      | some scalar =>
        simp only [own] at localSupport
        exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ localSupport
    have kept := RegistrationNativePlatformSecretWordPrekeyFinish.finish setup wire packet owner.view before.1.environment middle original
    cases equal
    exact set_canonical selected publicPrekey before.1.beacons index owner found prior middle.1.2 kept

private theorem record_canonical (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source Platform) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (prior : Canonical selected publicPrekey before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    Canonical selected publicPrekey result.2.1.beacons := by
  rcases query with (_ | _) | ⟨index,_ | _⟩
  all_goals simp only [RegistrationNativePlatformSecretWordOrdinary.record,StateT.run] at supported
  all_goals try split at supported
  all_goals first
    | rw [mem_support_pure_iff] at supported; cases supported; exact prior
    | rw [support_map] at supported; obtain ⟨_,_,equal⟩ := supported; cases equal; exact prior
    | rw [mem_support_bind_iff] at supported; obtain ⟨_,_,supported⟩ := supported
      rw [mem_support_bind_iff] at supported; obtain ⟨_,_,supported⟩ := supported
      rw [mem_support_pure_iff] at supported; cases supported; exact prior

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- Every actual current free callback preserves the selected mask through all platform/source outcomes. -/
theorem query (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range request × State source Platform)
    (prior : Canonical selectedOwner publicPrekey before.1.beacons)
    (supported : result ∈ support ((controller request).run before)) :
    Canonical selectedOwner publicPrekey result.2.1.beacons := by
  cases request with
  | inl coin =>
    simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordOrdinary.handler,
      StateT.run_lift,bind_pure_comp,support_map] at supported
    obtain ⟨_,_,equal⟩ := supported
    cases equal
    exact prior
  | inr request => cases request with
    | create edPin mlPin keyId => exact packed selectedOwner publicPrekey _ before result supported
    | bundle index =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_map,support_map] at supported
      obtain ⟨reached,called,equal⟩ := supported
      cases equal
      exact packed selectedOwner publicPrekey _ before reached called
    | finish index packet => exact finish_canonical setup wire selectedOwner publicPrekey index packet before result prior supported
    | accept packet =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.accept,
        StateT.run_bind,StateT.run_get,StateT.run_modify,pure_bind] at supported
      simp only [RegistrationNativePlatformSecretWordFrontend.serverOpen,StateT.run,support_map] at supported
      obtain ⟨_,_,equal⟩ := supported
      cases equal
      exact prior
    | build handle application =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.build,
        StateT.run,support_map] at supported
      obtain ⟨_,_,equal⟩ := supported
      cases equal
      exact prior
    | hmac key bytes =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact prior
    | hash bytes =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_lift,bind_pure_comp,support_map] at supported
      obtain ⟨_,_,equal⟩ := supported
      cases equal
      exact prior
    | serverSend keyId plaintext => exact record_canonical reserveFrame selectedOwner publicPrekey (.inl (.inl (plaintext,keyId))) before result prior supported
    | serverRaw raw => exact record_canonical reserveFrame selectedOwner publicPrekey (.inl (.inr raw)) before result prior supported
    | beaconSend index plaintext => exact record_canonical reserveFrame selectedOwner publicPrekey (.inr (index,.inl plaintext)) before result prior supported
    | beaconRaw index raw => exact record_canonical reserveFrame selectedOwner publicPrekey (.inr (index,.inr raw)) before result prior supported

variable (route : RawCtxServerRouting.SenderDecoder)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (outer : QueryImpl RegistrationNativeSecretWordService.Combined ProbComp)
local notation "sourceState" => RegistrationNativePlatformSecretWordExecution.State (State source Platform) n KemSK
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller

/-- Every interpreted current callback retains the actual mask under the complete private-provider result. -/
theorem typed_keeps (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : sourceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range request × sourceState)
    (prior : Canonical selectedOwner publicPrekey before.1.1.beacons)
    (supported : result ∈ support ((typed request).run before)) :
    Canonical selectedOwner publicPrekey result.2.1.1.beacons :=
  query setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    request before.1 (result.1,result.2.1) prior
    (RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller request before result supported)

/-- Adaptive source continuations preserve the mask without inspecting private KEM rows or root values. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : sourceState)
    (result : A × sourceState) (prior : Canonical selectedOwner publicPrekey before.1.1.beacons)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    Canonical selectedOwner publicPrekey result.2.1.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (fun current => Canonical selectedOwner publicPrekey current.1.1.beacons)
    (fun request current valid next reached => typed_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider outer request current next valid reached)
    work before prior result supported

/-- Original full-interface callbacks retain the same public-prekey mask through secrecy and failed raw requests. -/
theorem full_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (request : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × sourceState)
    (result : RegistrationNativeInterface.FullSpec.Range request × (RegistrationNativeLedger.State × sourceState))
    (prior : Canonical selectedOwner publicPrekey before.2.1.1.beacons)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed request).run before)) :
    Canonical selectedOwner publicPrekey result.2.2.1.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  rw [RegistrationNativeRawAdapter.program_native] at called
  have kept := program_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route input inside provider outer _ before.2 reached prior called
  cases equal
  exact kept

/-- Every literal supported source prefix retains the mask used by the actual publication at that prefix. -/
theorem path_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × sourceState} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after)
    (prior : Canonical selectedOwner publicPrekey before.2.1.1.beacons) :
    Canonical selectedOwner publicPrekey after.2.1.1.beacons :=
  RegistrationNativeSecretWordTargetPath.preserves _ (fun current => Canonical selectedOwner publicPrekey current.2.1.1.beacons)
    (fun request current next valid reached => full_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider outer serverKeyId bounds request current next valid reached)
    actual prior

/-- Empty actual owner initialization derives the mask for the complete raw source run, with arbitrary prior private/platform/record state. -/
theorem run_initialized (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : sourceState) (empty : before.1.1.beacons=[])
    (result : A × (RegistrationNativeLedger.State × sourceState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Canonical selectedOwner publicPrekey result.2.2.1.1.beacons := by
  rw [RegistrationNativeFullCompiler.compile_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have initial : Canonical selectedOwner publicPrekey before.1.1.beacons := by
    rw [empty]
    exact RegistrationNativePublicOwnerMask.empty _ _
  have kept := program_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route input inside provider outer _ before reached initial called
  cases equal
  exact kept

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.typed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.full_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.full_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.path_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.path_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.run_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask.run_initialized
