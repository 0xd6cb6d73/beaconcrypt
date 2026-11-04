-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundlePendingPin
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPrekeyMask
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource
/-! Every current symbolic source callback preserves the strong relation between a retained pending control and that same owner's original stored Server pin. Dynamic publication, corrected assigned-ID completion, failed calls and persistent platform state remain literal. The initialized path theorem derives the property from the empty actual owner roster. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativeSecretWordPendingPin (Holds Coherent holds_iff)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Terminal)
variable {n : Nat} {I Q KemSK Auxiliary Platform E A : Type} {base : OracleSpec I} {target : OracleSpec Q}
variable {source : RegistrationNativeMldsa.Source}
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem restored_holds (owners : RegistrationNativePublicOwners.State source) (valid : Holds owners) :
    RegistrationNativeSecretWordPendingPinNative.Holds (owners.map RegistrationNativePublicOwners.restore) := by
  intro owner member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have prior := (holds_iff owners).mp valid original present
  cases phase : original.view.phase
  all_goals simp only [RegistrationNativeSecretWordPendingPinNative.Coherent, Coherent, phase,
    RegistrationNativePublicOwners.restore, RegistrationBeaconReferenceCompiler.restoreOwner] at prior ⊢
  all_goals exact prior

private theorem packed_holds (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (valid : RegistrationNativeSecretWordPendingPinNative.Holds owners) :
    Holds (RegistrationNativePublicOwners.pack selected publicPrekey owners) := by
  intro index owner found
  simp only [RegistrationNativePublicOwners.pack, List.getElem?_mapIdx, Option.map_eq_some_iff] at found
  obtain ⟨original, present, rfl⟩ := found
  have prior := valid original (List.mem_of_getElem? present)
  cases phase : original.phase <;> by_cases chosen : index = selected
  all_goals simp only [chosen, ite_true, ite_false, Coherent, RegistrationNativeSecretWordPendingPinNative.Coherent, phase,
    RegistrationBeaconReferenceCompiler.eraseOwner] at prior ⊢
  all_goals exact prior

private theorem interpreted_support {Q X : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT Platform (OracleComp target))) (work : OracleComp spec X)
    (before after : Platform) (value : X)
    (present : (value, after) ∈ support ((simulateQ implementation work).run before)) : value ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq, support_map]
  exact ⟨(value, after), present, rfl⟩

theorem create_holds (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Platform (OracleComp target)))
    (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (prior : Holds owners)
    (present : result ∈ support ((((RegistrationNativePlatformPublicOwners.create implementation setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run previous)) :
    Holds result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, support_map] at present
  obtain ⟨inner, called, rfl⟩ := present
  have original := interpreted_support implementation
    (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run (owners.map RegistrationNativePublicOwners.restore)).run env)
    previous inner.2 inner.1 called
  exact packed_holds selected publicPrekey inner.1.1.2
    (RegistrationNativeSecretWordPendingPinNative.create_keeps setup edPin mlPin keyId _ env inner.1 (restored_holds owners prior) original)

theorem bundle_holds (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Platform (OracleComp target)))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform (OracleComp target)))
    (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (prior : Holds owners)
    (present : result ∈ support ((((RegistrationNativePlatformPublicOwners.bundle implementation writer setup source selected publicPrekey index).run owners).run env).run previous)) :
    Holds result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, support_map] at present
  obtain ⟨inner, called, rfl⟩ := present
  let combined : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT Platform (OracleComp target))
    | .inl query => implementation query
    | .inr query => writer query
  have original : inner.1 ∈ support
      (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run (owners.map RegistrationNativePublicOwners.restore)).run env) := by
    apply interpreted_support combined _ previous inner.2 inner.1
    have equation := RegistrationNativePlatformGenericBundle.program_evaluate (Auxiliary := Auxiliary) combined setup source index
    have invoked := congrArg (fun work => (((work.run (owners.map RegistrationNativePublicOwners.restore)).run env).run previous)) equation
    change inner ∈ support (((RegistrationNativePlatformGenericBundle.evaluate combined
      (RegistrationNativePlatformGenericBundle.program (n := n) E setup source index)).run (owners.map RegistrationNativePublicOwners.restore)).run env |>.run previous)
    rw [invoked]
    exact called
  exact packed_holds selected publicPrekey inner.1.1.2
    (RegistrationNativePlatformBundlePendingPin.program (n := n) setup index _ env inner.1 (restored_holds owners prior) original)

private theorem terminal_coherent (owner : SelectedOwner source) (valid : Terminal owner.phase) : Coherent owner := by
  cases phase : owner.phase <;> simp only [phase, Terminal] at valid
  all_goals simp only [Coherent, phase]

/-- Actual successful aborted-state consumption makes the same pending capability terminal; every other incoming outcome retains its original stored-pin relation. -/
theorem finish_coherent (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary)
    (prior : Coherent owner)
    (supported : result ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner).run env)) :
    Coherent result.1.2 := by
  have original := supported
  cases phase : owner.phase <;>
    simp only [RegistrationNativePlatformSecretWordFinish.finish, StateT.run_bind, StateT.run_get, pure_bind, phase] at supported
  all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact prior }
  case initSent pending oneTime =>
    cases moved : pending.aborted_state <;> simp only [moved] at supported
    all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact prior }
    case ok aborted =>
      exact terminal_coherent result.1.2
        (RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_consumes setup wire packet owner env pending oneTime aborted phase moved result original)

private theorem beacon_keeps
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A)
    (law : ∀ owners env previous result, Holds owners →
      result ∈ support (((work.run owners).run env).run previous) → Holds result.1.1.2)
    (before : State source Platform) (result : A × State source Platform) (prior : Holds before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.beacon work).run before)) :
    Holds result.2.1.beacons := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.beacon,StateT.run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  cases equal
  exact law before.1.beacons before.1.environment before.2 reached prior native

private theorem set_holds (owners : RegistrationNativePublicOwners.State source) (index : Nat)
    (owner : RegistrationNativePublicOwners.Owner source) (found : owners[index]?=some owner)
    (prior : Holds owners) (view : SelectedOwner source) (valid : Coherent view) :
    Holds (owners.set index {owner with view}) := by
  intro position current stored
  by_cases equal : position=index
  · subst position
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1,Option.some.injEq] at stored
    subst current
    exact valid
  · rw [List.getElem?_set_ne (Ne.symm equal)] at stored
    exact prior position current stored

private theorem finish_holds (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State source Platform) (result : RustM (Option Pqxdh.Bytes) × State source Platform)
    (prior : Holds before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) setup wire source index packet).run before)) :
    Holds result.2.1.beacons := by
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
    have kept := finish_coherent setup wire packet owner.view before.1.environment middle (prior index owner found) original
    cases equal
    exact set_holds before.1.beacons index owner found prior middle.1.2 kept

private theorem record_holds (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source Platform) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (prior : Holds before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    Holds result.2.1.beacons := by
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
    (prior : Holds before.1.beacons)
    (supported : result ∈ support ((controller request).run before)) :
    Holds result.2.1.beacons := by
  cases request with
  | inl coin =>
    simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordOrdinary.handler,
      StateT.run_lift,bind_pure_comp,support_map] at supported
    obtain ⟨_,_,equal⟩ := supported
    cases equal
    exact prior
  | inr request => cases request with
    | create edPin mlPin keyId =>
      apply beacon_keeps _ _ before result prior supported
      intro owners env previous reached valid called
      exact create_holds _ setup selectedOwner publicPrekey edPin mlPin keyId owners env previous reached valid called
    | bundle index =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordOrdinary.handler,
        StateT.run_map,support_map] at supported
      obtain ⟨reached,called,equal⟩ := supported
      cases equal
      apply beacon_keeps _ _ before reached prior called
      intro owners env previous result valid possible
      exact bundle_holds _ _ setup selectedOwner publicPrekey index owners env previous result valid possible
    | finish index packet => exact finish_holds setup wire index packet before result prior supported
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
    | serverSend keyId plaintext => exact record_holds reserveFrame (.inl (.inl (plaintext,keyId))) before result prior supported
    | serverRaw raw => exact record_holds reserveFrame (.inl (.inr raw)) before result prior supported
    | beaconSend index plaintext => exact record_holds reserveFrame (.inr (index,.inl plaintext)) before result prior supported
    | beaconRaw index raw => exact record_holds reserveFrame (.inr (index,.inr raw)) before result prior supported

variable (route : RawCtxServerRouting.SenderDecoder)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (outer : QueryImpl RegistrationNativeSecretWordService.Combined ProbComp)
local notation "sourceState" => RegistrationNativePlatformSecretWordExecution.State (State source Platform) n KemSK
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller

/-- Every interpreted current callback retains the actual pending-pin relation under the complete private-provider result. -/
theorem typed_keeps (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : sourceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range request × sourceState)
    (prior : Holds before.1.1.beacons)
    (supported : result ∈ support ((typed request).run before)) :
    Holds result.2.1.1.beacons :=
  query setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    request before.1 (result.1,result.2.1) prior
    (RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller request before result supported)

/-- Adaptive source continuations preserve the pending-pin relation without inspecting private KEM rows or root values. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : sourceState)
    (result : A × sourceState) (prior : Holds before.1.1.beacons)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    Holds result.2.1.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (fun current => Holds current.1.1.beacons)
    (fun request current valid next reached => typed_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider outer request current next valid reached)
    work before prior result supported

/-- Original full-interface callbacks retain the same strong stored-pin relation through secrecy and failed raw requests. -/
theorem full_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (request : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × sourceState)
    (result : RegistrationNativeInterface.FullSpec.Range request × (RegistrationNativeLedger.State × sourceState))
    (prior : Holds before.2.1.1.beacons)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed request).run before)) :
    Holds result.2.2.1.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  rw [RegistrationNativeRawAdapter.program_native] at called
  have kept := program_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route input inside provider outer _ before.2 reached prior called
  cases equal
  exact kept

/-- Every literal supported source prefix retains the pending capability against its original stored Server pin. -/
theorem path_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × sourceState} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after)
    (prior : Holds before.2.1.1.beacons) :
    Holds after.2.1.1.beacons :=
  RegistrationNativeSecretWordTargetPath.preserves _ (fun current => Holds current.2.1.1.beacons)
    (fun request current next valid reached => full_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider outer serverKeyId bounds request current next valid reached)
    actual prior

/-- Empty actual owner initialization derives the strong stored-pin invariant for the complete raw source run, with arbitrary prior private/platform/record state. -/
theorem run_initialized (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : sourceState) (empty : before.1.1.beacons=[])
    (result : A × (RegistrationNativeLedger.State × sourceState))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Holds result.2.2.1.1.beacons := by
  rw [RegistrationNativeFullCompiler.compile_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have initial : Holds before.1.1.beacons := by
    rw [empty]
    intro index owner found
    simp only [List.getElem?_nil] at found
    cases found
  have kept := program_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer route input inside provider outer _ before reached initial called
  cases equal
  exact kept

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.create_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.create_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.bundle_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.bundle_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.finish_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.finish_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.typed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.full_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.full_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.path_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.path_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.run_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordPendingPin.run_initialized
