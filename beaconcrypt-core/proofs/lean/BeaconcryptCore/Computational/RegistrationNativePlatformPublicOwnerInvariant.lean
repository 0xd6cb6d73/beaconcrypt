-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerState
/-! Canonical masking and pending coherence are internal invariants of the actual corrected mixed public frontend. The effectful Init writer, assigned-ID finish and all other callbacks preserve them on every free outcome; adaptive and raw compiled clients inherit the same properties. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicOwnerState (Valid)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {E Platform ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private def Keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : LocalM n KemSK Platform source Value) : Prop :=
  ∀ before result, Valid selected publicPrekey before.1.beacons →
    result ∈ support (work.run before) → Valid selected publicPrekey result.2.1.beacons

private theorem pure_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (value : Value) :
    Keeps selected publicPrekey (pure value : LocalM n KemSK Platform source Value) := by
  intro before result prior present
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem bind_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : LocalM n KemSK Platform source Value) (next : Value → LocalM n KemSK Platform source Next)
    (first : Keeps selected publicPrekey work) (rest : ∀ value, Keeps selected publicPrekey (next value)) :
    Keeps selected publicPrekey (work >>= next) := by
  intro before result prior present
  simp only [StateT.run_bind, mem_support_bind_iff] at present
  obtain ⟨middle, called, continued⟩ := present
  exact rest middle.1 middle.2 result (first before middle prior called) continued

private theorem lift_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp (LocalSpec n KemSK) Value) :
    Keeps selected publicPrekey (StateT.lift work : LocalM n KemSK Platform source Value) := by
  intro before result prior present
  simp only [StateT.run_lift, bind_pure_comp, support_map] at present
  obtain ⟨value, _called, rfl⟩ := present
  exact prior

private theorem execute_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : LocalM n KemSK Platform source Value) (law : Keeps selected publicPrekey work)
    (before : State source Platform) (result : Value × State source Platform)
    (prior : Valid selected publicPrekey before.1.beacons)
    (present : result ∈ support ((executeLocal work).run before)) : Valid selected publicPrekey result.2.1.beacons :=
  law before result prior (RegistrationNativePublicSourceSupport.simulate_support embedLocal _ result present)

private theorem beacon_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State (Base n KemSK Platform) Value)
    (law : ∀ owners env previous result, Valid selected publicPrekey owners →
      result ∈ support (((work.run owners).run env).run previous) → Valid selected publicPrekey result.1.1.2) :
    Keeps selected publicPrekey (beacon work) := by
  intro before result prior present
  simp only [beacon, StateT.run, support_map] at present
  obtain ⟨inner, called, rfl⟩ := present
  exact law before.1.beacons before.1.environment before.2 inner prior called

private theorem server_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativePlatformServerReferenceAccept.PublicM (Base n KemSK Platform) Value) :
    Keeps selected publicPrekey (serverOpen (source := source) work) := by
  intro before result prior present
  simp only [serverOpen, StateT.run, support_map] at present
  obtain ⟨inner, _called, rfl⟩ := present
  exact prior

private theorem get_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    Keeps selected publicPrekey (get : LocalM n KemSK Platform source (State source Platform)) := by
  intro before result prior present
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem increment_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    Keeps selected publicPrekey ((modify fun (current : State source Platform) =>
      ({current.1 with parsedAccepts := current.1.parsedAccepts + 1}, current.2)) : LocalM n KemSK Platform source Unit) := by
  intro before result prior present
  simp only [StateT.run_modify, support_pure, Set.mem_singleton_iff] at present
  cases present
  exact prior

private theorem record_keeps (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source Platform) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (prior : Valid selected publicPrekey before.1.beacons)
    (present : result ∈ support ((record (n := n) (KemSK := KemSK) reserve query).run before)) : Valid selected publicPrekey result.2.1.beacons := by
  cases query with
  | inl query => cases query with
    | inl send =>
      simp only [record, StateT.run, mem_support_bind_iff] at present
      obtain ⟨reply, _queried, changed, _gated, returned⟩ := present
      simp only [support_pure, Set.mem_singleton_iff] at returned
      cases returned
      exact prior
    | inr raw =>
      simp only [record, StateT.run, support_map] at present
      obtain ⟨reply, _queried, rfl⟩ := present
      exact prior
  | inr query => rcases query with ⟨index, query⟩; cases query with
    | inl plaintext =>
      simp only [record, StateT.run] at present
      cases found : before.1.beacons[index]? with
      | none =>
        simp only [found, support_pure, Set.mem_singleton_iff] at present
        cases present
        exact prior
      | some owner =>
        simp only [found, mem_support_bind_iff] at present
        obtain ⟨reply, _queried, changed, _gated, returned⟩ := present
        simp only [support_pure, Set.mem_singleton_iff] at returned
        cases returned
        exact prior
    | inr raw =>
      simp only [record, StateT.run] at present
      cases found : before.1.beacons[index]? with
      | none =>
        simp only [found, support_pure, Set.mem_singleton_iff] at present
        cases present
        exact prior
      | some owner =>
        simp only [found, support_map] at present
        obtain ⟨reply, _queried, rfl⟩ := present
        exact prior

/-- Every actual corrected callback preserves canonical selected masking and every pending control/pin equation, with no whole callback or frame premise. -/
theorem handler [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (before : State source Platform) (result : TypedSpec.Range query × State source Platform)
    (prior : Valid selectedOwner publicPrekey before.1.beacons)
    (present : result ∈ support ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept
      publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    Valid selectedOwner publicPrekey result.2.1.beacons := by
  cases query with
  | inl coin => exact execute_keeps selectedOwner publicPrekey _ (lift_keeps selectedOwner publicPrekey _) before result prior present
  | inr command => cases command with
    | create edPin mlPin keyId =>
      apply execute_keeps selectedOwner publicPrekey _ (beacon_keeps selectedOwner publicPrekey _ ?_) before result prior present
      intro owners env previous output valid called
      exact ⟨RegistrationNativePlatformPublicOwnerState.executeLocal_canonical _ _ _ _ _ _ output called,
        RegistrationNativePlatformPublicOwnerState.create_coherent _ setup selectedOwner publicPrekey edPin mlPin keyId
          owners env previous output valid.2 called⟩
    | bundle index =>
      apply execute_keeps selectedOwner publicPrekey _ ?_ before result prior present
      intro current output valid called
      simp only [StateT.run_map, support_map] at called
      obtain ⟨inner, reached, rfl⟩ := called
      apply beacon_keeps selectedOwner publicPrekey _ ?_ current inner valid reached
      intro owners env previous output valid called
      exact ⟨RegistrationNativePlatformPublicOwnerState.executeLocal_canonical _ _ _ _ _ _ output called,
        RegistrationNativePlatformPublicOwnerState.bundle_coherent _ _ setup selectedOwner publicPrekey index owners env previous output valid.2 called⟩
    | accept packet =>
      apply execute_keeps selectedOwner publicPrekey _ ?_ before result prior present
      exact bind_keeps selectedOwner publicPrekey _ _ (get_keeps selectedOwner publicPrekey) (fun _ =>
        bind_keeps selectedOwner publicPrekey _ _ (increment_keeps selectedOwner publicPrekey) (fun _ => server_keeps selectedOwner publicPrekey _))
    | build handle application =>
      apply execute_keeps selectedOwner publicPrekey _ ?_ before result prior present
      intro current output valid called
      simp only [build, StateT.run, support_map] at called
      obtain ⟨inner, _reached, rfl⟩ := called
      exact valid
    | finish index packet =>
      apply execute_keeps selectedOwner publicPrekey _ (beacon_keeps selectedOwner publicPrekey _ ?_) before result prior present
      intro owners env previous output valid called
      exact RegistrationNativePlatformPublicOwnerState.finish_valid setup wire selectedOwner publicPrekey index packet owners env previous output valid called
    | hmac key bytes =>
      simp only [RegistrationNativePlatformPublicFrontend.handler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
      cases present
      exact prior
    | hash bytes => exact execute_keeps selectedOwner publicPrekey _ (lift_keeps selectedOwner publicPrekey _) before result prior present
    | serverSend keyId plaintext => exact record_keeps reserveFrame selectedOwner publicPrekey (.inl (.inl (plaintext, keyId))) before result prior present
    | serverRaw raw => exact record_keeps reserveFrame selectedOwner publicPrekey (.inl (.inr raw)) before result prior present
    | beaconSend index plaintext => exact record_keeps reserveFrame selectedOwner publicPrekey (.inr (index, .inl plaintext)) before result prior present
    | beaconRaw index raw => exact record_keeps reserveFrame selectedOwner publicPrekey (.inr (index, .inr raw)) before result prior present

/-- All adaptive typed clients preserve the same initialized owner representation properties. -/
theorem program [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp TypedSpec Value) (before : State source Platform) (result : Value × State source Platform)
    (prior : Valid selectedOwner publicPrekey before.1.beacons)
    (present : result ∈ support ((simulateQ (RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept
      publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before)) :
    Valid selectedOwner publicPrekey result.2.1.beacons := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
    cases present
    exact prior
  | query_bind query next ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at present
    obtain ⟨middle, called, continued⟩ := present
    exact ih middle.1 middle.2 result
      (handler setup checks wire sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer query before middle prior called) continued

/-- The actual full raw compiler retains both owner properties in every mode and every free result. -/
theorem run [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source Platform)
    (result : (Value × RegistrationNativeLedger.State) × State source Platform)
    (prior : Valid selectedOwner publicPrekey before.1.beacons)
    (present : result ∈ support (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept
      publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)) :
    Valid selectedOwner publicPrekey result.2.1.beacons :=
  program setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign selectedOwner selectedAccept publicPrekey view failure
    allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    before result prior present

/-- Empty owner startup derives the internal premises for the same complete adaptive raw run. -/
theorem run_empty [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source Platform)
    (result : (Value × RegistrationNativeLedger.State) × State source Platform)
    (empty : before.1.beacons = [])
    (present : result ∈ support (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept
      publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)) :
    Valid selectedOwner publicPrekey result.2.1.beacons := by
  have prior : Valid selectedOwner publicPrekey before.1.beacons := by
    rw [empty]
    exact RegistrationNativePlatformPublicOwnerState.empty selectedOwner publicPrekey
  exact program setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign selectedOwner selectedAccept publicPrekey view failure
    allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    before result prior present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.run_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerInvariant.run_empty
