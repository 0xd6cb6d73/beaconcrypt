-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterialSessionFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution
/-! Public callback token frames follow the actual corrected frontend code and its exact free build program. The proof includes effectful writers and public allocation histories, before private source interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicFrontend (State Base LocalM M)
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Beacon callbacks preserve every Server capability while retaining their real effectful platform poststate. -/
theorem beacon (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (Base n KemSK Platform) Value) (before : State source Platform) (result : Value × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.beacon work).run before)) :
    result.2.1.server.sessions = before.1.server.sessions := by
  change result ∈ support ((fun result => (result.1.1.1,
    ({ before.1 with beacons := result.1.1.2, environment := result.1.2 }, result.2))) <$>
      (((work.run before.1.beacons).run before.1.environment).run before.2)) at supported
  rw [support_map] at supported
  obtain ⟨result, _reached, rfl⟩ := supported
  rfl

/-- Embedding an actual local callback into the full query language preserves its token-subset property. -/
theorem execute_local (work : LocalM n KemSK Platform source Value)
    (subset : ∀ before result, result ∈ support (work.run before) → ∀ ready,
      some ready ∈ result.2.1.server.sessions → some ready ∈ before.1.server.sessions)
    (before : State source Platform) (result : Value × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.executeLocal work).run before))
    (ready : RegistrationServerReferenceRoot.Ready) (member : some ready ∈ result.2.1.server.sessions) :
    some ready ∈ before.1.server.sessions := by
  exact subset before result (RegistrationNativePublicSourceSupport.simulate_support
    RegistrationNativePlatformPublicFrontend.embedLocal (work.run before) result supported) ready member

/-- The actual compiled corrected Server build keeps only earlier session tokens under all primitive and external writer replies. -/
theorem build [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (index : Nat) (application : Option (Slice U8))
    (before : State source Platform) (result : RustM (Option (U64 × Pqxdh.Bytes)) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.build (n := n) setup sign view failure allocation erased
      helper writer reserve index application source).run before))
    (ready : RegistrationServerReferenceRoot.Ready) (member : some ready ∈ result.2.1.server.sessions) :
    some ready ∈ before.1.server.sessions := by
  change result ∈ support ((fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    ({ before.1 with server := result.1.2, environment := { before.1.environment with receipts := result.2.1, recordRequests := [] } }, result.2.2))) <$>
    simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (n := n))
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program index application).run before.1.server)).run
          (before.1.environment.receipts, before.2))) at supported
  rw [support_map] at supported
  obtain ⟨⟨⟨reply, current⟩, after⟩, reached, rfl⟩ := supported
  have lowered := RegistrationNativePublicSourceSupport.simulate_support (RegistrationNativePlatformPublicFrontend.buildEmbedding (n := n))
    _ ((reply, current), after) reached
  have possible : (reply, current) ∈ support ((RegistrationNativePlatformServerFrontendProgram.program index application).run before.1.server) := by
    apply support_simulateQ_run'_subset
      (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
      ((RegistrationNativePlatformServerFrontendProgram.program index application).run before.1.server)
      (before.1.environment.receipts, before.2)
    rw [StateT.run'_eq, support_map]
    exact ⟨((reply, current), after), lowered, rfl⟩
  exact RegistrationNativePlatformMaterialSessionFrame.program_subset index application before.1.server current reply possible ready member


/-- All four dynamic ordinary-record routes preserve Server capabilities, including failed terminal allocation after an advanced send. -/
theorem record (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.record (n := n) (KemSK := KemSK) reserve query).run before)) :
    result.2.1.server.sessions = before.1.server.sessions := by
  cases query with
  | inl query => cases query with
    | inl send =>
        simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, mem_support_bind_iff,
          mem_support_pure_iff] at supported
        obtain ⟨first, _called, last, _reserved, rfl⟩ := supported
        rfl
    | inr raw =>
        simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, support_map] at supported
        obtain ⟨reply, _called, rfl⟩ := supported
        rfl
  | inr query =>
      rcases query with ⟨index, query⟩
      cases found : before.1.beacons[index]? with
      | none =>
          cases query <;> simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found,
            mem_support_pure_iff] at supported <;> cases supported <;> rfl
      | some owner => cases query with
        | inl plaintext =>
            simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found,
              mem_support_bind_iff, mem_support_pure_iff] at supported
            obtain ⟨first, _called, last, _reserved, rfl⟩ := supported
            rfl
        | inr raw =>
            simp only [RegistrationNativePlatformPublicFrontend.record, StateT.run, found, support_map] at supported
            obtain ⟨reply, _called, rfl⟩ := supported
            rfl


private theorem lift_sessions (work : OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK) Value)
    (before : State source Platform) (result : Value × State source Platform)
    (supported : result ∈ support (((StateT.lift work : LocalM n KemSK Platform source Value)).run before)) :
    result.2.1.server.sessions = before.1.server.sessions := by
  rw [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨value, _reached, rfl⟩ := supported
  rfl

private theorem map_beacon {A B : Type} (observe : A → B)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State (Base n KemSK Platform) A)
    (before : State source Platform) (result : B × State source Platform)
    (supported : result ∈ support ((observe <$> RegistrationNativePlatformPublicFrontend.beacon work).run before)) :
    result.2.1.server.sessions = before.1.server.sessions := by
  rw [StateT.run_map, support_map] at supported
  obtain ⟨value, reached, rfl⟩ := supported
  exact beacon work before value reached

def NonAccept : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.accept _) => False
  | _ => True

/-- Every actual corrected callback other than accept can only remove previously owned Server capabilities. -/
theorem handler_nonaccept [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : NonAccept query)
    (before : State source Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before))
    (ready : RegistrationServerReferenceRoot.Ready) (member : some ready ∈ result.2.1.server.sessions) :
    some ready ∈ before.1.server.sessions := by
  cases query with
  | inl coin =>
      apply execute_local _ ?_ before result supported ready member
      intro current output reached retained stored
      rw [lift_sessions _ current output reached] at stored
      exact stored
  | inr command => cases command with
    | create edPin mlPin keyId =>
        apply execute_local _ ?_ before result supported ready member
        intro current output reached retained stored
        rw [beacon _ current output reached] at stored
        exact stored
    | bundle index =>
        apply execute_local _ ?_ before result supported ready member
        intro current output reached retained stored
        rw [map_beacon _ _ current output reached] at stored
        exact stored
    | accept packet => exact ordinary.elim
    | build index application =>
        apply execute_local _ ?_ before result supported ready member
        intro current output reached retained stored
        exact build setup sign view failure allocation erased helper writer reservePeer index application current output reached retained stored
    | finish index packet =>
        apply execute_local _ ?_ before result supported ready member
        intro current output reached retained stored
        rw [beacon _ current output reached] at stored
        exact stored
    | hmac key bytes =>
        change result ∈ support (pure (setup.hmac.eval key bytes, before)) at supported
        rw [mem_support_pure_iff] at supported
        cases supported
        exact member
    | hash bytes =>
        apply execute_local _ ?_ before result supported ready member
        intro current output reached retained stored
        rw [lift_sessions _ current output reached] at stored
        exact stored
    | serverSend keyId plaintext =>
        rw [record (n := n) (KemSK := KemSK) reserveFrame (.inl (.inl (plaintext, keyId))) before result supported] at member
        exact member
    | serverRaw raw =>
        rw [record (n := n) (KemSK := KemSK) reserveFrame (.inl (.inr raw)) before result supported] at member
        exact member
    | beaconSend index plaintext =>
        rw [record (n := n) (KemSK := KemSK) reserveFrame (.inr (index, .inl plaintext)) before result supported] at member
        exact member
    | beaconRaw index raw =>
        rw [record (n := n) (KemSK := KemSK) reserveFrame (.inr (index, .inr raw)) before result supported] at member
        exact member

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.execute_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.execute_local

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.handler_nonaccept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSessionFrame.handler_nonaccept
