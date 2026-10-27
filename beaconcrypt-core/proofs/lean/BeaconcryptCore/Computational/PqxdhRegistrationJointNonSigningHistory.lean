-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript

/-! The actual non-signing registration callbacks preserve every identity's successful signing-message history. Auxiliary protocol state and converted-DH/reveal observations remain in the complete source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointSigningTranscript
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Equality of this exact transcript projection is preserved through the complete adaptive stateful program. -/
theorem program {κ : Type} {spec : OracleSpec κ} {State : Type}
    (impl : QueryImpl spec (StateT State ProbComp)) (view : State → List PqxdhDynamicIdentityPool.Observation)
    (index : Nat)
    (steps : ∀ query before after, after ∈ support ((impl query).run before) →
      messagesAt index (view after.2) = messagesAt index (view before))
    (work : OracleComp spec Result) (before : State) (after : Result × State)
    (supported : after ∈ support ((simulateQ impl work).run before)) :
    messagesAt index (view after.2) = messagesAt index (view before) :=
  run_rel impl (fun before after => messagesAt index (view after) = messagesAt index (view before))
    (fun _ => rfl) (fun _ _ _ first second => second.trans first) steps work before after supported

/-- Beacon preparation adds only its actual DH or KEM observations, never a signing message. -/
theorem preparation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex target : Nat)
    (query : (PqxdhRegistrationJointPreparation.NativeSpec KemSK Response).Domain)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (result : (PqxdhRegistrationJointPreparation.NativeSpec KemSK Response).Range query × PqxdhRegistrationJointPreparation.Pool KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointPreparation.annotated setup codec identityIndex kemIndex query).run pool)) :
    messagesAt target result.2.1.transcript = messagesAt target pool.1.transcript := by
  cases query <;> simp only [PqxdhRegistrationJointPreparation.annotated, StateT.run,
    support_map, Set.mem_image, mem_support_pure_iff] at supported
  all_goals obtain ⟨reply, _, rfl⟩ := supported
  all_goals simp [PqxdhDynamicIdentityPool.record, messagesAt, messageAt]

/-- Every literal native finish callback preserves the signing projection while retaining its complete private/native poststate. -/
theorem finish_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex target : Nat)
    (query : (PqxdhRegistrationJointFinish.NativeSpec KemSK Response).Domain)
    (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (PqxdhRegistrationJointFinish.NativeSpec KemSK Response).Range query × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex query).run state)) :
    messagesAt target result.2.1.1.transcript = messagesAt target state.1.1.transcript := by
  cases query <;> simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onPool,
    PqxdhRegistrationJointFinish.onNative, StateT.run, support_map, Set.mem_image] at supported
  all_goals obtain ⟨answer, member, rfl⟩ := supported
  case inl query => exact preparation setup codec identityIndex kemIndex target query state.1 answer member
  case inr => rfl

/-- The entire actual Beacon finish preserves all earlier signatures, even after failed preparation or opening. -/
theorem finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex target : Nat) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run state)) :
    messagesAt target result.2.1.1.transcript = messagesAt target state.1.1.transcript :=
  program (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex)
    (fun state => state.1.1.transcript) target (finish_query setup codec identityIndex kemIndex target)
    (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner) state result supported

/-- Literal Server prefix verification and converted-DH callbacks cannot append a signature to any owner's history. -/
theorem server_prefix (joint : Primitives) (seed : IdentitySeed) (identityIndex target : Nat)
    (aux : QueryImpl (PqxdhRegistrationJointServerPrefix.AuxSpec Reader) (StateT A ProbComp))
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (result : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Range query × PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : result ∈ support ((PqxdhRegistrationJointServerPrefix.annotated joint seed identityIndex aux query).run state)) :
    messagesAt target result.2.1.1.transcript = messagesAt target state.1.1.transcript := by
  cases query <;> simp only [PqxdhRegistrationJointServerPrefix.annotated,
    PqxdhServerStaticDhSource.nativeImpl, PqxdhRegistrationJointServerPrefix.onAux,
    StateT.run, support_map, Set.mem_image] at supported
  all_goals obtain ⟨answer, _, rfl⟩ := supported
  all_goals simp [PqxdhDynamicIdentityPool.record, messagesAt, messageAt]

/-- The complete actual raw Server preparation retains every owner's earlier signing messages. -/
theorem server_prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex target : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : (Option (PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerAccept.sourcePrepare setup codec checks seed identityIndex raw).run state)) :
    messagesAt target result.2.1.1.transcript = messagesAt target state.1.1.transcript := by
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨answer, reached, rfl⟩ := supported
  exact program (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex (serverAux setup codec checks))
    (fun state => state.1.1.transcript) target
    (server_prefix setup.joint seed identityIndex target (serverAux setup codec checks))
    (PqxdhServerRootPreparation.collect raw) (state.1, state.2.2.server.consumed) answer reached

/-- Full raw acceptance performs no signing; root generation, consumed IDs, pending publication and every failed branch remain in its native continuation. -/
theorem server_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex target : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointFinish.State KemSK)
    (result : Option Nat × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw).run state)) :
    messagesAt target result.2.1.1.transcript = messagesAt target state.1.1.transcript := by
  simp only [PqxdhRegistrationJointServerAccept.source, PqxdhRegistrationJointServerAccept.run, StateT.run_bind] at supported
  simp only [PqxdhRegistrationJointFinish.onNative, nativeGet, localState, StateT.run, map_pure, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, reached, final⟩ := supported
  simp only [support_map, Set.mem_image] at final
  obtain ⟨nativeResult, _, rfl⟩ := final
  exact server_prepare setup codec checks seed identityIndex target raw state prepared reached

/-- Current live-field reads record disclosure but never issue a signature. -/
theorem entry_read (field : PqxdhRegistrationJointLiveRead.Field)
    (entry : PqxdhRegistrationJointOwnership.Entry KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (target : Nat) :
    messagesAt target (PqxdhRegistrationJointLiveRead.entrySource field entry pool).2.1.transcript =
      messagesAt target pool.1.transcript := by
  cases field <;> cases phase : entry.owner.beacon.phase <;>
    simp [PqxdhRegistrationJointLiveRead.entrySource, PqxdhRegistrationJointOwnership.activeKey, phase,
      PqxdhDynamicIdentityPool.record, messagesAt, messageAt]

/-- A complete current-field read preserves every signing-message projection at present and missing addresses. -/
theorem live_read (request : Nat × PqxdhRegistrationJointLiveRead.Field)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (target : Nat) :
    messagesAt target (PqxdhRegistrationJointLiveRead.sourceStep request state).2.pool.1.transcript =
      messagesAt target state.pool.1.transcript := by
  cases found : state.owners[request.1]? <;>
    simp only [PqxdhRegistrationJointLiveRead.sourceStep, found]
  case some entry => exact entry_read request.2 entry state.pool target

end BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.preparation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.finish_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.finish_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.server_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.server_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.server_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.server_prepare

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.server_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.server_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.entry_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.entry_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.live_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNonSigningHistory.live_read
