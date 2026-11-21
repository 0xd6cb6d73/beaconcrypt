-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordStage
import BeaconcryptCore.Computational.RegistrationNativePlatformServerHistoryOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseAccepted
import BeaconcryptCore.Computational.RegistrationNativeCausalResponseContents

/-! Actual corrected response issuance selects a single earlier source first-record witness with that same signing receipt. All public response fields and the retained unsigned Init digest are derived from this coupled witness, before any root/initializer/application agreement composition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCausalRecordStage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaRoleFrame (NonBuild serverReceipts)
open RegistrationNativeServerIssuance (history)
open RegistrationSigningShared (Receipt)
open RegistrationSigningTrace (Command)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformServerHistoryOrigin (SourceAt)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

private theorem issued_member (before : Native) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before)))) :
    ∃ receipt ∈ serverReceipts (history before.server),
      receipt.observation.payload = RegistrationResponseExecutor.payload pending packet ∧
      absBytes receipt.observation.publicKey = absBytes pending.binding.server_pin.public_key := by
  obtain ⟨signed, member, samePayload⟩ := issued
  have historyMember : signed ∈ BeaconcryptCore.Refinement.RegistrationSigningTrace.historyFor
      (absBytes pending.binding.server_pin.public_key) ((history before.server).map Receipt.observation) := member
  obtain ⟨observation, observed, key, sameCall⟩ :=
    (BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff _ _ _).mp historyMember
  obtain ⟨receipt, recorded, sameObservation⟩ := List.mem_map.mp observed
  subst observation
  have content : receipt.observation.payload = RegistrationResponseExecutor.payload pending packet :=
    (congrArg MldsaTranscriptAuth.SigningCall.payload sameCall).trans samePayload
  refine ⟨receipt, List.mem_filter.mpr ⟨recorded, ?_⟩, content, key⟩
  simp only [content, RegistrationResponseExecutor.payload, MldsaTranscriptAuth.responsePayload, decide_true]

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformInitPendingJournal.callback, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

/-- Prior unsigned response issuance locates one exact earlier coupled source record/hash/sign witness in the same actual path. -/
theorem path (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (reached : Path impl (initial.state, previous) calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish.1)))) :
    ∃ leading trailing serverCall receipt serverIndex serverInput,
      ∃ stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup wire view failure allocation erased helper serverIndex serverInput
        serverCall.before.1.server serverCall.after.1.server receipt,
      calls = leading ++ (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) :: trailing ∧
      Path impl (initial.state, previous) leading beforeFinish ∧ Path impl afterFinish trailing final ∧ serverCall ∈ leading ∧
      serverCall.query = .inr (.build serverIndex serverInput) ∧ receipt.observation.payload = RegistrationResponseExecutor.payload pending packet ∧
      stage.hashed.candidate.server_identity_public_key = packet.public.identity_key ∧
      stage.hashed.candidate.ephemeral_public_key = packet.public.ephemeral_key ∧ stage.hashed.candidate.kem_ciphertext = packet.public.kem_cipher_text ∧
      stage.hashed.ciphertext = packet.application ∧ stage.hashed.candidate.key_id = packet.public.key_id ∧ stage.hashed.binding.init_hash = pending.binding.init_hash := by
  obtain ⟨leading, trailing, split, prefixRun, _finished, suffixRun⟩ := reached.member
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) member
  obtain ⟨receipt, present, content, _key⟩ := issued_member beforeFinish.1 pending packet issued
  rcases RegistrationNativePlatformServerHistoryOrigin.path_origin setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer prefixRun receipt present with old | ⟨serverCall, earlier, origin⟩
  · have empty := RegistrationNativeServerHistoryOrigin.start_empty setup ensureInit identityIndex serverKeyId initial startup
    rw [empty] at old
    cases old
  · have sourceOrigin := origin
    obtain ⟨serverIndex, serverInput, _token, _current, _pin, _plaintext, _availability, _serverInitial, _hashed, queryEq, _taken, _plaintextEq,
      _admitted, _path, _publicKey, _payload, newMember, absentBefore⟩ := origin
    obtain ⟨_before, _after, _split, _prefix, called, _suffix⟩ := prefixRun.member serverCall earlier
    rcases serverCall with ⟨query, before, reply, after⟩
    change query = .inr (.build serverIndex serverInput) at queryEq
    subst query
    have sourceCalled := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      (.inr (.build serverIndex serverInput)) before after reply called
    obtain ⟨stage⟩ := RegistrationNativePlatformResponseRecordStage.typed coins setup checks wire route representation created credential view failure allocation erased
      reserveRegistration reservePeer helper writer serverIndex serverInput before.1 after.1 before.2 after.2 reply sourceCalled receipt newMember absentBefore
    have selectedPayload : receipt.observation.payload = Command.payload (.server stage.hashed) :=
      congrArg (fun value : Receipt => value.observation.payload) stage.selected
    have samePayload := selectedPayload.symm.trans content
    obtain ⟨identity, ephemeral, kem, ciphertext, assigned, initHash⟩ :=
      RegistrationNativeResponseStageContents.native_fields stage.initial stage.hashed stage.path pending packet samePayload
    exact ⟨leading, trailing, ⟨.inr (.build serverIndex serverInput), before, reply, after⟩, receipt, serverIndex, serverInput, stage,
      split, prefixRun, suffixRun, earlier, rfl, content, identity, ephemeral, kem, ciphertext, assigned, initHash⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformCausalRecordStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCausalRecordStage.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCausalRecordStage.path
