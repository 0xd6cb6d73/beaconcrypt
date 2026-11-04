-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerHistoryOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseAccepted
import BeaconcryptCore.Computational.RegistrationNativeCausalResponseContents

/-! Prior unsigned Server response issuance at a successful corrected source finish yields the same actual earlier source build and exact public response fields in one chronological execution. The selected source token, initializer admission, first-record hash path and extra platform states remain present; completed Server installation is not inferred. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCausalResponseContents
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
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
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

/-- Actual corrected source completion with prior unsigned issuance has its own earlier source build and exact response contents on the same path. -/
theorem path_contents (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (reached : Path impl (initial.state, previous) calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls)
    (found : beforeFinish.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish.1)))) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash afterFinish.1.server.world.world.1.primitive.2) source.verify
      (RegistrationResponseExecutor.trial true pending packet (RegistrationSigningShared.historyFor
        (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish.1))) ∧
      ∃ leading trailing serverCall receipt serverIndex serverInput token current pin plaintext availability serverInitial hashed,
        calls = leading ++ (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) :: trailing ∧
        Path impl (initial.state, previous) leading beforeFinish ∧
        Executed impl (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∧
        Path impl afterFinish trailing final ∧ serverCall ∈ leading ∧ serverCall.query = .inr (.build serverIndex serverInput) ∧
        RegistrationServerSdkSource.take serverIndex serverCall.before.1.server = (some token, current) ∧ serverInput = some plaintext ∧
        SourceAt serverCall receipt ∧ registration.begin_server_completion current.control pin availability token.agreement plaintext = .ok (.Ok serverInitial) ∧
        RegistrationServerRecordExecutor.Path serverInitial hashed ∧ hashed.candidate.server_identity_public_key = packet.public.identity_key ∧
        hashed.candidate.ephemeral_public_key = packet.public.ephemeral_key ∧ hashed.candidate.kem_ciphertext = packet.public.kem_cipher_text ∧
        hashed.ciphertext = packet.application ∧ hashed.candidate.key_id = packet.public.key_id ∧ hashed.binding.init_hash = pending.binding.init_hash ∧
        pqxdh.concrete.start_server_candidate_ratchet_kdf serverInitial.candidate token.agreement.root.bytes = .ok serverInitial.pending := by
  obtain ⟨leading, trailing, split, prefixRun, finished, suffixRun⟩ := reached.member
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) member
  have finishedRaw := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    (.inr (.finish index (some packet))) beforeFinish afterFinish (.ok (some application)) finished
  have verified := RegistrationNativePlatformResponseAccepted.typed coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer index owner pending oneTime packet beforeFinish.1 afterFinish.1 beforeFinish.2 afterFinish.2 application
      found phase finishedRaw
  obtain ⟨receipt, present, content, _key⟩ := issued_member beforeFinish.1 pending packet issued
  rcases RegistrationNativePlatformServerHistoryOrigin.path_origin setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer prefixRun receipt present with old | ⟨serverCall, earlier, origin⟩
  · have empty := RegistrationNativeServerHistoryOrigin.start_empty setup ensureInit identityIndex serverKeyId initial startup
    rw [empty] at old
    cases old
  · have stageReceipt := origin
    obtain ⟨serverIndex, serverInput, token, current, pin, plaintext, availability, serverInitial, hashed, query, taken, plaintextEq,
      admitted, path, _publicKey, payload, _newMember, _absentBefore⟩ := origin
    have samePayload : Command.payload (.server hashed) = RegistrationResponseExecutor.payload pending packet := payload.symm.trans content
    obtain ⟨identity, ephemeral, kem, ciphertext, assigned, initHash⟩ :=
      RegistrationNativeResponseStageContents.native_fields serverInitial hashed path pending packet samePayload
    have rooted := (RegistrationNativeServerBindingReceipt.initial_root current.control pin availability token.agreement plaintext serverInitial admitted).2.2.2
    exact ⟨verified, leading, trailing, serverCall, receipt, serverIndex, serverInput, token, current, pin, plaintext, availability, serverInitial, hashed,
      split, prefixRun, finished, suffixRun, earlier, query, taken, plaintextEq, stageReceipt, admitted, path, identity, ephemeral, kem, ciphertext, assigned, initHash, rooted⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformCausalResponseContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCausalResponseContents.path_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCausalResponseContents.path_contents
