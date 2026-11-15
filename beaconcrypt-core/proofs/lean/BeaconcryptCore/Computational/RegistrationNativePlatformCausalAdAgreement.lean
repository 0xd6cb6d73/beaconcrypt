-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCausalRecordStage
import BeaconcryptCore.Computational.RegistrationNativePlatformMatchedServerInput
import BeaconcryptCore.Computational.RegistrationNativePlatformAdAgreement

/-! The initialized source journal supplies the earlier Server AD callback, original attached Init fields and matched accepted request. Every actual successful authentication of that issued response then has the same session transcript digest and complete AD151 before invoking an opener. The only cryptographic exception used here is the existing common-cache collision event; actual root correctness and a completed peer are not premises. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCausalAdAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

/-- The same reached earlier Server stage supplies AD agreement at every actual response authentication cut. All inputs below are concrete chronological/source receipts already returned by the coupled stage theorem. -/
theorem from_stage (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (reached : Path (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created credential
      view failure allocation reserveRegistration reservePeer erased helper writer) (initial.state, previous) calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls)
    (found : beforeFinish.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final.1))
    (leading trailing : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (serverCall : Call RegistrationNativeRawAdapter.TypedSpec Whole)
    (receipt : RegistrationSigningShared.Receipt) (serverIndex : Nat)
    (serverInput : Option (Slice U8))
    (stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup wire view failure allocation erased helper
      serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt)
    (prefixRun : Path (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created credential
      view failure allocation reserveRegistration reservePeer erased helper writer) (initial.state, previous) leading beforeFinish)
    (suffixRun : Path (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created credential
      view failure allocation reserveRegistration reservePeer erased helper writer) afterFinish trailing final)
    (earlier : serverCall ∈ leading)
    (identity : stage.hashed.candidate.server_identity_public_key = packet.public.identity_key)
    (ephemeral : stage.hashed.candidate.ephemeral_public_key = packet.public.ephemeral_key)
    (kem : stage.hashed.candidate.kem_ciphertext = packet.public.kem_cipher_text)
    (assigned : stage.hashed.candidate.key_id = packet.public.key_id)
    (initHash : stage.hashed.binding.init_hash = pending.binding.init_hash) :
    ∀ (authBefore authAfter : Local n KemSK source) (authenticated : registration.AuthenticatedResponse),
        (.ok (.Ok authenticated), authAfter) ∈ support
          ((lower setup checks representation initial.created
            (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
              (RegistrationResponseExecutor.begin pending (.Some packet)))).run authBefore) →
        (project authAfter).2 ≤ RegistrationNativeWorldCache.cache final.1 →
        stage.initial.binding.session_transcript_hash = authenticated.binding.session_transcript_hash ∧
          stage.initial.binding.associated_data = authenticated.binding.associated_data := by
  let finishCall : Call RegistrationNativeRawAdapter.TypedSpec Whole :=
    ⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩
  obtain ⟨_leading, _trailing, _split, _prefix, finished, _suffix⟩ := reached.member finishCall member
  have beforeExtension := RegistrationNativePlatformPathState.cache coins setup checks wire route representation initial.created credential view failure allocation
    reserveRegistration reservePeer erased helper writer (.cons finishCall finished _ _ suffixRun)
  have earlierCollisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache beforeFinish.1) := by
    intro collision
    obtain ⟨one, two, left, right, distinct, firstAt, secondAt, equal⟩ := collision
    exact collisionFree ⟨one, two, left, right, distinct, beforeExtension firstAt, beforeExtension secondAt, equal⟩
  obtain ⟨matched⟩ := RegistrationNativePlatformMatchedServerInput.from_taken coins setup checks wire route representation initial.created credential view failure allocation
    reserveRegistration reservePeer erased helper writer ensureInit identityIndex serverKeyId initial startup
    previous beforeFinish leading prefixRun index owner pending oneTime found phase serverCall earlier serverIndex stage.token stage.current stage.taken
    stage.pin stage.plaintext stage.availability stage.initial stage.hashed stage.admitted stage.path initHash earlierCollisionFree
  let matchedFinal : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation initial.created owner oneTime stage.token
      beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1) :=
    { matched with cacheExtension := matched.cacheExtension.trans beforeExtension }
  obtain ⟨pendingCall, _pendingMember, origin, _leading, pendingTrailing, earlierOwner, _split, _before, _called, afterPending,
      earlierFound, earlierPhase, metadata⟩ :=
    RegistrationNativePlatformInitPendingJournal.initialized_path coins setup checks wire route representation initial.created credential view failure allocation
      reserveRegistration reservePeer erased helper writer ensureInit identityIndex serverKeyId initial startup previous beforeFinish leading prefixRun
      index owner pending oneTime found phase
  obtain ⟨earlierPending⟩ := RegistrationNativePlatformInitPendingJournal.source_receipt coins setup checks representation initial.created writer
    pendingCall index pending oneTime origin earlierOwner earlierFound earlierPhase
  obtain ⟨original⟩ := RegistrationNativePlatformPendingTuple.transport setup earlierOwner owner pending oneTime _ _ metadata
    ((RegistrationNativePlatformPathState.cache coins setup checks wire route representation initial.created credential view failure allocation
      reserveRegistration reservePeer erased helper writer afterPending).trans beforeExtension) earlierPending
  obtain ⟨adDigest, binding, completedAt, initialBinding, _application, _root⟩ :=
    (RegistrationNativeServerBindingReceipt.initial_root stage.current.control stage.pin stage.availability stage.token.agreement
      stage.plaintext stage.initial stage.admitted).2
  obtain ⟨expectedBinding, expectedAt, _pin, hashRetained, _identity, _digest, _consistent⟩ :=
    SessionBinding.complete_refines stage.token.agreement.binding adDigest
  have completedSame : expectedBinding = binding := RustM.ok.inj (expectedAt.symm.trans completedAt)
  have retained := (RegistrationNativeServerContents.path_contents stage.initial stage.hashed stage.path).1
  have tokenHash : stage.token.agreement.binding.init_hash = pending.binding.init_hash :=
    (hashRetained ▸ congrArg (fun value : session.CompletedRegistrationBinding => value.init_hash)
      ((retained.trans initialBinding).trans completedSame.symm)).symm.trans initHash
  obtain ⟨_buildLeading, _buildTrailing, _buildSplit, _beforeBuild, _built, afterBuild⟩ := prefixRun.member serverCall earlier
  have serverExtension := (RegistrationNativePlatformPathState.cache coins setup checks wire route representation initial.created credential view failure allocation
    reserveRegistration reservePeer erased helper writer afterBuild).trans beforeExtension
  have responseFields : RegistrationAd.serverView stage.hashed.candidate = RegistrationAd.responseView packet.public := by
    simp only [RegistrationAd.serverView, RegistrationAd.responseView, identity, ephemeral, kem, assigned]
  intro authBefore authAfter authenticated authenticatedAt authExtension
  exact RegistrationNativePlatformAdAgreement.from_cuts coins setup checks wire route representation initial.created
    view failure allocation erased helper serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt stage
    owner pending oneTime packet beforeFinish.1.server.pin (RegistrationNativeWorldCache.cache final.1) matchedFinal original tokenHash
    responseFields serverExtension authBefore authAfter authenticated authenticatedAt authExtension collisionFree

/-- One initialized chronological execution supplies its earlier partner and AD agreement for every actual successful authentication cut of the issued response, independently of record opening. -/
theorem path (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)) (final : Whole)
    (reached : Path (RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation initial.created credential
      view failure allocation reserveRegistration reservePeer erased helper writer) (initial.state, previous) calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Whole) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls)
    (found : beforeFinish.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish.1))))
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache final.1)) :
    ∃ serverCall ∈ calls, ∃ receipt serverIndex serverInput,
      ∃ stage : RegistrationNativePlatformResponseRecordStage.Stage coins setup wire view failure allocation erased helper
        serverIndex serverInput serverCall.before.1.server serverCall.after.1.server receipt,
      serverCall.query = .inr (.build serverIndex serverInput) ∧
      ∀ (authBefore authAfter : Local n KemSK source) (authenticated : registration.AuthenticatedResponse),
        (.ok (.Ok authenticated), authAfter) ∈ support
          ((lower setup checks representation initial.created
            (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
              (RegistrationResponseExecutor.begin pending (.Some packet)))).run authBefore) →
        (project authAfter).2 ≤ RegistrationNativeWorldCache.cache final.1 →
        stage.initial.binding.session_transcript_hash = authenticated.binding.session_transcript_hash ∧
          stage.initial.binding.associated_data = authenticated.binding.associated_data := by
  obtain ⟨leading, trailing, serverCall, receipt, serverIndex, serverInput, stage, split, prefixRun, suffixRun,
      earlier, queryEq, _payload, identity, ephemeral, kem, _ciphertext, assigned, initHash⟩ :=
    RegistrationNativePlatformCausalRecordStage.path setup checks wire route representation initial.created credential view failure allocation
      reserveRegistration reservePeer erased helper writer ensureInit identityIndex serverKeyId initial startup
      previous calls final reached index pending packet beforeFinish afterFinish application member issued
  refine ⟨serverCall, ?_, receipt, serverIndex, serverInput, stage, queryEq, ?_⟩
  · rw [split]
    exact List.mem_append_left _ earlier
  · exact from_stage setup checks wire route representation credential view failure allocation reserveRegistration reservePeer erased helper writer
      ensureInit identityIndex serverKeyId initial startup previous calls final reached index pending packet owner oneTime
      beforeFinish afterFinish application member found phase collisionFree leading trailing serverCall receipt serverIndex serverInput stage
      prefixRun suffixRun earlier identity ephemeral kem assigned initHash

end BeaconcryptCore.Computational.RegistrationNativePlatformCausalAdAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCausalAdAgreement.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCausalAdAgreement.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCausalAdAgreement.from_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCausalAdAgreement.from_stage
