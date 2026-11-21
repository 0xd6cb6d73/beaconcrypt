-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodBuild

/-!
# CE-3's invariant across owner k's challenge finish (CE-11b, unit U6, fourth part)

The CE side of the invariant of the middle execution (`PqxdhDeploymentIdealPostReduce.MiddleInv`) must survive owner k's challenge finish: after an active selected accept, the finish of the selected owner while it is `initSent`, which the middle source handler answers by the ideal registration's challenge finish (`PqxdhDeploymentIdealSteps.finishChallenge`: the grouped native owner under `ownerImplCE` with the factored hidden services and the challenge handle). CE-3's preservation of its invariant `PqxdhDeploymentCompileInvariant.Good` by a finish (`good_finish`) reads the footprint of the real finish (`PqxdhDeploymentCompileFootprint.finish_owner`). This module proves the same footprint for the CE-native challenge finish and the preservation for owner k's challenge finish of the middle execution.

- The challenge-handle preparation (`PqxdhDeploymentIdealSteps.preparationCE`): `collectCE_inputs` (the collected inputs carry the response read from the finish bytes by the codec Phase 2 reader and the assigned key ID read from it) and `prepareCE_facts` (a successful preparation's metadata is the control's expected Server binding, that assigned key ID and the control's associated data).
- The grouped finish (`PqxdhDeploymentIdealSteps.groupCE`): `staged_opening` (a staged registration from a successful opening carries the opened candidate and its associated data), `afterRoot_opening` and `hiddenAfter_opening` (every staged outcome of the native continuation after a root and of the factored hidden continuation at any value is an opening of the metadata-cleared candidate), and `groupCE_footprint` (the grouped finish changes only the CTX cache of the game state, and every staged outcome carries the metadata-cleared candidate and its associated data).
- `finish_shape` (the source commit `PqxdhBeaconPhase2Publication.finish` on such a staged outcome aborts or establishes with the expected binding, the assigned key ID and the associated data) and `groupedOwnerCE_footprint`: owner k's grouped native finish through the first-touch allocator has the footprint of CE-3's `finish_owner`, with only the CTX cache of the game state changed.
- The hashed finish (`PqxdhDeploymentIdealSteps.hashedOwnerCE`, design §4.3/§4.5): `nativePrim_ctx`, `primLabels_ctx`, `rawReceive_ctx`, `hiddenAfter_ctx`, `groupCE_ctx` and `groupedOwnerCE_ctx` (the grouped finish only extends the BLAKE2b cache), and `hashedOwnerCE_footprint` (owner k's hashed grouped finish has the footprint of CE-3's `ownerFinish_owner`: only the CTX cache changes and only grows; a success leaves the transcript of the retained bundle and the decoded response cached at a digest whose `PqxdhTranscriptAd.adOf` is the established associated data).
- `good_of_finish`: CE-3's invariant survives every finish of a present owner with that footprint that keeps the Server fields of the game state and only extends its BLAKE2b cache, with the reply logged (the argument of `good_finish`, from the footprint alone).
- `compiledMid_challenge` and `good_challenge`: the compiled challenge finish of the middle execution logs the reply, keeps the accept counter, keeps the Server fields of the game state and replaces the addressed owner as the footprint describes; hence it keeps CE-3's invariant on the local copies and the native state of the annotated source state.

These are support facts and invariant preservation. They use no codec contract, charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhKemIndCca (MlKem768Ciphertext MlKem768PublicKey)
open PqxdhPhase2DecapsulationRouting (Shared)

/-! ### The challenge-handle preparation -/

section Prepare
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response)
open PqxdhDeploymentIdealSteps (preparationCE)

/-- The inputs collected under the challenge-handle preparation carry the response read from the finish bytes by the codec Phase 2 reader and the assigned key ID read from that response (CE-3's `PqxdhDeploymentCompileFootprint.collect_inputs` for `preparationCE`). -/
theorem collectCE_inputs (challenge : MlKem768Ciphertext) (identity : IdentitySeed) (prekey oneTime : ScalarBytes)
    (kem : MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes) (inputs : PqxdhBeaconPhase2Shared.Inputs Response Shared)
    (supported : some inputs ∈ support (simulateQ (preparationCE setup codec challenge)
      (PqxdhBeaconPhase2Shared.collect identity prekey oneTime kem raw))) :
    codec.read2 raw = some inputs.response ∧ inputs.assigned = codec.assignedId inputs.response := by
  simp only [PqxdhBeaconPhase2Shared.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query] at supported
  rw [show preparationCE setup codec challenge (.decode raw) = pure (codec.read2 raw) from rfl, pure_bind] at supported
  cases decoded : codec.read2 raw with
  | none => simp [decoded] at supported
  | some response =>
      simp only [decoded, Option.elim_some] at supported
      iterate 10
        rw [simulateQ_bind, mem_support_bind_iff] at supported
        obtain ⟨reply, -, supported⟩ := supported
        rcases reply with _ | reply
        · simp at supported
        simp only [Option.elim_some] at supported
      rw [simulateQ_bind, mem_support_bind_iff] at supported
      obtain ⟨assigned, assignedMember, supported⟩ := supported
      change assigned ∈ support (pure (codec.assignedId response) : ProbComp _) at assignedMember
      rw [support_pure, Set.mem_singleton_iff] at assignedMember
      subst assignedMember
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at supported
      subst supported
      exact ⟨rfl, rfl⟩

/-- A successful challenge-handle preparation at a completed binding reads the response from the finish bytes, and its metadata is the control's expected Server binding, the assigned key ID read from that response and the completed binding. -/
theorem prepareCE_facts (challenge : MlKem768Ciphertext) (binding : session.CompletedRegistrationBinding)
    (control : pqxdh.BeaconInitSent) (identity : IdentitySeed)
    (prekey oneTime : ScalarBytes) (kem : MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (prepared : PqxdhBeaconPhase2Shared.Prepared Response Shared)
    (supported : some prepared ∈ support (simulateQ (preparationCE setup codec challenge)
      (PqxdhBeaconPhase2Shared.prepare binding control identity prekey oneTime kem raw))) :
    ∃ response, codec.read2 raw = some response ∧
      prepared.metadata = ⟨control.expected_server_binding, codec.assignedId response, binding⟩ := by
  simp only [PqxdhBeaconPhase2Shared.prepare, simulateQ_bind, mem_support_bind_iff] at supported
  obtain ⟨inputs, collected, supported⟩ := supported
  rcases inputs with _ | inputs
  · simp at supported
  obtain ⟨decoded, assigned⟩ := collectCE_inputs setup codec challenge identity prekey oneTime kem raw inputs collected
  simp only [PqxdhBeaconPhase2Shared.afterInputs, simulateQ_bind, simulateQ_pure, mem_support_bind_iff] at supported
  obtain ⟨_, _, supported⟩ := supported
  rw [support_pure, Set.mem_singleton_iff] at supported
  unfold PqxdhBeaconPhase2Shared.admitted at supported
  split_ifs at supported
  · simp only [Option.map_some, Option.some.injEq] at supported
    subst supported
    exact ⟨inputs.response, decoded, by rw [assigned]; rfl⟩
  · simp at supported
  · simp at supported

end Prepare

/-! ### The grouped finish -/

section Group
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response) (checks : Checks)
open PqxdhDeploymentIdealSteps (groupCE liftS)
open PqxdhDeploymentIdealSlots (Coord)

/-- A staged Beacon registration from a successful opening carries the opened candidate and the associated data of the opening. -/
theorem staged_opening (candidate : pqxdh.BeaconRegistrationCandidate) (associatedData : Std.Array Std.U8 151#usize)
    (kernel : ConcreteRatchetKernel) (reply : _) (staged : PqxdhBeaconPhase2Publication.Staged)
    (success : PqxdhBeaconPhase2Publication.afterOpening candidate associatedData kernel reply = some staged) :
    staged.authenticated.candidate = candidate ∧ staged.associatedData = associatedData := by
  obtain ⟨_, _, _, adEq, _, authenticated⟩ :=
    PqxdhBeaconPhase2Publication.afterOpening_success associatedData candidate kernel reply staged success
  exact ⟨PqxdhDeploymentCompileFootprint.authenticate_candidate _ _ _ _ authenticated, adEq⟩

/-- Every staged outcome of the native continuation after a root is an opening of the metadata-cleared candidate at the metadata's associated data, for any answers to its requests. -/
theorem afterRoot_opening (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhBeaconPhase2Shared.Prepared Response Shared) (root : PqxdhBeaconPhase2Preparation.Word32)
    (outcome : Option PqxdhBeaconPhase2Publication.Staged)
    (member : outcome ∈ support (PqxdhBeaconPhase2Shared.afterRoot decode pending root))
    (staged : PqxdhBeaconPhase2Publication.Staged) (found : outcome = some staged) :
    ∃ kernel reply, PqxdhBeaconPhase2Publication.afterOpening
      (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) pending.metadata.associatedData kernel reply =
        some staged := by
  unfold PqxdhBeaconPhase2Shared.afterRoot at member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, -, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨raw, -, member⟩ := member
  rcases raw with _ | raw
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    cases found
  · rw [mem_support_bind_iff] at member
    obtain ⟨result, -, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨_, _, found⟩

/-- Every staged outcome of the hidden continuation of the factored services at any value is an opening of the cleared candidate of its prepared state at the associated data of its completed binding. -/
theorem hiddenAfter_opening (value : PqxdhRegistrationJointKemEntryFactor.Output)
    (prepared : PqxdhPhase2DhMetadata.Prepared Response) (state : RawCtxSharedPrimitive.SharedState Unit)
    (outcome : Option PqxdhBeaconPhase2Publication.Staged × RawCtxSharedPrimitive.SharedState Unit)
    (member : outcome ∈ support (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenAfter
      prepared).run state))
    (staged : PqxdhBeaconPhase2Publication.Staged) (found : outcome.1 = some staged) :
    ∃ kernel reply, PqxdhBeaconPhase2Publication.afterOpening
      (PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhPhase2DhRootConsumer.cleared prepared).candidate)
        prepared.metadata.completed.associated_data kernel reply = some staged := by
  simp only [PqxdhRegistrationJointKemEntryFactor.factoredHidden, PqxdhServerAuthBeaconFactor.factored,
    StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨⟨raw, after⟩, -, member⟩ := member
  rcases raw with _ | raw
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases found
  · simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨result, -, rfl⟩ := member
    exact ⟨_, _, found⟩

/-- The CE-native grouped finish with the factored hidden services changes only the CTX cache of the game state, and every staged outcome carries the metadata-cleared candidate of the pending finish and its associated data. -/
theorem groupCE_footprint (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (s : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (r : Option PqxdhBeaconPhase2Publication.Staged × (PqxdhServerAuthNative.NativeState KemSK × Option Coord))
    (member : r ∈ support ((groupCE setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
      pending).run s)) :
    r.2.1.2 = { s.1.2 with ctx := r.2.1.2.ctx } ∧
      ∀ staged, r.1 = some staged →
        staged.authenticated.candidate = PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata ∧
          staged.associatedData = pending.metadata.associatedData := by
  unfold PqxdhDeploymentIdealSteps.groupCE at member
  change r ∈ support (match pending.root.shared with
    | .challenge => _
    | .known _ => _) at member
  split at member
  · split at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨value, -, member⟩ := member
      rw [mem_support_bind_iff] at member
      obtain ⟨ctx, ctxMember, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [support_liftComp] at ctxMember
      simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at ctxMember
      obtain ⟨inner, innerMember, rfl⟩ := ctxMember
      refine ⟨rfl, fun staged found => ?_⟩
      obtain ⟨kernel, reply, opened⟩ := hiddenAfter_opening setup codec checks value _ _ inner innerMember staged found
      obtain ⟨candidateEq, adEq⟩ := staged_opening _ _ kernel reply staged opened
      exact ⟨candidateEq, adEq⟩
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, fun staged found => by cases found⟩
  · rw [support_map, support_liftComp] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    rw [StateT.run_bind, mem_support_bind_iff] at innerMember
    obtain ⟨rooted, rootedMember, innerMember⟩ := innerMember
    have rootKept : rooted.2.2 = s.1.2 := by
      unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot at rootedMember
      split at rootedMember
      · simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, support_map, Set.mem_image] at rootedMember
        obtain ⟨_, _, rfl⟩ := rootedMember
        rfl
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rootedMember
        subst rootedMember
        rfl
    split at innerMember
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerMember
      subst innerMember
      refine ⟨?_, fun staged found => by cases found⟩
      change rooted.2.2 = { s.1.2 with ctx := rooted.2.2.ctx }
      rw [rootKept]
    · rename_i root _
      simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at innerMember
      obtain ⟨tailed, tailedMember, rfl⟩ := innerMember
      refine ⟨by rw [← rootKept], fun staged found => ?_⟩
      have opened : tailed.1 ∈ support (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root) := by
        apply OracleComp.support_simulateQ_run'_subset (PqxdhRegistrationJointKemPostSkeleton.tailNative setup codec) _ _
        rw [StateT.run'_eq, support_map]
        exact ⟨tailed, tailedMember, rfl⟩
      obtain ⟨kernel, reply, success⟩ := afterRoot_opening codec.frameRead pending root tailed.1 opened staged found
      exact staged_opening _ _ kernel reply staged success

/-- Every request of the Beacon's native primitive interpreter keeps or extends the CTX cache. -/
theorem nativePrim_ctx (query : RawCtxWholeOwner.PrimitiveSpec.Domain)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support ((PqxdhServerAuthBeaconFactor.nativePrim setup codec query).run before),
      before.2 ≤ result.2.2 := by
  intro result member
  change result ∈ support ((simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto
    (RawCtxSourceHkdf.kdfImpl setup.source)) (RawCtxSourceOpen.nativeAdapter query)).run before) at member
  exact PqxdhServerAuthExperiment.run_rel _ (fun before after => before.2 ≤ after.2) (fun _ => le_rfl)
    (fun _ _ _ left right => le_trans left right)
    (fun query state result supported => PqxdhServerAuthExperiment.nativeImpl_grows setup.source query state result
      supported) _ before result member

/-- Every request of the labelled Beacon receive over the native primitives keeps or extends the CTX cache. -/
theorem primLabels_ctx (challenge : beaconcrypt_core.ratchet.RatchetKdfResponse)
    (query : (RawCtxChainReceive.ReceiveSpec RawCtxSelectedChain.Slot RawCtxSelectedChain.Slot
      beaconcrypt_core.ratchet.RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support ((PqxdhServerAuthBeaconFactor.primLabels (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      setup.source challenge query).run before), before.2 ≤ result.2.2 := by
  intro result member
  rcases query with slot | pending
  · simp only [PqxdhServerAuthBeaconFactor.primLabels, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  · simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose] at member
    exact PqxdhServerAuthExperiment.run_rel _ (fun before after => before.2 ≤ after.2) (fun _ => le_rfl)
      (fun _ _ _ left right => le_trans left right)
      (fun query state result supported => nativePrim_ctx setup codec query state result supported) _ before result
      member

/-- A raw receive of a chain owner keeps or extends the CTX cache when its receive call does. -/
theorem rawReceive_ctx {Kernel Metadata : Type}
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (grows : ∀ entry target context state, ∀ result ∈ support ((calls.receive entry target context).run state),
      state.2 ≤ result.2.2)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : RawCtxChainOwner.State Kernel Metadata)
    (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support (((RawCtxChainOwner.rawReceive calls decode raw).run owner).run before), before.2 ≤ result.2.2 := by
  intro result supported
  change result ∈ support ((if raw.isEmpty then pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) else
    match decode raw with
    | none => pure (RawCtxChainOwner.publish owner (owner.kernel, .None))
    | some frame =>
      if RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame then do
        let result ← calls.receive owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩
        pure (RawCtxChainOwner.publish owner result)
      else pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) :
        StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp _).run before) at supported
  have kept : ∀ value, result ∈ support ((pure value : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp _).run
      before) → before.2 ≤ result.2.2 := by
    intro value member
    rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  split at supported
  · exact kept _ supported
  · split at supported
    · exact kept _ supported
    · split at supported
      · rw [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨received, member, published⟩ := supported
        rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at published
        subst published
        exact grows _ _ _ before received member
      · exact kept _ supported

/-- The hidden continuation of the factored services at any value keeps or extends the CTX cache. -/
theorem hiddenAfter_ctx (value : PqxdhRegistrationJointKemEntryFactor.Output)
    (prepared : PqxdhPhase2DhMetadata.Prepared Response) (before : RawCtxSharedPrimitive.SharedState Unit) :
    ∀ result ∈ support (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenAfter
      prepared).run before), before.2 ≤ result.2.2 := by
  intro result member
  simp only [PqxdhRegistrationJointKemEntryFactor.factoredHidden, PqxdhServerAuthBeaconFactor.factored,
    StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨⟨raw, after⟩, applied, member⟩ := member
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at applied
  obtain ⟨-, rfl⟩ := applied
  rcases raw with _ | raw
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl
  · simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨received, receivedMember, rfl⟩ := member
    exact rawReceive_ctx _ (fun entry target context state result member =>
      PqxdhServerAuthExperiment.run_rel _ (fun before after => before.2 ≤ after.2) (fun _ => le_rfl)
        (fun _ _ _ left right => le_trans left right)
        (fun query state result supported => primLabels_ctx setup codec _ query state result supported) _ state result
        member) _ _ _ _ received receivedMember

/-- The CE-native grouped finish with the factored hidden services keeps or extends the CTX cache of the game state. -/
theorem groupCE_ctx (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (s : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (r : Option PqxdhBeaconPhase2Publication.Staged × (PqxdhServerAuthNative.NativeState KemSK × Option Coord))
    (member : r ∈ support ((groupCE setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
      pending).run s)) :
    s.1.2.ctx ≤ r.2.1.2.ctx := by
  unfold PqxdhDeploymentIdealSteps.groupCE at member
  change r ∈ support (match pending.root.shared with
    | .challenge => _
    | .known _ => _) at member
  split at member
  · split at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨value, -, member⟩ := member
      rw [mem_support_bind_iff] at member
      obtain ⟨ctx, ctxMember, member⟩ := member
      rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [support_liftComp] at ctxMember
      simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at ctxMember
      obtain ⟨inner, innerMember, rfl⟩ := ctxMember
      exact hiddenAfter_ctx setup codec checks value _ ((), s.1.2.ctx) inner innerMember
    · rw [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_rfl
  · rw [support_map, support_liftComp] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    rw [StateT.run_bind, mem_support_bind_iff] at innerMember
    obtain ⟨rooted, rootedMember, innerMember⟩ := innerMember
    have rootKept : rooted.2.2 = s.1.2 := by
      unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot at rootedMember
      split at rootedMember
      · simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, support_map, Set.mem_image] at rootedMember
        obtain ⟨_, _, rfl⟩ := rootedMember
        rfl
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rootedMember
        subst rootedMember
        rfl
    split at innerMember
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerMember
      subst innerMember
      change s.1.2.ctx ≤ rooted.2.2.ctx
      rw [rootKept]
    · simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, support_map, Set.mem_image] at innerMember
      obtain ⟨tailed, tailedMember, rfl⟩ := innerMember
      change s.1.2.ctx ≤ tailed.2.2
      rw [← rootKept]
      refine PqxdhServerAuthExperiment.run_rel _ (fun before after => before.2 ≤ after.2) (fun _ => le_rfl)
        (fun _ _ _ left right => le_trans left right) (fun query before result member => ?_) _ _ tailed tailedMember
      rcases query with query | (input | request | response)
      · exact PqxdhServerAuthExperiment.beaconNative_grows setup codec (.inl query) before result member
      · simp only [PqxdhRegistrationJointKemPostSkeleton.tailNative, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at member
        subst member
        exact le_rfl
      · exact PqxdhServerAuthExperiment.beaconNative_grows setup codec (.inr (.initial request)) before result member
      · exact PqxdhServerAuthExperiment.beaconNative_grows setup codec (.inr (.application response)) before result
          member

/-- The source commit of a Beacon finish (`PqxdhBeaconPhase2Publication.finish`) on a staged outcome that carries the control's expected Server binding, a given assigned key ID and a given associated data: a rejection aborts the owner, and a success establishes it with that binding, key ID and associated data. -/
theorem finish_shape {I D K : Type} (control : pqxdh.BeaconInitSent) (owner : RawCtxBeaconLifecycle.State I D K)
    (assigned : Std.U64) (associatedData : Std.Array Std.U8 151#usize) (outcome : Option PqxdhBeaconPhase2Publication.Staged)
    (facts : ∀ staged, outcome = some staged →
      staged.authenticated.candidate.server_binding = control.expected_server_binding ∧
        staged.authenticated.candidate.assigned_key_id = assigned ∧
        staged.associatedData = associatedData) :
    ((PqxdhBeaconPhase2Publication.finish control owner outcome).1 = none →
        (PqxdhBeaconPhase2Publication.finish control owner outcome).2 = PqxdhBeaconPhase2Preparation.abort control owner) ∧
      (∀ plaintext, (PqxdhBeaconPhase2Publication.finish control owner outcome).1 = some plaintext → ∃ kernel,
        (PqxdhBeaconPhase2Publication.finish control owner outcome).2 = { owner with beacon := { owner.beacon with
          identityKeyId := assigned
          phase := .established ⟨control.expected_server_binding, assigned⟩ associatedData kernel } }) := by
  rcases outcome with _ | staged
  · exact ⟨fun _ => rfl, fun _ found => by cases found⟩
  · obtain ⟨binding, assignedEq, adEq⟩ := facts staged rfl
    unfold PqxdhBeaconPhase2Publication.finish
    dsimp only
    split_ifs
    · exact ⟨fun _ => rfl, fun _ found => by cases found⟩
    · exact ⟨fun _ => rfl, fun _ found => by cases found⟩
    · refine ⟨(fun found => by cases found), fun _ _ => ⟨staged.kernel, ?_⟩⟩
      simp only [PqxdhBeaconPhase2Publication.publish, binding, assignedEq, adEq]

/-- Owner k's grouped native finish under `ownerImplCE` with the factored hidden services and the challenge handle, through the first-touch allocator (CE-3's `PqxdhDeploymentCompileFootprint.finish_owner` for the CE-native challenge finish): it changes only the CTX cache of the game state; a rejection keeps the owner or aborts an `initSent` owner; a success comes from an `initSent` owner and establishes it with the expected Server binding, the assigned key ID read from the finish bytes by the codec Phase 2 reader as both the control's assigned key ID and the outer key ID, and the associated data of the `initSent` control. -/
theorem groupedOwnerCE_footprint {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (binding : session.CompletedRegistrationBinding) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge)
          (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) binding raw owner)).run state)).run slots)) :
    result.1.2.1.2 = { state.1.2 with ctx := result.1.2.1.2.ctx } ∧
      (result.1.1.1 = none → result.1.1.2 = owner ∨ ∃ control prekey oneTime kem,
        owner.beacon.phase = .initSent control prekey oneTime kem ∧
        result.1.1.2 = PqxdhBeaconPhase2Preparation.abort control owner) ∧
      (∀ plaintext, result.1.1.1 = some plaintext → ∃ control prekey oneTime kem response kernel,
        owner.beacon.phase = .initSent control prekey oneTime kem ∧ codec.read2 raw = some response ∧
        result.1.1.2 = { owner with beacon := { owner.beacon with
          identityKeyId := codec.assignedId response
          phase := (.established ⟨control.expected_server_binding, codec.assignedId response⟩
            binding.associated_data kernel) } }) := by
  unfold PqxdhDeploymentIdealSteps.groupedOwnerCE at member
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals simp only [phase] at member
  case initSent =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      PqxdhDeploymentIdealPostChallenge.slot_prep setup codec p, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨prepared, preparedMember, member⟩ := member
    rcases prepared with _ | prepared
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, fun _ => Or.inr ⟨control, prekey, oneTime, kem, rfl, rfl⟩, fun _ found => by cases found⟩
    obtain ⟨response, decoded, metadata⟩ := prepareCE_facts setup codec p.challenge binding control owner.beacon.identity
      prekey oneTime kem raw prepared preparedMember
    dsimp only at member
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨grouped, groupedMember, member⟩ := member
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    have inner : grouped.1 ∈ support ((groupCE setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec
        checks) prepared).run state) := by
      apply OracleComp.support_simulateQ_run'_subset
        (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ slots
      rw [StateT.run'_eq, support_map]
      rw [simulateQ_spec_query] at groupedMember
      exact ⟨grouped, groupedMember, rfl⟩
    obtain ⟨ctx, staged⟩ := groupCE_footprint setup codec checks prepared state grouped.1 inner
    have shape := finish_shape control owner (codec.assignedId response) binding.associated_data grouped.1.1
      (fun outcome found => by
      obtain ⟨candidateEq, adEq⟩ := staged outcome found
      rw [candidateEq, adEq, metadata]
      exact ⟨rfl, rfl, rfl⟩)
    refine ⟨ctx, fun failed => Or.inr ⟨control, prekey, oneTime, kem, rfl, shape.1 failed⟩, fun plaintext found => ?_⟩
    obtain ⟨kernel, established⟩ := shape.2 plaintext found
    exact ⟨control, prekey, oneTime, kem, response, kernel, rfl, decoded, established⟩

  all_goals
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, fun _ => Or.inl rfl, fun _ found => by cases found⟩

/-- Owner k's grouped native finish under `ownerImplCE` with the factored hidden services and the challenge handle, through the first-touch allocator, keeps or extends the CTX cache of the game state. -/
theorem groupedOwnerCE_ctx {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (binding : session.CompletedRegistrationBinding) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge)
          (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) binding raw owner)).run state)).run slots)) :
    state.1.2.ctx ≤ result.1.2.1.2.ctx := by
  unfold PqxdhDeploymentIdealSteps.groupedOwnerCE at member
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals simp only [phase] at member
  case initSent =>
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind,
      PqxdhDeploymentIdealPostChallenge.slot_prep setup codec p, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨prepared, -, member⟩ := member
    rcases prepared with _ | prepared
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact le_rfl
    dsimp only at member
    rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨grouped, groupedMember, member⟩ := member
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    have inner : grouped.1 ∈ support ((groupCE setup codec (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec
        checks) prepared).run state) := by
      apply OracleComp.support_simulateQ_run'_subset
        (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ slots
      rw [StateT.run'_eq, support_map]
      rw [simulateQ_spec_query] at groupedMember
      exact ⟨grouped, groupedMember, rfl⟩
    exact groupCE_ctx setup codec checks prepared state grouped.1 inner
  all_goals
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact le_rfl

/-- Owner k's hashed grouped native finish (`PqxdhDeploymentIdealSteps.hashedOwnerCE`) under the factored hidden services and the challenge handle, through the first-touch allocator (CE-3's `PqxdhDeploymentCompileFootprint.ownerFinish_owner` for the CE-native challenge finish): it changes only the CTX cache of the game state, which it only extends; a rejection keeps the owner or aborts an `initSent` owner; a success comes from an `initSent` owner with a retained bundle and a decodable finish input, leaves the transcript of that bundle and the decoded response fields cached at a digest, and establishes the owner with the expected Server binding, the assigned key ID read from the finish bytes as both the control's assigned key ID and the outer key ID, and the associated data `PqxdhTranscriptAd.adOf` of that digest. -/
theorem hashedOwnerCE_footprint {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((PqxdhDeploymentIdealSteps.hashedOwnerCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge retained raw owner).run
          state)).run slots)) :
    result.1.2.1.2 = { state.1.2 with ctx := result.1.2.1.2.ctx } ∧ state.1.2.ctx ≤ result.1.2.1.2.ctx ∧
      (result.1.1.1 = none → result.1.1.2 = owner ∨ ∃ control prekey oneTime kem,
        owner.beacon.phase = .initSent control prekey oneTime kem ∧
        result.1.1.2 = PqxdhBeaconPhase2Preparation.abort control owner) ∧
      (∀ plaintext, result.1.1.1 = some plaintext → ∃ control prekey oneTime kem response kernel init fields digest,
        owner.beacon.phase = .initSent control prekey oneTime kem ∧ codec.read2 raw = some response ∧
        retained = some init ∧ PqxdhServerAuthExperiment.responseOf codec raw = some fields ∧
        result.1.2.1.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
        result.1.1.2 = { owner with beacon := { owner.beacon with
          identityKeyId := codec.assignedId response
          phase := (.established ⟨control.expected_server_binding, codec.assignedId response⟩
            (PqxdhTranscriptAd.adOf digest) kernel) } }) := by
  unfold PqxdhDeploymentIdealSteps.hashedOwnerCE at member
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals simp only [phase] at member
  case initSent =>
    rcases retained with _ | init
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, le_rfl, fun _ => Or.inr ⟨control, prekey, oneTime, kem, rfl, rfl⟩, fun _ found => by cases found⟩
    rcases decoded : PqxdhServerAuthExperiment.responseOf codec raw with _ | fields
    · simp only [decoded, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, le_rfl, fun _ => Or.inr ⟨control, prekey, oneTime, kem, rfl, rfl⟩, fun _ found => by cases found⟩
    simp only [decoded] at member
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨hashed, hashedMember, member⟩ := member
    have hashRun : hashed.1 ∈ support ((fun r => (r.1, (r.2, state.2))) <$> PqxdhDeploymentIdealSteps.liftS
        ((PqxdhServerAuthNative.nativeHash (KemSK := KemSK)
          (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields)).run state.1)) := by
      apply OracleComp.support_simulateQ_run'_subset
        (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ slots
      rw [StateT.run'_eq, support_map]
      exact ⟨hashed, hashedMember, rfl⟩
    rw [support_map, support_liftComp] at hashRun
    obtain ⟨hashOut, hashOutMember, hashEq⟩ := hashRun
    change hashOut ∈ support ((fun inner => (inner.1, (state.1.1, { state.1.2 with ctx := inner.2 }))) <$>
      (CtxRomAuth.ctxRandomOracle ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields)).run
        state.1.2.ctx) at hashOutMember
    rw [support_map] at hashOutMember
    obtain ⟨inner, innerMember, rfl⟩ := hashOutMember
    have hashLe := QueryImpl.withCaching_cache_le uniformSampleImpl _ state.1.2.ctx inner innerMember
    have cached := QueryImpl.withCaching_run_caches uniformSampleImpl _ state.1.2.ctx inner innerMember
    rcases hashed with ⟨⟨digest, hashedState⟩, hashedSlots⟩
    simp only [Prod.mk.injEq] at hashEq
    obtain ⟨rfl, rfl⟩ := hashEq
    obtain ⟨fieldsEq, rejected, published⟩ := groupedOwnerCE_footprint setup codec checks p _ raw owner _ _ result member
    have grown := groupedOwnerCE_ctx setup codec checks p _ raw owner _ _ result member
    rw [phase] at rejected published
    refine ⟨by rw [fieldsEq], le_trans hashLe grown, rejected, fun plaintext succeeded => ?_⟩
    obtain ⟨control', prekey', oneTime', kem', response, kernel, initSent, read, established⟩ :=
      published plaintext succeeded
    cases initSent
    refine ⟨control, prekey, oneTime, kem, response, kernel, init, fields, inner.1, rfl, read, rfl, rfl,
      grown cached, ?_⟩
    rw [established, PqxdhTranscriptAd.completedOf_ad]
  all_goals
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, le_rfl, fun _ => Or.inl rfl, fun _ found => by cases found⟩

end Group

/-! ### CE-3's invariant across owner k's challenge finish -/

section Good
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileInvariant (Good)

/-- CE-3's invariant survives every Beacon finish of a present owner with the footprint of `PqxdhDeploymentCompileFootprint.ownerFinish_owner` that keeps the Server fields of the game state and only extends its BLAKE2b cache, with the reply logged and the retained bundles kept (the argument of CE-3's `PqxdhDeploymentCompileInvariant.good_finish`, from the footprint alone). -/
theorem good_of_finish (index : ℕ) (raw : Pqxdh.Bytes) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (found : native.owners[index]? = some owner) (reply : Option Pqxdh.Bytes) (next : PqxdhRegistrationSchedule.Owner KemSK)
    (shared : PqxdhServerAuthNative.NativeState KemSK)
    (fixed : PqxdhDeploymentCompileFootprint.ServerFixed native.shared.2 shared.2)
    (grow : native.shared.2.ctx ≤ shared.2.ctx)
    (rejected : reply = none → next = owner ∨ ∃ control prekey oneTime kem,
      owner.beacon.phase = .initSent control prekey oneTime kem ∧ next = PqxdhBeaconPhase2Preparation.abort control owner)
    (published : ∀ plaintext, reply = some plaintext → ∃ control prekey oneTime kem response kernel init fields digest,
      owner.beacon.phase = .initSent control prekey oneTime kem ∧ codec.read2 raw = some response ∧
      native.inits index = some init ∧ PqxdhServerAuthExperiment.responseOf codec raw = some fields ∧
      shared.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
      next = { owner with beacon := { owner.beacon with
        identityKeyId := codec.assignedId response
        phase := (.established ⟨control.expected_server_binding, codec.assignedId response⟩
          (PqxdhTranscriptAd.adOf digest) kernel) } }) :
    Good setup codec { copies with log := PqxdhDeploymentCompile.logReply copies.log (.finish index raw) reply }
      ⟨shared, native.owners.set index next, native.inits⟩ := by
  have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨server, keyId, pending, sessions⟩ := fixed
  have copiedKept : ∀ other current, copies.owners other = some current →
      ∃ owner' control associatedData kernel,
        (native.owners.set index next)[other]? = some owner' ∧
        owner'.beacon.phase = .established control associatedData kernel := by
    intro other current copied
    obtain ⟨old, control, associatedData, kernel, oldFound, established⟩ := good.copied other current copied
    by_cases same : other = index
    · subst same
      rw [found, Option.some.injEq] at oldFound
      subst oldFound
      refine ⟨next, control, associatedData, kernel, List.getElem?_set_self bound, ?_⟩
      rcases reply with _ | plaintext
      · rcases rejected rfl with unchanged | ⟨control', prekey, oneTime, kem, initSent, _⟩
        · rw [unchanged]; exact established
        · rw [initSent] at established; cases established
      · obtain ⟨control', prekey, oneTime, kem, _, _, _, _, _, initSent, _⟩ := published plaintext rfl
        rw [initSent] at established
        cases established
    · exact ⟨old, control, associatedData, kernel, by rw [List.getElem?_set_ne (Ne.symm same)]; exact oldFound,
        established⟩
  have peersKept : ∀ kid peer, shared.2.server.server.peers kid = some peer →
      ∃ transcript digest, PqxdhDeploymentCompile.peerTranscript codec copies.log kid = some transcript ∧
        shared.2.ctx ((), transcript) = some digest ∧ peer.metadata = PqxdhTranscriptAd.adOf digest := by
    intro kid peer peerFound
    rw [server] at peerFound
    obtain ⟨transcript, digest, view, cached, adEq⟩ := good.peers kid peer peerFound
    exact ⟨transcript, digest, view, grow cached, adEq⟩
  rcases reply with _ | plaintext
  · simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨by rw [keyId]; exact good.keyId, ?_, by rw [server]; exact good.serverVisible,
      by simp only [List.length_set, good.count], copiedKept, ?_, by rw [pending, sessions]; exact good.pending,
      by rw [sessions]; exact good.accepts, peersKept, by rw [pending]; exact good.pendingInit⟩
    · intro kid current copied
      rw [server]
      exact good.installed kid current copied
    · intro other current currentFound
      by_cases same : other = index
      · subst same
        rw [List.getElem?_set_self bound, Option.some.injEq] at currentFound
        subst currentFound
        obtain ⟨pin, keyId', created, pinned, _⟩ := good.owners other owner found
        rcases rejected rfl with unchanged | ⟨control, prekey, oneTime, kem, _, aborted⟩
        · rw [unchanged]
          exact PqxdhDeploymentCompileInvariant.ownerShape_grow codec copies.log native.inits grow other owner
            (good.owners other owner found)
        · refine ⟨pin, keyId', created, by rw [aborted]; exact pinned, ?_⟩
          rw [aborted]
          trivial
      · rw [List.getElem?_set_ne (Ne.symm same)] at currentFound
        exact PqxdhDeploymentCompileInvariant.ownerShape_grow codec copies.log native.inits grow other current
          (good.owners other current currentFound)
  · obtain ⟨control, prekey, oneTime, kem, response, kernel, init, decodedFields, digest, initSent, decoded, retained,
      responseDecoded, cachedTranscript, established⟩ := published plaintext rfl
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨by rw [keyId]; exact good.keyId, ?_, by rw [server]; exact good.serverVisible,
      by simp only [List.length_set, good.count], copiedKept, ?_, by rw [pending, sessions]; exact good.pending,
      by rw [sessions]; exact good.accepts, peersKept, by rw [pending]; exact good.pendingInit⟩
    · intro kid current copied
      rw [server]
      exact good.installed kid current copied
    · intro other current currentFound
      by_cases same : other = index
      · subst same
        rw [List.getElem?_set_self bound, Option.some.injEq] at currentFound
        subst currentFound
        obtain ⟨pin, keyId', created, pinned, oldShape⟩ := good.owners other owner found
        rw [initSent] at oldShape
        obtain ⟨binding, bytes, logged, identified, init', initFound, initRead⟩ := oldShape
        rw [retained, Option.some.injEq] at initFound
        subst initFound
        refine ⟨pin, keyId', created, by rw [established]; exact pinned, ?_⟩
        rw [established]
        dsimp only
        refine ⟨PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) decodedFields, digest, ?_,
          cachedTranscript, rfl⟩
        simp only [PqxdhDeploymentCompile.ownerView, created, logged, identified, Function.update_self, decoded,
          Option.bind_eq_bind, Option.bind_some, Option.pure_def, PqxdhDeploymentCompile.publicTranscript, initRead,
          responseDecoded]
        rw [← binding]
      · rw [List.getElem?_set_ne (Ne.symm same)] at currentFound
        exact PqxdhDeploymentCompileInvariant.ownerShape_grow codec _ native.inits grow other current
          (PqxdhDeploymentCompileInvariant.ownerShape_finish codec copies.log native.inits native.shared.2.ctx index
            other raw same current (good.owners other current currentFound))

end Good

/-! ### Owner k's challenge finish in the middle execution -/

section Middle
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : Setup baseSpec KemSK)
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : ℕ}
  (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentIdealPostSource (Mid sourceMid compiledMid finishHiddenAt)

/-- Owner k's challenge finish of the middle execution, as the compiled step sees it: on every outcome the local copies log the reply, the accept counter is kept, and the native state of the annotated source state has the Server fields of the game state kept, its BLAKE2b cache only extended, the retained bundles kept and the addressed owner replaced as `hashedOwnerCE_footprint` describes at the owner's retained bundle. -/
theorem compiledMid_challenge (address : ℕ) (raw : Pqxdh.Bytes) (copies : Local) (m : Mid KemSK)
    (hidden : finishHiddenAt t m address = true) (result : Option Pqxdh.Bytes × (Local × Mid KemSK))
    (supported : result ∈ support ((compiledMid setup codec route checks t p created
      (.inr (.finish address raw))).run (copies, m))) :
    result.2.1 = { copies with log := PqxdhDeploymentCompile.logReply copies.log (.finish address raw) result.1 } ∧
      result.2.2.backend.2.2.accepts = m.backend.2.2.accepts ∧
      ∃ owner next shared, (PqxdhRegistrationJointSchedule.source m.joint).owners[address]? = some owner ∧
        PqxdhDeploymentCompileFootprint.ServerFixed m.joint.shared.2 shared.2 ∧ m.joint.shared.2.ctx ≤ shared.2.ctx ∧
        PqxdhRegistrationJointSchedule.source result.2.2.joint =
          ⟨shared, (PqxdhRegistrationJointSchedule.source m.joint).owners.set address next,
            (PqxdhRegistrationJointSchedule.source m.joint).inits⟩ ∧
        (result.1 = none → next = owner ∨ ∃ control prekey oneTime kem,
          owner.beacon.phase = .initSent control prekey oneTime kem ∧
          next = PqxdhBeaconPhase2Preparation.abort control owner) ∧
        (∀ plaintext, result.1 = some plaintext → ∃ control prekey oneTime kem response kernel init fields digest,
          owner.beacon.phase = .initSent control prekey oneTime kem ∧ codec.read2 raw = some response ∧
          (PqxdhRegistrationJointSchedule.source m.joint).inits address = some init ∧
          PqxdhServerAuthExperiment.responseOf codec raw = some fields ∧
          shared.2.ctx ((), PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
          next = { owner with beacon := { owner.beacon with
            identityKeyId := codec.assignedId response
            phase := (.established ⟨control.expected_server_binding, codec.assignedId response⟩
              (PqxdhTranscriptAd.adOf digest) kernel) } }) := by
  change result ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((PqxdhDeploymentCompile.forwardLogged (.finish address raw) (.finish address raw) id).run copies)).run m)
    at supported
  rw [PqxdhDeploymentIdealPostSource.compiledMid_forward, Functor.map_map, support_map] at supported
  obtain ⟨stepped, steppedMember, rfl⟩ := supported
  have sent := (of_decide_eq_true hidden).2.2
  rcases foundEntry : m.joint.owners[address]? with _ | entry
  · exfalso
    unfold PqxdhDeploymentIdealSteps.initSentAt at sent
    simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, foundEntry] at sent
  rw [PqxdhDeploymentIdealPostChallenge.sourceMid_challenge setup codec route checks t p created address raw m hidden
    entry foundEntry, support_map] at steppedMember
  obtain ⟨r, rMember, rfl⟩ := steppedMember
  obtain ⟨ctx, grow, rejected, published⟩ :=
    hashedOwnerCE_footprint setup codec checks p (m.joint.inits address) raw entry.owner (m.joint.shared, none)
      (m.backend.2.1, m.backend.1) r rMember
  refine ⟨rfl, rfl, entry.owner, r.1.1.2, r.1.2.1,
    by simp [PqxdhRegistrationJointSchedule.source, List.getElem?_map, foundEntry], ?_, grow, ?_, rejected, published⟩
  · rw [ctx]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [PqxdhDeploymentIdealPostChallenge.afterChallenge, PqxdhRegistrationJointSchedule.source, List.map_set]

/-- Owner k's challenge finish of the middle execution keeps CE-3's invariant on the local copies and the native state of the annotated source state, and the accept counter. -/
theorem good_challenge (address : ℕ) (raw : Pqxdh.Bytes) (copies : Local) (m : Mid KemSK)
    (hidden : finishHiddenAt t m address = true)
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (result : Option Pqxdh.Bytes × (Local × Mid KemSK))
    (supported : result ∈ support ((compiledMid setup codec route checks t p created
      (.inr (.finish address raw))).run (copies, m))) :
    Good setup codec result.2.1 (PqxdhRegistrationJointSchedule.source result.2.2.joint) ∧
      result.2.2.backend.2.2.accepts = m.backend.2.2.accepts := by
  obtain ⟨copied, accepts, owner, next, shared, found, fixed, grow, joint, rejected, published⟩ :=
    compiledMid_challenge setup codec route checks t p created address raw copies m hidden result supported
  refine ⟨?_, accepts⟩
  rw [copied, joint]
  exact good_of_finish setup codec address raw copies _ good owner found result.1 next shared fixed grow rejected
    published

end Middle

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.collectCE_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.collectCE_inputs

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.prepareCE_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.prepareCE_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.staged_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.staged_opening

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.afterRoot_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.afterRoot_opening

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.hiddenAfter_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.hiddenAfter_opening

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupCE_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupCE_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.finish_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.finish_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupedOwnerCE_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupedOwnerCE_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.good_of_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.good_of_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.compiledMid_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.compiledMid_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.good_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.good_challenge
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.nativePrim_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.nativePrim_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.primLabels_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.primLabels_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.rawReceive_ctx' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.rawReceive_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.hiddenAfter_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.hiddenAfter_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupCE_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupCE_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupedOwnerCE_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.groupedOwnerCE_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.hashedOwnerCE_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish.hashedOwnerCE_footprint
