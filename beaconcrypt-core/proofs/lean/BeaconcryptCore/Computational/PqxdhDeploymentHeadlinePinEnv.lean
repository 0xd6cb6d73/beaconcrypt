import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects
import BeaconcryptCore.Computational.PqxdhDeploymentCompileFootprint
import BeaconcryptCore.Computational.PqxdhEnvironmentForward
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv

/-!
# Source certificates for the computational Server-pin row

Every newly installed Beacon shell and Server peer binding carries AD151 assembled from a digest cached at the exact registration transcript. The Beacon transcript's response identity is its stored public pin; the Server transcript's response identity is the Server's own identity. These source facts include the native and erased hidden finish paths, successful builds, and every optional failure and rollback branch.

`InstallPin` and `InstallOk` are indexed by an ambient cache. `envGD_ok_cached` proves installation admissibility on the reply-refined source tree of `PqxdhDeploymentHeadlinePinEffects`; that module derives the refinement from actual CTX execution and cache growth. This is internal proof evidence and imposes no new contract on arbitrary source callbacks or deployment callers. The movement facts separately preserve the public pins, Server identity and written Phase 2 fields. Generic writer lemmas remain parametric in the actual per-call AD151.

These facts replace the old identity-derived AD281 and legacy-peer assertions. They change no protocol event, distribution or cryptographic assumption.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv

section NativeReceipts

open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhRegistrationSchedule (Owner ownerFinish)
open PqxdhDeploymentCompileFootprint (preparationHandler)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealSteps (groupCE)
open PqxdhDeploymentIdealPostGoodFinish (prepareCE_facts groupCE_footprint)
open PqxdhRefinement
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Native owner finish keeps the owner's stored public Server pin on every success, abort and inactive branch. -/
theorem nativeOwnerFinish_serverIdentity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (state : NativeState KemSK) (result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((ownerFinish setup codec retained raw owner).run state)) :
    result.1.2.beacon.serverIdentity = owner.beacon.serverIdentity := by
  obtain ⟨_, _, failure, success⟩ := PqxdhDeploymentCompileFootprint.ownerFinish_owner setup codec retained raw
    owner state result supported
  cases reply : result.1.1 with
  | none =>
    rcases failure reply with same | ⟨control, _, _, _, _, aborted⟩
    · rw [same]
    · rw [aborted]
      rfl
  | some plaintext =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, installed⟩ := success plaintext reply
    rw [installed]

/-- Pure typed response decoding gives the response width receipt and the exact decoded identity getter. -/
theorem nativeOwnerFinish_response_fields (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (fields : Pqxdh.SessionTranscript.ResponseFields) (decoded : responseOf codec raw = some fields) :
    fields.WellFormed ∧ ∃ response server, codec.read2 raw = some response ∧
      codec.serverIdentity response = some server ∧ fields.identityKey = absBytes server := by
  unfold responseOf at decoded
  obtain ⟨response, read, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨ciphertext, cipherRead, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨ephemeral, ephemeralRead, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨server, serverRead, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  cases Option.some.inj decoded
  exact ⟨PqxdhTranscriptAd.adResponse_wellFormed _ _ _ _, response, server, read, serverRead, rfl⟩


/-- Successful collection retains exactly the Server identity read from the actual Phase 2 response. -/
theorem nativeOwnerFinish_collect_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identity : IdentitySeed)
    (prekey oneTime : ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (shared : NativeState KemSK) (inputs : PqxdhBeaconPhase2Preparation.Inputs Response) (after : NativeState KemSK)
    (supported : (some inputs, after) ∈ support ((simulateQ (preparationHandler setup codec)
      (PqxdhBeaconPhase2Preparation.collect identity prekey oneTime kem raw)).run shared)) :
    codec.read2 raw = some inputs.response ∧ codec.serverIdentity inputs.response = some inputs.finishInputs.response_server_identity := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query] at supported
  have decodeRun : (preparationHandler setup codec (.decode raw)).run shared = pure (codec.read2 raw, shared) := rfl
  rw [StateT.run_bind, decodeRun, pure_bind] at supported
  cases decoded : codec.read2 raw with
  | none => simp [decoded] at supported
  | some response =>
      simp only [decoded, Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply1, state1⟩, member1, supported⟩ := supported
      rcases reply1 with _ | reply1
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply2, state2⟩, member2, supported⟩ := supported
      rcases reply2 with _ | reply2
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply3, state3⟩, member3, supported⟩ := supported
      rcases reply3 with _ | reply3
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply4, state4⟩, member4, supported⟩ := supported
      rcases reply4 with _ | reply4
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply5, state5⟩, member5, supported⟩ := supported
      rcases reply5 with _ | reply5
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply6, state6⟩, member6, supported⟩ := supported
      rcases reply6 with _ | reply6
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply7, state7⟩, member7, supported⟩ := supported
      rcases reply7 with _ | reply7
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply8, state8⟩, member8, supported⟩ := supported
      rcases reply8 with _ | reply8
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply9, state9⟩, member9, supported⟩ := supported
      rcases reply9 with _ | reply9
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply10, state10⟩, member10, supported⟩ := supported
      rcases reply10 with _ | reply10
      · simp at supported
      simp only [Option.elim_some] at supported
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨assigned, final⟩, assignedMember, supported⟩ := supported
      change (assigned, final) ∈ support (pure (codec.assignedId response, state10) : ProbComp _) at assignedMember
      rw [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at assignedMember
      obtain ⟨rfl, rfl⟩ := assignedMember
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some.injEq] at supported
      obtain ⟨rfl, rfl⟩ := supported
      refine ⟨rfl, ?_⟩
      change (some reply3, state3) ∈ support (pure (codec.serverIdentity response, state2) : ProbComp _) at member3
      exact (congrArg Prod.fst (eq_of_mem_support_pure _ member3)).symm


/-- Native success enforces both the core's response-identity check and the outer owner's stored Server pin. -/
theorem nativeOwnerFinish_native_pin (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (shared : NativeState KemSK) (result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding) codec.frameRead raw owner)).run shared))
    (plaintext : Pqxdh.Bytes) (succeeded : result.1.1 = some plaintext)
    (fields : Pqxdh.SessionTranscript.ResponseFields) (decoded : responseOf codec raw = some fields) :
    fields.identityKey = absBytes owner.beacon.serverIdentity := by
  rw [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose] at supported
  rcases result with ⟨⟨reply, next⟩, final⟩
  simp only at succeeded
  subst succeeded
  obtain ⟨control, prekey, oneTime, kem, prepared, intermediate, staged, phase, prepareSupport, tailSupport,
    finished, _, _, published⟩ := PqxdhBeaconPhase2Publication.owner_success (completedBinding := completedBinding)
      _ codec.frameRead raw plaintext owner next shared final supported
  have handlerEq : (fun query => (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ
      PqxdhBeaconPhase2Publication.nativeAdapter) (.inl query)) = preparationHandler setup codec := by
    funext query
    simp only [QueryImpl.compose, PqxdhBeaconPhase2Publication.nativeAdapter, simulateQ_spec_query]
    rfl
  rw [handlerEq] at prepareSupport
  obtain ⟨inputs, middle, collected, _, coreFinished, _, _, _⟩ :=
    PqxdhBeaconPhase2Preparation.prepare_origin (completedBinding := completedBinding) _ control owner.beacon.identity
      prekey oneTime kem raw shared intermediate prepared prepareSupport
  obtain ⟨read, serverRead⟩ := nativeOwnerFinish_collect_identity setup codec owner.beacon.identity prekey oneTime kem
    raw shared inputs middle collected
  obtain ⟨_, response, server, read', serverRead', identity⟩ := nativeOwnerFinish_response_fields codec raw fields decoded
  rw [read, Option.some.injEq] at read'
  subst response
  rw [serverRead, Option.some.injEq] at serverRead'
  subst server
  have expected : control.expected_server_binding.identity_public_key = inputs.finishInputs.response_server_identity := by
    by_contra different
    have rejected := BeaconcryptCore.Refinement.PqxdhSurface.beacon_response_identity_mismatch_is_rejected
      control inputs.finishInputs different
    rw [coreFinished] at rejected
    cases rejected
  have binding := (PqxdhDeploymentCompileFootprint.prepare_finish_shape control inputs.finishInputs prepared.candidate
    coreFinished).1
  obtain ⟨root, rootState, _, rooted⟩ := PqxdhBeaconPhase2Publication.tail_supported _ codec.frameRead prepared
    intermediate final staged tailSupport
  obtain ⟨_, _, _, _, received, _, _, _, _, opened⟩ := PqxdhBeaconPhase2Publication.afterRoot_supported _
    codec.frameRead prepared root rootState final staged rooted
  obtain ⟨_, _, _, _, _, authenticated⟩ := PqxdhBeaconPhase2Publication.afterOpening_success
    (associatedData := prepared.binding.associated_data) _ _ _ staged opened
  have candidateEq := PqxdhDeploymentCompileFootprint.authenticate_candidate _ _ _ _ authenticated
  obtain ⟨actual, same, _, pin, _⟩ := PqxdhBeaconPhase2Publication.finish_success control owner next (some staged)
    plaintext finished
  have same' := Option.some.inj same
  subst actual
  rw [candidateEq, (PqxdhBeaconPhase2Publication.clearedCandidate_fields _).1, binding] at pin
  exact identity.trans ((congrArg absBytes expected.symm).trans pin.symm)

/-- The actual hashed owner finish preserves the native success pin check. -/
theorem nativeOwnerFinish_pin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (shared : NativeState KemSK) (result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((ownerFinish setup codec retained raw owner).run shared))
    (plaintext : Pqxdh.Bytes) (succeeded : result.1.1 = some plaintext)
    (fields : Pqxdh.SessionTranscript.ResponseFields) (decoded : responseOf codec raw = some fields) :
    fields.identityKey = absBytes owner.beacon.serverIdentity := by
  cases phase : owner.beacon.phase with
  | initSent control prekey oneTime kem =>
    cases retained with
    | none =>
      rw [PqxdhRegistrationSchedule.ownerFinish_unhashed setup codec _ raw owner control prekey oneTime kem phase
        (Or.inl rfl), StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases succeeded
    | some init =>
      rw [PqxdhRegistrationSchedule.ownerFinish_hashed setup codec init raw owner control prekey oneTime kem phase
        fields decoded, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨hashed, _, native⟩ := supported
      exact nativeOwnerFinish_native_pin (PqxdhTranscriptAd.completedOf control hashed.1) setup codec raw owner
        hashed.2 result native plaintext succeeded fields decoded
  | _ =>
    simp only [ownerFinish, phase, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases succeeded

/-- Native successful establishment yields the exact cached transcript, installed AD, response-width receipt and stored Server pin. -/
theorem nativeOwnerFinish_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (shared : NativeState KemSK) (result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((ownerFinish setup codec retained raw owner).run shared))
    (plaintext : Pqxdh.Bytes) (succeeded : result.1.1 = some plaintext) :
    ∃ init fields digest control kernel, retained = some init ∧ responseOf codec raw = some fields ∧
      result.2.2.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
      result.1.2.beacon.phase = .established control (PqxdhTranscriptAd.adOf digest) kernel ∧
      fields.identityKey = absBytes owner.beacon.serverIdentity ∧ fields.WellFormed := by
  obtain ⟨_, _, _, success⟩ := PqxdhDeploymentCompileFootprint.ownerFinish_owner setup codec retained raw owner
    shared result supported
  obtain ⟨control, prekey, oneTime, kem, response, kernel, init, fields, digest, _, _, retainedEq, decoded, cached,
    installed⟩ := success plaintext succeeded
  refine ⟨init, fields, digest, ⟨control.expected_server_binding, codec.assignedId response⟩, kernel, retainedEq,
    decoded, cached, ?_, nativeOwnerFinish_pin setup codec retained raw owner shared result supported plaintext
      succeeded fields decoded, (nativeOwnerFinish_response_fields codec raw fields decoded).1⟩
  rw [installed]

/-- The install-producing branch is a successful finish: unchanged or aborted failure outcomes cannot newly establish an owner. -/
theorem nativeOwnerFinish_new_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes) (owner : Owner KemSK)
    (shared : NativeState KemSK) (result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((ownerFinish setup codec retained raw owner).run shared))
    (control : beaconcrypt_core.pqxdh.BeaconEstablished) (ad : PqxdhTranscriptAd.AssociatedData)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (established : result.1.2.beacon.phase = .established control ad kernel)
    (inactive : ¬ RawCtxBeaconLifecycle.Established owner.beacon.phase) :
    ∃ init fields digest, retained = some init ∧ responseOf codec raw = some fields ∧
      result.2.2.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
      ad = PqxdhTranscriptAd.adOf digest ∧ fields.identityKey = absBytes owner.beacon.serverIdentity ∧
      fields.WellFormed := by
  cases reply : result.1.1 with
  | none =>
    have failure := (PqxdhDeploymentCompileFootprint.ownerFinish_owner setup codec retained raw owner shared result
      supported).2.2.1 reply
    rcases failure with same | ⟨control, _, _, _, _, aborted⟩
    · rw [same] at established
      exact (inactive (by rw [established]; trivial)).elim
    · rw [aborted] at established
      cases established
  | some plaintext =>
    obtain ⟨init, fields, digest, afterControl, afterKernel, retainedEq, decoded, cached, installed, identity, width⟩ :=
      nativeOwnerFinish_receipt setup codec retained raw owner shared result supported plaintext reply
    have same := RawCtxBeaconLifecycle.Phase.established.inj (established.symm.trans installed)
    exact ⟨init, fields, digest, retainedEq, decoded, cached, same.2.1, identity, width⟩

/-- The outer source finish keeps the stored Server pin for every supplied staged reply. -/
theorem nativeOwnerFinish_finish_serverIdentity {I D K : Type}
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (owner : PqxdhBeaconPhase2Preparation.State I D K)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (PqxdhBeaconPhase2Publication.finish control owner staged).2.beacon.serverIdentity = owner.beacon.serverIdentity := by
  cases staged with
  | none => rfl
  | some staged =>
    simp only [PqxdhBeaconPhase2Publication.finish]
    split_ifs <;> rfl

/-- Every callback reply of the source Phase 2 owner keeps its stored Server pin. -/
theorem nativeOwnerFinish_owner_serverIdentity {Response : Type}
    (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (owner : Owner KemSK) :
    ∀ result ∈ support (PqxdhBeaconPhase2Publication.owner (completedBinding := completedBinding)
      (X := IdentitySeed) (Response := Response) decode raw owner),
      result.2.beacon.serverIdentity = owner.beacon.serverIdentity := by
  intro result member
  unfold PqxdhBeaconPhase2Publication.owner at member
  split at member
  · rename_i control prekey oneTime kem phase
    rw [mem_support_bind_iff] at member
    obtain ⟨prepared, _, rest⟩ := member
    cases prepared with
    | none =>
      rw [support_pure, Set.mem_singleton_iff] at rest
      subst rest
      exact nativeOwnerFinish_finish_serverIdentity control owner none
    | some prepared =>
      rw [mem_support_bind_iff] at rest
      obtain ⟨staged, _, final⟩ := rest
      rw [support_pure, Set.mem_singleton_iff] at final
      subst final
      exact nativeOwnerFinish_finish_serverIdentity control owner staged
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

/-- The native adapter preserves the same all-reply stored-Server-pin fact. -/
theorem nativeOwnerFinish_native_serverIdentity {Response : Type}
    (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (owner : Owner KemSK) :
    ∀ result ∈ support (PqxdhBeaconPhase2Publication.nativeOwner (completedBinding := completedBinding)
      (X := IdentitySeed) (Response := Response) decode raw owner),
      result.2.beacon.serverIdentity = owner.beacon.serverIdentity := by
  intro result member
  exact nativeOwnerFinish_owner_serverIdentity completedBinding decode raw owner result
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member)

/-- Challenge-handle collection retains the exact Server identity getter. -/
theorem nativeOwnerFinish_collectCE_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (identity : IdentitySeed) (prekey oneTime : ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (inputs : PqxdhBeaconPhase2Shared.Inputs Response PqxdhPhase2DecapsulationRouting.Shared)
    (supported : some inputs ∈ support (simulateQ (PqxdhDeploymentIdealSteps.preparationCE setup codec challenge)
      (PqxdhBeaconPhase2Shared.collect identity prekey oneTime kem raw))) :
    codec.read2 raw = some inputs.response ∧ codec.serverIdentity inputs.response = some inputs.serverIdentity := by
  simp only [PqxdhBeaconPhase2Shared.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query] at supported
  rw [show PqxdhDeploymentIdealSteps.preparationCE setup codec challenge (.decode raw) = pure (codec.read2 raw)
    from rfl, pure_bind] at supported
  cases decoded : codec.read2 raw with
  | none => simp [decoded] at supported
  | some response =>
    simp only [decoded, Option.elim_some] at supported
    rw [simulateQ_bind, mem_support_bind_iff] at supported
    obtain ⟨reply1, _, supported⟩ := supported
    rcases reply1 with _ | reply1
    · simp at supported
    simp only [Option.elim_some] at supported
    rw [simulateQ_bind, mem_support_bind_iff] at supported
    obtain ⟨reply2, _, supported⟩ := supported
    rcases reply2 with _ | reply2
    · simp at supported
    simp only [Option.elim_some] at supported
    rw [simulateQ_bind, mem_support_bind_iff] at supported
    obtain ⟨reply3, member3, supported⟩ := supported
    rcases reply3 with _ | reply3
    · simp at supported
    simp only [Option.elim_some] at supported
    iterate 7
      rw [simulateQ_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, supported⟩ := supported
      rcases reply with _ | reply
      · simp at supported
      simp only [Option.elim_some] at supported
    rw [simulateQ_bind, mem_support_bind_iff] at supported
    obtain ⟨assigned, _, supported⟩ := supported
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at supported
    subst supported
    refine ⟨rfl, ?_⟩
    change some reply3 ∈ support (pure (codec.serverIdentity response) : ProbComp _) at member3
    exact (eq_of_mem_support_pure _ member3).symm

/-- Challenge-handle preparation enforces the same identity pin before every hidden or native continuation. -/
theorem nativeOwnerFinish_prepareCE_pin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (binding : beaconcrypt_core.session.CompletedRegistrationBinding)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : IdentitySeed) (prekey oneTime : ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (prepared : PqxdhBeaconPhase2Shared.Prepared Response PqxdhPhase2DecapsulationRouting.Shared)
    (supported : some prepared ∈ support (simulateQ (PqxdhDeploymentIdealSteps.preparationCE setup codec challenge)
      (PqxdhBeaconPhase2Shared.prepare binding control identity prekey oneTime kem raw)))
    (fields : Pqxdh.SessionTranscript.ResponseFields) (decoded : responseOf codec raw = some fields) :
    fields.identityKey = absBytes control.expected_server_binding.identity_public_key := by
  simp only [PqxdhBeaconPhase2Shared.prepare, simulateQ_bind, mem_support_bind_iff] at supported
  obtain ⟨inputs, collected, supported⟩ := supported
  rcases inputs with _ | inputs
  · simp at supported
  obtain ⟨read, serverRead⟩ := nativeOwnerFinish_collectCE_identity setup codec challenge identity prekey oneTime kem
    raw inputs collected
  obtain ⟨_, response, server, read', serverRead', identityEq⟩ := nativeOwnerFinish_response_fields codec raw fields decoded
  rw [read, Option.some.injEq] at read'
  subst response
  rw [serverRead, Option.some.injEq] at serverRead'
  subst server
  simp only [PqxdhBeaconPhase2Shared.afterInputs, simulateQ_bind, simulateQ_pure, mem_support_bind_iff] at supported
  obtain ⟨_, _, supported⟩ := supported
  rw [support_pure, Set.mem_singleton_iff] at supported
  unfold PqxdhBeaconPhase2Shared.admitted at supported
  split_ifs at supported with identityMatches nonzero
  · exact identityEq.trans identityMatches.symm
  · simp at supported
  · simp at supported


/-- The grouped hidden finish enforces the prepared response identity and outer stored Server pin. -/
theorem nativeOwnerFinish_groupedCE_pin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (binding : beaconcrypt_core.session.CompletedRegistrationBinding) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge)
          (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) binding raw owner)).run state)).run slots)) (plaintext : Pqxdh.Bytes) (succeeded : result.1.1.1 = some plaintext)
    (fields : Pqxdh.SessionTranscript.ResponseFields) (decodedFields : responseOf codec raw = some fields) :
    fields.identityKey = absBytes owner.beacon.serverIdentity := by
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
      cases succeeded
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
    obtain ⟨_, staged⟩ := groupCE_footprint setup codec checks prepared state grouped.1 inner
    have finished : PqxdhBeaconPhase2Publication.finish control owner grouped.1.1 =
        (some plaintext, (PqxdhBeaconPhase2Publication.finish control owner grouped.1.1).2) :=
      Prod.ext succeeded rfl
    obtain ⟨actual, same, _, pin, _⟩ := PqxdhBeaconPhase2Publication.finish_success control owner _ grouped.1.1
      plaintext finished
    obtain ⟨candidateEq, _⟩ := staged actual same
    rw [candidateEq] at pin
    change absBytes owner.beacon.serverIdentity = absBytes prepared.metadata.binding.identity_public_key at pin
    rw [metadata] at pin
    exact (nativeOwnerFinish_prepareCE_pin setup codec p.challenge binding control owner.beacon.identity prekey
      oneTime kem raw prepared preparedMember fields decodedFields).trans pin.symm
  all_goals
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases succeeded


/-- Hashing the retained transcript preserves the grouped challenge finish's response pin check. -/
theorem nativeOwnerFinish_hashedCE_pin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((PqxdhDeploymentIdealSteps.hashedOwnerCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge retained raw owner).run
          state)).run slots)) (plaintext : Pqxdh.Bytes) (succeeded : result.1.1.1 = some plaintext)
    (fields : Pqxdh.SessionTranscript.ResponseFields) (decodedFields : responseOf codec raw = some fields) :
    fields.identityKey = absBytes owner.beacon.serverIdentity := by
  unfold PqxdhDeploymentIdealSteps.hashedOwnerCE at member
  rcases phase : owner.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals simp only [phase] at member
  case initSent =>
    rcases retained with _ | init
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      cases succeeded
    rcases decoded : responseOf codec raw with _ | actualFields
    · simp only [decoded, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      cases succeeded
    simp only [decoded] at member
    rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨hashed, _, member⟩ := member
    exact nativeOwnerFinish_groupedCE_pin setup codec checks p _ raw owner hashed.1.2 hashed.2 result member
      plaintext succeeded fields decodedFields
  all_goals
    simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases succeeded


/-- The hidden hashed challenge finish supplies the same cached transcript receipt and response pin. -/
theorem nativeOwnerFinish_hidden_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((PqxdhDeploymentIdealSteps.hashedOwnerCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge retained raw owner).run
          state)).run slots)) (plaintext : Pqxdh.Bytes) (succeeded : result.1.1.1 = some plaintext) :
    ∃ init fields digest control kernel, retained = some init ∧ responseOf codec raw = some fields ∧
      result.1.2.1.2.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
      result.1.1.2.beacon.phase = .established control (PqxdhTranscriptAd.adOf digest) kernel ∧
      fields.identityKey = absBytes owner.beacon.serverIdentity ∧ fields.WellFormed := by
  obtain ⟨_, _, _, success⟩ := PqxdhDeploymentIdealPostGoodFinish.hashedOwnerCE_footprint setup codec checks p
    retained raw owner state slots result member
  obtain ⟨control, prekey, oneTime, kem, response, kernel, init, fields, digest, _, _, retainedEq, decoded, cached,
    installed⟩ := success plaintext succeeded
  refine ⟨init, fields, digest, ⟨control.expected_server_binding, codec.assignedId response⟩, kernel, retainedEq,
    decoded, cached, ?_, nativeOwnerFinish_hashedCE_pin setup codec checks p retained raw owner state slots result
      member plaintext succeeded fields decoded, (nativeOwnerFinish_response_fields codec raw fields decoded).1⟩
  rw [installed]

/-- A newly established hidden challenge owner necessarily passed the successful pin-checked branch. -/
theorem nativeOwnerFinish_new_hidden_receipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((PqxdhDeploymentIdealSteps.hashedOwnerCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge retained raw owner).run
          state)).run slots)) (control : beaconcrypt_core.pqxdh.BeaconEstablished) (ad : PqxdhTranscriptAd.AssociatedData)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (established : result.1.1.2.beacon.phase = .established control ad kernel)
    (inactive : ¬ RawCtxBeaconLifecycle.Established owner.beacon.phase) :
    ∃ init fields digest, retained = some init ∧ responseOf codec raw = some fields ∧
      result.1.2.1.2.ctx (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf init) fields) = some digest ∧
      ad = PqxdhTranscriptAd.adOf digest ∧ fields.identityKey = absBytes owner.beacon.serverIdentity ∧
      fields.WellFormed := by
  cases reply : result.1.1.1 with
  | none =>
    have failure := (PqxdhDeploymentIdealPostGoodFinish.hashedOwnerCE_footprint setup codec checks p
      retained raw owner state slots result member).2.2.1 reply
    rcases failure with same | ⟨control, _, _, _, _, aborted⟩
    · rw [same] at established
      exact (inactive (by rw [established]; trivial)).elim
    · rw [aborted] at established
      cases established
  | some plaintext =>
    obtain ⟨init, fields, digest, afterControl, afterKernel, retainedEq, decoded, cached, installed, identity, width⟩ :=
      nativeOwnerFinish_hidden_receipt setup codec checks p retained raw owner state slots result member plaintext reply
    have same := RawCtxBeaconLifecycle.Phase.established.inj (established.symm.trans installed)
    exact ⟨init, fields, digest, retainedEq, decoded, cached, same.2.1, identity, width⟩

/-- Every hidden hashed challenge outcome keeps the stored public Server pin. -/
theorem nativeOwnerFinish_hidden_serverIdentity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK × Option Coord)
    (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option Coord)) × PqxdhDeploymentIdealPostSim.SlotState)
    (member : result ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      PqxdhDeploymentSeedSplit.tableService) ((PqxdhDeploymentIdealSteps.hashedOwnerCE setup codec
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge retained raw owner).run
          state)).run slots)):
    result.1.1.2.beacon.serverIdentity = owner.beacon.serverIdentity := by
  obtain ⟨_, _, failure, success⟩ := PqxdhDeploymentIdealPostGoodFinish.hashedOwnerCE_footprint setup codec checks p
    retained raw owner state slots result member
  cases reply : result.1.1.1 with
  | none =>
    rcases failure reply with same | ⟨control, _, _, _, _, aborted⟩
    · rw [same]
    · rw [aborted]
      rfl
  | some plaintext =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, installed⟩ := success plaintext reply
    rw [installed]

end NativeReceipts

section Moves

variable (associatedData : Aeneas.Std.Array Aeneas.Std.U8 151#usize)
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhDeploymentEnvironment (EnvState strip stripOwner coins)
open PqxdhRecordLiftInterface (EnvEffects Capability)

variable {KemSK : Type}

/-- Forwarding the transcript hash and Phase 2 effects preserves the stored public pin on every reply path. -/
theorem ownerFinishFwd_serverIdentity {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} {n : ℕ}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentEnvironment.ownerFinishFwd (n := n) setup codec retained raw owner).run state),
      result.1.2.beacon.serverIdentity = owner.beacon.serverIdentity := by
  intro result member
  unfold PqxdhDeploymentEnvironment.ownerFinishFwd at member
  split at member
  · split at member
    · simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, mem_support_bind_iff] at member
      obtain ⟨digest, _, member⟩ := member
      exact nativeOwnerFinish_native_serverIdentity _ codec.frameRead raw owner result.1
        (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member)
    · exact congrArg (fun value => value.1.2.beacon.serverIdentity) (eq_of_mem_support_pure _ member)
  · exact congrArg (fun value => value.1.2.beacon.serverIdentity) (eq_of_mem_support_pure _ member)

/-! ### Pins and associated data -/


/-- The source commit of a Beacon finish keeps the pinned Server identity, on every staged result. -/
theorem finish_serverIdentity (control : pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.serverIdentity = before.beacon.serverIdentity := by
  rcases staged with _ | value
  · rfl
  · unfold PqxdhBeaconPhase2Publication.finish
    dsimp only
    split_ifs <;> rfl


/-! ### Environment states -/

section Env
variable {Bk : Type} {n : ℕ}

/-- The pins of an environment state: every owner's pinned Server identity, in index order. -/
def pins (e : EnvState KemSK Bk) : List PqxdhBeaconPhase2Preparation.Word32 :=
  e.native.owners.map fun owner => owner.beacon.serverIdentity

/-- The Server identity of an environment state. -/
def serverId (e : EnvState KemSK Bk) : RawCtxServerRouting.Identity := e.native.shared.2.server.server.identity


/-- Stripping keeps every owner's pin. -/
theorem strip_pins (state : PqxdhRegistrationSchedule.State KemSK) :
    (strip state).owners.map (fun owner => owner.beacon.serverIdentity) =
      state.owners.map fun owner => owner.beacon.serverIdentity := by
  simp only [strip, List.map_map]
  congr 1
  funext owner
  show (stripOwner owner).beacon.serverIdentity = owner.beacon.serverIdentity
  unfold stripOwner
  split <;> rfl

/-- Replacing an owner by one with the same pin keeps the pins. -/
theorem pins_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (found : owners[index]? = some before)
    (same : after.beacon.serverIdentity = before.beacon.serverIdentity) :
    (owners.set index after).map (fun owner => owner.beacon.serverIdentity) =
      owners.map fun owner => owner.beacon.serverIdentity := by
  rw [List.map_set, same]
  have below := (List.getElem?_eq_some_iff.mp found).1
  have value := (List.getElem?_eq_some_iff.mp found).2
  apply List.ext_getElem (by simp)
  intro i first second
  by_cases equal : i = index
  · subst equal
    simp [value]
  · simp [Ne.symm equal]

end Env


/-! ### The finish steps -/

section Finish
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Bk : Type} {n : ℕ}

/-- The real finish keeps the Server identity and the pins. -/
theorem finishStep_pin (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.finishStep (n := n) setup codec owner raw).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.finishStep at member
  simp only [StateT.run] at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · rename_i before owned
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨result, resultMember, _, _, rfl⟩ := member
    have game := PqxdhDeploymentEnvironmentReal.ownerFinishFwd_game setup codec (e.native.inits owner) raw before e.native.shared result resultMember
    have pinned := ownerFinishFwd_serverIdentity setup codec (e.native.inits owner) raw before e.native.shared
      result resultMember
    refine ⟨?_, ?_⟩
    · show result.2.2.server.server.identity = e.native.shared.2.server.server.identity
      rw [game]
    · unfold pins
      rw [strip_pins]
      exact pins_set _ owner before _ owned pinned


end Finish


/-! ### Owner k's challenge finish -/

section Challenge
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count n : ℕ}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealEnvFinish (commitEnv groupEnv finishedEnv finishChallengeEnv)

/-- The environment state after a challenge finish keeps the Server identity when the Server's game is kept, and the pins when the owner keeps its pin. -/
theorem finishedEnv_pin (e : EnvState KemSK SplitBk) (owner : ℕ) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (backend : SplitBk) (owned : e.native.owners[owner]? = some before)
    (same : after.beacon.serverIdentity = before.beacon.serverIdentity) (game : shared.2 = e.native.shared.2) :
    serverId (finishedEnv e owner shared after backend) = serverId e ∧
      pins (finishedEnv e owner shared after backend) = pins e := by
  refine ⟨?_, ?_⟩
  · show shared.2.server.server.identity = e.native.shared.2.server.server.identity
    rw [game]
  · unfold pins finishedEnv
    dsimp only
    rw [strip_pins]
    exact pins_set _ owner before after owned same

/-- Every outcome of the source commit is the finished environment state. -/
theorem commitEnv_member (e : EnvState KemSK SplitBk) (owner : ℕ) (control : pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    ∀ v ∈ support (commitEnv e owner control before shared staged),
      v.2 = finishedEnv e owner shared (PqxdhBeaconPhase2Publication.finish control before staged).2 e.backend := by
  intro v member
  unfold commitEnv at member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, _, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  rfl


/-- The private root of a marked finish keeps the Server's game. -/
theorem markedRoot_game (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (secrets : PqxdhRegistrationJointBeaconOpaqueFinish.Secrets) (s : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ r ∈ support ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot (KemSK := KemSK) hmac candidate secrets).run s),
      r.2.2 = s.2 := by
  intro r member
  unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot at member
  split at member
  · simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

/-- Every outcome of the grouped finish request is a finished environment state with the Server's game kept. -/
theorem groupEnv_member (owner : ℕ) (control : pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (e : EnvState KemSK SplitBk) (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    ∀ v ∈ support (groupEnv setup codec owner control before e pending),
      ∃ shared staged backend, shared.2 = e.native.shared.2 ∧
        v.2 = finishedEnv e owner shared (PqxdhBeaconPhase2Publication.finish control before staged).2 backend := by
  intro v member
  unfold groupEnv at member
  split at member
  · split_ifs at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨read, -, member⟩ := member
      split at member
      · rw [support_map] at member
        obtain ⟨committed, committedMember, rfl⟩ := member
        unfold PqxdhDeploymentEnvironment.finishSplitEnv at committedMember
        rw [mem_support_bind_iff] at committedMember
        obtain ⟨staged, -, committedMember⟩ := committedMember
        rw [mem_support_bind_iff] at committedMember
        obtain ⟨_, -, committedMember⟩ := committedMember
        rw [support_pure, Set.mem_singleton_iff] at committedMember
        subst committedMember
        exact ⟨e.native.shared, staged, _, rfl, rfl⟩
      · exact ⟨e.native.shared, none, e.backend, rfl, commitEnv_member e owner control before _ none v member⟩
    · exact ⟨e.native.shared, none, e.backend, rfl, commitEnv_member e owner control before _ none v member⟩
  · rw [mem_support_bind_iff] at member
    obtain ⟨r, rMember, member⟩ := member
    have game := markedRoot_game setup.hmac _ pending.root e.native.shared r
      (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember)
    split at member
    · exact ⟨r.2, none, e.backend, game, commitEnv_member e owner control before _ none v member⟩
    · rw [mem_support_bind_iff] at member
      obtain ⟨staged, -, member⟩ := member
      exact ⟨r.2, staged, e.backend, game, commitEnv_member e owner control before _ staged v member⟩


/-- Owner k's challenge finish keeps the Server identity and the pins. -/
theorem finishChallengeEnv_pin (p : PqxdhDeploymentIdealParams.Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((finishChallengeEnv setup codec p owner raw).run e), serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  change v ∈ support (finishChallengeEnv setup codec p owner raw e) at member
  unfold finishChallengeEnv at member
  split at member
  · rename_i before owned
    split at member
    · rename_i control prekey oneTime kem phase
      split at member
      · rw [mem_support_bind_iff] at member
        obtain ⟨digest, _, member⟩ := member
        rw [mem_support_bind_iff] at member
        obtain ⟨prepared, -, member⟩ := member
        split at member
        · rw [commitEnv_member e owner control before _ none v member]
          exact finishedEnv_pin e owner _ before _ _ owned (finish_serverIdentity control before none) rfl
        · rename_i pending
          obtain ⟨shared, staged, backend, game, same⟩ := groupEnv_member setup codec owner control before e pending v member
          rw [same]
          exact finishedEnv_pin e owner shared before _ backend owned (finish_serverIdentity control before staged) game
      · simpa only [commitEnv_member e owner control before _ none v member] using
          finishedEnv_pin e owner _ before _ _ owned (finish_serverIdentity control before none) rfl
    · simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩


end Challenge


/-! ### The other registration steps -/

section Steps
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {Bk : Type} {n : ℕ}


/-- A bundle publication preserves its owner's pin. -/
theorem bundled_serverIdentity (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (shape : PqxdhDeploymentEnvironmentReal.Bundled before after) :
    after.beacon.serverIdentity = before.beacon.serverIdentity := by
  rcases shape with rfl | ⟨⟨control, prekey, oneTime, kem, rfl⟩, _⟩ <;> rfl

/-- The real bundle keeps the Server identity and the pins. -/
theorem bundleStep_pin (owner : ℕ) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.bundleStep (n := n) setup codec owner).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.bundleStep at member
  simp only [StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨r, rMember, _, _, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.bundle setup codec owner).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  cases owned : e.native.owners[owner]? with
  | none =>
      rw [PqxdhDeploymentEnvironmentReal.bundle_run_missing setup codec owner _ owned, support_pure,
        Set.mem_singleton_iff] at inner
      subst inner
      exact ⟨rfl, by unfold pins; exact strip_pins _⟩
  | some current =>
      rw [PqxdhDeploymentEnvironmentReal.bundle_run_found setup codec owner _ current owned, support_map] at inner
      obtain ⟨b, bMember, rfl⟩ := inner
      have shape := PqxdhDeploymentEnvironmentReal.bundle_shape _ current b.1
        (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ bMember)
      refine ⟨rfl, ?_⟩
      unfold pins
      rw [strip_pins]
      exact pins_set _ owner current b.1.2 owned (bundled_serverIdentity current b.1.2 shape)


/-- The native logged accept keeps the Server's peer map, identity and metadata. -/
theorem acceptLogged_server (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes)
    (shared : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ result ∈ support ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run shared),
      result.2.2.server.server = shared.2.server.server := by
  intro result supported
  have native : ((result.1.1, result.2) : Option ℕ × PqxdhServerAuthNative.NativeState KemSK) ∈ support
      ((PqxdhServerAuthNative.nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run
        shared) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨result, supported, rfl⟩
  rw [← PqxdhServerAuthNative.accept_native] at native
  have inner := PqxdhServerAuthNative.evaluate_support setup seed _ _ shared _ native
  exact (PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw shared.2 _ inner).1

/-- The real accept keeps the Server identity and the pins and issues no inadmissible request. -/
theorem acceptStep_pin (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.acceptStep (n := n) setup codec checks raw).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.acceptStep at member
  simp only [StateT.run, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup
      codec checks e.created.seed raw)).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  refine ⟨?_, by unfold pins; exact strip_pins _⟩
  show x.2.2.server.server.identity = e.native.shared.2.server.server.identity
  rw [acceptLogged_server setup codec checks e.created.seed raw e.native.shared x xMember]


/-- The real public HMAC keeps the Server identity and the pins. -/
theorem hmacStep_pin (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.hmacStep (n := n) setup key message).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv at member
  simp only [StateT.run, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup e.created.seed
      PqxdhRegistrationSchedule.observationScalar key message)).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  rw [← PqxdhServerAuthNative.hmac_native] at xMember
  have evaluated := PqxdhServerAuthNative.evaluate_support setup e.created.seed _ _ e.native.shared x xMember
  have fixed := PqxdhDeploymentCompileFootprint.hmac_fixed key message e.native.shared.2 _ evaluated
  refine ⟨?_, by unfold pins; exact strip_pins _⟩
  show x.2.2.server.server.identity = e.native.shared.2.server.server.identity
  rw [fixed.1]


end Steps


/-! ### The pool create and the selected accept -/

section Ideal
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ} {Bk : Type} {n : ℕ}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealSlots (SlotSpec Coord)

/-- The pool create keeps the Server identity; it either returns nothing and keeps the pins, or parses the pin and appends it to the pins. -/
theorem createPoolStep_pin (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := n) setup pool pin keyId).run e),
      serverId v.2 = serverId e ∧ ((v.1 = none ∧ pins v.2 = pins e) ∨
        ∃ word index, PqxdhDeploymentInterface.parsePin pin = some word ∧ v.1 = some index ∧
          pins v.2 = pins e ++ [word]) := by
  intro v member
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rename_i word parsed
    rw [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨r, rMember, member⟩ := member
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    simp only [PqxdhDeploymentEnvironment.onEnv, StateT.run, support_map, Set.mem_image] at rMember
    obtain ⟨x, xMember, rfl⟩ := rMember
    have inner : x ∈ support ((PqxdhDeploymentIdealSteps.createPool setup pool word keyId).run e.native) :=
      PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ xMember
    rw [PqxdhDeploymentIdealEnvReal.createPool_run setup pool word keyId e.native] at inner
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
    obtain ⟨_, _, _, _, _, _, rfl⟩ := inner
    refine ⟨rfl, Or.inr ⟨word, _, parsed, rfl, ?_⟩⟩
    unfold pins
    dsimp only
    rw [strip_pins]
    simp


/-- A marker-tail request other than an install of a game with another Server identity. -/
def TailKeeps (identity : RawCtxServerRouting.Identity) :
    (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → Prop
  | .inr (.install game) => game.server.server.identity = identity
  | _ => True

open Classical in
/-- A marker-tail request that installs a game with another Server identity, as a Boolean. -/
noncomputable def tailBad (identity : RawCtxServerRouting.Identity)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) : Bool :=
  decide (¬ TailKeeps identity query)

open Classical in
/-- A tail request is bad exactly when it installs a game with another Server identity. -/
theorem tailBad_iff (identity : RawCtxServerRouting.Identity)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) :
    tailBad identity query = true ↔ ¬ TailKeeps identity query := by
  unfold tailBad
  exact decide_eq_true_iff

/-- Every step of the marker tail at an admissible request keeps the Server identity of the native state. -/
theorem tailCE_keeps (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (identity : RawCtxServerRouting.Identity)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain)
    (z : PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)) (good : ¬ tailBad identity query = true)
    (holds : z.1.2.server.server.identity = identity) :
    ∀ r ∈ support ((PqxdhDeploymentIdealSteps.tailCE hmac index query).run z),
      r.2.1.2.server.server.identity = identity := by
  obtain ⟨s, mark⟩ := z
  intro r member
  rcases query with (input | aux) | mutation
  · cases shared : input.shared with
    | challenge =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared] at member
        rw [mem_support_bind_iff] at member
        obtain ⟨_, _, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact holds
    | known secret =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared] at member
        rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
        obtain ⟨x, xMember, rfl⟩ := member
        change x ∈ support ((PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index (List.Vector.replicate 32 0)
          input).run s) at xMember
        simp only [PqxdhRegistrationJointKemOpaqueClient.romRoot, PqxdhServerAuthNative.nativeTouch, StateT.run_bind,
          StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at xMember
        obtain ⟨root, rootMember, _, touched, rfl⟩ := xMember
        unfold PqxdhServerAuthNative.romRootBytes at rootMember
        simp only [StateT.run, support_map, Set.mem_image] at rootMember
        obtain ⟨_, _, rfl⟩ := rootMember
        simp only [PqxdhServerAuthNative.localState, StateT.run, support_pure, Set.mem_singleton_iff] at touched
        subst touched
        exact holds
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run] at member
    rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
    obtain ⟨x, xMember, rfl⟩ := member
    cases aux <;>
      simp [PqxdhRegistrationJointKemOpaqueClient.auxiliary, PqxdhServerAuthNative.nativeConsume,
        PqxdhServerAuthNative.localState] at xMember <;>
      subst xMember <;> exact holds
  · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run] at member
    rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
    obtain ⟨x, xMember, rfl⟩ := member
    cases mutation with
    | install game =>
        simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeSet,
          PqxdhServerAuthNative.localState] at xMember
        subst xMember
        by_contra differ
        exact good ((tailBad_iff _ _).2 differ)
    | publish at_ token =>
        simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeModify,
          PqxdhServerAuthNative.localState] at xMember
        subst xMember
        exact holds

/-- The marker tail on a game installs only games with that game's Server identity. -/
theorem tail_keeps (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected).IsQueryBoundP
      (fun query => tailBad state.server.server.identity query = true) 0 := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [tailBad, TailKeeps]), fun _ => ?_⟩
  simp only [tailBad, TailKeeps, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  split
  · trivial
  · rw [show (0 : ℕ) = 0 + 0 from rfl]
    refine isQueryBoundP_bind (IsQueryBoundP.simulateQ_of_step (p := fun _ => False)
      (isQueryBoundP_false _ _) (fun _ wrong => absurd wrong id) (fun query _ => ?_)) fun returned _ => ?_
    · exact (isQueryBoundP_query_iff _ _ _).2 (fun bad => by simp at bad)
    · split
      · rw [isQueryBoundP_query_bind_iff]
        exact ⟨Or.inl (by simp), fun _ => trivial⟩
      · trivial

/-- The selected accept with its encapsulation exposed keeps the Server identity, for any slot replies. -/
theorem acceptExposed_server (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (shared : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ r ∈ support ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw).run shared),
      r.2.2.server.server.identity = shared.2.server.server.identity := by
  have inactive : ∀ r ∈ support ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw).run shared),
      r.2.2.server.server.identity = shared.2.server.server.identity := by
    intro r member
    change r ∈ support ((fun r : (Option ℕ × Option PqxdhJointGapDh.ScalarBytes) ×
      PqxdhServerAuthNative.NativeState KemSK => ((r.1, (false, none)), r.2)) <$>
      PqxdhDeploymentIdealSteps.liftS ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
        raw).run shared)) at member
    rw [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp] at member
    obtain ⟨x, xMember, rfl⟩ := member
    rw [acceptLogged_server setup codec checks seed raw shared x xMember]
  intro r member
  unfold PqxdhDeploymentIdealSteps.acceptExposed at member
  split at member
  · split_ifs at member
    · rename_i verified _ _
      change r ∈ support (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified shared) at member
      unfold PqxdhDeploymentIdealSteps.acceptActive at member
      rw [mem_support_bind_iff] at member
      obtain ⟨pre, -, member⟩ := member
      split at member
      · rw [mem_support_bind_iff] at member
        obtain ⟨x, xMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at xMember
        simp [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run] at xMember
        subst xMember
        rfl
      · rw [mem_support_bind_iff] at member
        obtain ⟨prepared, -, member⟩ := member
        rw [mem_support_bind_iff] at member
        obtain ⟨answer, answerMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact PqxdhDeploymentIdealEnvFacts.run_keepsGood (PqxdhDeploymentIdealSteps.tailCE setup.hmac shared.2.sessions)
          (fun query => tailBad shared.2.server.server.identity query = true)
          (fun z => z.1.2.server.server.identity = shared.2.server.server.identity)
          (fun query z good holds result resultMember =>
            tailCE_keeps setup.hmac shared.2.sessions _ query z good holds result resultMember)
          _ (tail_keeps _ _ shared.2 _) (shared, none) rfl answer answerMember
    · exact inactive r member
  · exact inactive r member

/-- The selected accept keeps the Server identity and the pins and issues no inadmissible request. -/
theorem acceptSelectedEnv_pin (p : PqxdhDeploymentIdealParams.Params KemSK count) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e := by
  intro v member
  change v ∈ support ((fun r => (r.1.1.1.1, PqxdhDeploymentIdealEnvStep.acceptedEnv e r)) <$> coins (n := 2)
    ((PqxdhDeploymentIdealEnvStep.acceptGame setup codec checks p e.created.seed raw
      (e.backend.2.1, (e.backend.1, ∅))).run e.native.shared)) at member
  rw [support_map] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
      (PqxdhDeploymentIdealKernel.lazyDummy (n := 2)))
      ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks e.created.seed p.chosen p.challenge raw).run
        e.native.shared)).run (e.backend.2.1, (e.backend.1, ∅))) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  have kept := acceptExposed_server setup codec checks e.created.seed p.chosen p.challenge raw e.native.shared x.1
    (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ xMember)
  refine ⟨kept, ?_⟩
  unfold pins PqxdhDeploymentIdealEnvStep.acceptedEnv
  exact strip_pins _


end Ideal


/-! ### Build responses -/

section Wrote
variable {Reader Response : Type} (codec : Codec Reader Response)

/-- A build result that published a response carries the Phase 2 writer output of fields with the given Server identity. -/
def Wrote {S : Type} (identity : RawCtxServerRouting.Identity) :
    RustM (Option PqxdhServerRegistrationPublication.Response × S) → Prop
  | .ok (some response, _) => ∃ fields, codec.write2 fields = some response.serialized ∧ fields.identity = identity
  | _ => True

/-- A published result with its state mapped writes the same response. -/
theorem wrote_map {S T : Type} (identity : RawCtxServerRouting.Identity) (f : S → T)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × S)) (wrote : Wrote codec identity result) :
    Wrote codec identity (Functor.map (Prod.map id f) result) := by
  rcases result with ⟨_ | response, after⟩ | error | _
  · trivial
  · exact wrote
  · trivial
  · trivial

section Native
variable {Metadata PeerMetadata Consumed σ ι' : Type} {base : OracleSpec ι'}
open PqxdhServerRegistrationPublication (TailSpec State build candidateTail afterInitialization responseFields)

/-- A registration tail whose Phase 2 writer callback answers every request with the codec's writer. -/
def WriteDet (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) : Prop :=
  ∀ fields state, ∀ result ∈ support ((impl (.inr (.write fields))).run state), result.1 = codec.write2 fields

/-- The first send and Phase 2 writing under a deterministic writer: a published response is the writer output of the candidate's response fields. -/
theorem after_wrote (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) (det : WriteDet codec impl)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : ConcreteRatchetKernel) (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : σ) :
    ∀ result ∈ support ((simulateQ impl (afterInitialization associatedData candidate authenticated kernel metadata state)).run primitive),
      Wrote codec candidate.server_identity_public_key (.ok result.1) := by
  intro result supported
  obtain ⟨sent, afterSend, afterErase, _, _, rest⟩ :=
    PqxdhServerRegistrationPublication.afterInitialization_support (associatedData := associatedData) impl candidate authenticated kernel metadata state
      primitive result supported
  cases hs : sent.2 with
  | none =>
      rw [hs] at rest
      rw [rest]
      trivial
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written, afterWrite, writtenMember, same⟩ := rest
      rw [same]
      have value := det _ _ _ writtenMember
      cases written with
      | none => trivial
      | some bytes => exact ⟨responseFields candidate encrypted, value.symm, rfl⟩

/-- The candidate tail under a deterministic writer: a published response is the writer output of fields carrying the candidate's Server identity. -/
theorem candidate_wrote (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) (det : WriteDet codec impl)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (candidate : pqxdh.ServerRegistrationCandidate)
    (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : σ) :
    ∀ result ∈ support ((simulateQ impl (candidateTail (associatedData := associatedData) source candidate root payload metadata state)).run primitive),
      Wrote codec candidate.server_identity_public_key result.1 := by
  intro result supported
  obtain ⟨kernel, hrun, _, _, _⟩ := PqxdhRootTableInitialization.initialize_refines source
    PqxdhServerAuthExperiment.unitRatchet false root
  have hinit := (PqxdhServerRegistrationPublication.candidate_initialization source candidate root).trans hrun
  obtain ⟨binding, hbinding, _⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
  simp only [candidateTail, hinit, hbinding, PqxdhServerRegistrationPublication.continueRust, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨valid, afterIdentity⟩, _, supported⟩ := supported
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    rw [supported]
    trivial
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
  cases reserved
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    rw [supported]
    trivial
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at supported
  split_ifs at supported with empty fits
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    trivial
  · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨allocated, afterAllocate⟩, _, supported⟩ := supported
    cases allocated
    · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      rw [supported]
      trivial
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
      support_map, Set.mem_image] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact after_wrote (associatedData := associatedData) codec impl det candidate _ kernel metadata state afterAllocate inner reached
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    trivial

/-- The native Server build under a deterministic writer: a published response is the writer output of fields carrying the Server's identity. -/
theorem build_wrote (impl : QueryImpl TailSpec (StateT σ (OracleComp base))) (det : WriteDet codec impl)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : State Metadata PeerMetadata Consumed) (primitive : σ) :
    ∀ result ∈ support ((simulateQ impl (build (associatedData := associatedData) source pending root payload metadata state)).run primitive),
      Wrote codec state.server.identity result.1 := by
  intro result supported
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, PqxdhServerRegistrationPublication.continueRust] at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      trivial
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then .Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          rw [supported]
          trivial
      | Ok candidate =>
          have identity := (PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate hprepared).2.1
          have wrote := candidate_wrote (associatedData := associatedData) codec impl det source candidate root payload metadata state primitive result
            supported
          rw [identity] at wrote
          exact wrote

end Native

section Generic
variable {Kernel Metadata PeerMetadata Consumed ι' : Type} {spec' : OracleSpec ι'}
open PqxdhInitialGenericPublication (State)

/-- A Phase 2 writer callback that answers every request with the codec's writer. -/
def AuxWriteDet (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) : Prop :=
  ∀ fields, ∀ x ∈ support (aux (.write fields)), x = codec.write2 fields

/-- The generic first send and Phase 2 writing under a deterministic writer, for any other replies. -/
theorem afterInitializationG_wrote (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) (det : AuxWriteDet codec aux)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhInitialGenericPublication.afterInitialization (associatedData := associatedData) calls aux candidate authenticated kernel
      metadata state), Wrote codec candidate.server_identity_public_key (.ok result) := by
  intro result supported
  unfold PqxdhInitialGenericPublication.afterInitialization at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨advanced, encrypted⟩, _, member⟩ := supported
  rw [mem_support_bind_iff] at member
  obtain ⟨_, _, member⟩ := member
  cases encrypted with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      trivial
  | some encrypted =>
      dsimp only at member
      rw [mem_support_bind_iff] at member
      obtain ⟨serialized, serializedMember, member⟩ := member
      cases serialized with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          trivial
      | some serialized =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨_, (det _ _ serializedMember).symm, rfl⟩

/-- A written response of every continuation of the actual Rust value is a written response of the continued result. -/
theorem continueRust_wrote {α : Type} (value : RustM α)
    (next : α → OracleComp spec' (RustM (Option PqxdhServerRegistrationPublication.Response × State Kernel Metadata
      PeerMetadata Consumed))) (identity : RawCtxServerRouting.Identity)
    (continued : ∀ inner, value = ok inner → ∀ result ∈ support (next inner), Wrote codec identity result) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.continueRust value next), Wrote codec identity result := by
  intro result supported
  cases value with
  | ok inner => exact continued inner rfl result supported
  | fail error =>
      simp only [PqxdhInitialGenericBuilder.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial
  | div =>
      simp only [PqxdhInitialGenericBuilder.continueRust, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial

/-- The generic candidate admission and first send under a deterministic writer, for any other replies. -/
theorem candidateG_wrote (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) (det : AuxWriteDet codec aux)
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.candidate (associatedData := associatedData) calls aux initial candidate data metadata state),
      Wrote codec candidate.server_identity_public_key result := by
  intro result supported
  unfold PqxdhInitialGenericBuilder.candidate at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨valid, _, member⟩ := supported
  by_cases invalid : (!valid) = true
  · simp only [invalid, ite_true, support_pure, Set.mem_singleton_iff] at member
    subst member
    trivial
  · simp only [invalid, Bool.false_eq_true, ite_false, mem_support_bind_iff] at member
    obtain ⟨reserved, _, member⟩ := member
    by_cases unreserved : (!reserved) = true
    · simp only [unreserved, ite_true, support_pure, Set.mem_singleton_iff] at member
      subst member
      trivial
    · simp only [unreserved, Bool.false_eq_true, ite_false] at member
      refine continueRust_wrote codec _ _ _ (fun kernel _ inner innerMember => ?_) result member
      split_ifs at innerMember with empty bounded
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        trivial
      · rw [mem_support_bind_iff] at innerMember
        obtain ⟨allocated, _, innerMember⟩ := innerMember
        by_cases unallocated : (!allocated) = true
        · simp only [unallocated, ite_true, support_pure, Set.mem_singleton_iff] at innerMember
          subst innerMember
          trivial
        · simp only [unallocated, Bool.false_eq_true, ite_false] at innerMember
          refine continueRust_wrote codec _ _ _ (fun binding _ final finalMember => ?_) inner innerMember
          rw [support_map] at finalMember
          obtain ⟨published, publishedMember, rfl⟩ := finalMember
          exact afterInitializationG_wrote (associatedData := associatedData) codec calls aux det candidate _ _ metadata state published publishedMember
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        trivial

/-- The generic Server build under a deterministic writer: a published response is the writer output of fields carrying the Server's identity, for any other replies. -/
theorem genericBuild_wrote (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec'))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp spec')) (det : AuxWriteDet codec aux)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhServerAuthSendFactor.genericBuild (associatedData := associatedData) calls aux initial pending data metadata state),
      Wrote codec state.server.identity result := by
  intro result supported
  unfold PqxdhServerAuthSendFactor.genericBuild at supported
  refine continueRust_wrote codec _ _ _ (fun next _ inner innerMember => ?_) result supported
  rcases next with key | error
  · dsimp only at innerMember
    refine continueRust_wrote codec _ _ _ (fun prepared preparedEq final finalMember => ?_) inner innerMember
    rcases prepared with candidate | error
    · have identity := (PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate preparedEq).2.1
      have wrote := candidateG_wrote (associatedData := associatedData) codec calls aux det initial candidate data metadata state final finalMember
      rw [identity] at wrote
      exact wrote
    · simp only [support_pure, Set.mem_singleton_iff] at finalMember
      subst finalMember
      trivial
  · simp only [support_pure, Set.mem_singleton_iff] at innerMember
    subst innerMember
    trivial

end Generic

end Wrote


/-! ### The build steps -/

section BuildSteps
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {Bk : Type} {n : ℕ}
open PqxdhServerRegistrationPublication (TailSpec)

/-- The registration tail with its Phase 2 writer answered by the codec's writer and every other request forwarded. -/
def writeImpl : QueryImpl TailSpec (OracleComp TailSpec)
  | .inl query => liftM (TailSpec.query (.inl query))
  | .inr (.write fields) => pure (codec.write2 fields)
  | .inr query => liftM (TailSpec.query (.inr query))

/-- The forwarded native registration tail answers its Phase 2 writer as `writeImpl` does. -/
theorem nativeTailFwd_writeImpl :
    (PqxdhDeploymentEnvironment.nativeTailFwd (n := n) setup codec checks) ∘ₛ writeImpl codec =
      PqxdhDeploymentEnvironment.nativeTailFwd setup codec checks := by
  funext query
  rcases query with query | query
  · simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]
  · cases query with
    | write fields =>
        simp only [QueryImpl.apply_compose, writeImpl, simulateQ_pure]
        rfl
    | _ => simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]

/-- The forwarded registration tail answers its Phase 2 writer with the codec's writer. -/
theorem tailFwd_det : WriteDet codec (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec checks) := by
  intro fields state result member
  have same : (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec checks (.inr (.write fields))).run state =
      pure (codec.write2 fields, state) := rfl
  rw [same, support_pure, Set.mem_singleton_iff] at member
  rw [member]

/-- The free factored build with the Phase 2 writer answered by the codec's writer: a published response is the writer output of fields carrying the Server's identity, for any other replies. -/
theorem freeBuild_wrote (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (value : PqxdhServerAuthSendFactor.Factor) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ result ∈ support (simulateQ (writeImpl codec) (PqxdhDeploymentSplitFactor.freeBuild (associatedData := associatedData) source value pending data
      server)), Wrote codec server.server.identity result := by
  intro result supported
  rw [← PqxdhDeploymentSplitFactor.factored_free (associatedData := associatedData) (writeImpl codec)] at supported
  unfold PqxdhServerAuthLoggedSendFactor.factored at supported
  rw [support_map] at supported
  obtain ⟨g, gMember, rfl⟩ := supported
  exact wrote_map codec _ _ g (genericBuild_wrote (associatedData := associatedData) codec _ _ (fun fields x member => by
    simpa only [writeImpl, support_pure, Set.mem_singleton_iff] using member) _ _ _ _ _ g gMember)

/-- A build reply that is a response carries the Phase 2 writer output of fields with the Server identity. -/
def ReplyWrote (identity : RawCtxServerRouting.Identity)
    (reply : Option PqxdhServerRegistrationPublication.Response) : Prop :=
  ∀ response, reply = some response →
    ∃ fields, codec.write2 fields = some response.serialized ∧ fields.identity = identity

/-- Settling a build result that keeps the Server identity and writes its response keeps both. -/
theorem settle_wrote (server : PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes)))
    (kept : ∀ value, result = ok value → value.2.server.identity = server.server.identity)
    (wrote : Wrote codec server.server.identity result) :
    (PqxdhServerAuthExperiment.settle server result).2.server.identity = server.server.identity ∧
      ReplyWrote codec server.server.identity (PqxdhServerAuthExperiment.settle server result).1 := by
  rcases result with ⟨_ | response, after⟩ | error | _
  · exact ⟨kept _ rfl, fun _ found => by cases found⟩
  · refine ⟨kept _ rfl, fun other found => ?_⟩
    simp only [PqxdhServerAuthExperiment.settle, Option.some.injEq] at found
    subst found
    exact wrote
  · exact ⟨rfl, fun _ found => by cases found⟩
  · exact ⟨rfl, fun _ found => by cases found⟩

/-- The real build keeps the Server identity and the pins, and a reply carries the Phase 2 writer output of fields with the Server identity. -/
theorem buildStep_pin (session : ℕ) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := n) setup codec checks session payload).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e ∧ ReplyWrote codec (serverId e) v.1 := by
  intro v member
  unfold PqxdhDeploymentEnvironment.buildStep at member
  simp only [StateT.run] at member
  split at member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl, fun _ found => by cases found⟩
  · rename_i token _
    split at member
    · obtain rfl := eq_of_mem_support_pure _ member
      exact ⟨rfl, by unfold pins; exact strip_pins _, fun _ found => by cases found⟩
    · rw [mem_support_bind_iff] at member
      obtain ⟨digest, _, member⟩ := member
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨result, resultMember, _, _, rfl⟩ := member
      have wrote := build_wrote (associatedData := PqxdhTranscriptAd.adOf digest) codec _ (tailFwd_det setup codec checks) setup.source token.pending token.root payload (PqxdhTranscriptAd.adOf digest)
        e.native.shared.2.server [] result resultMember
      have kept : ∀ value, result.1 = ok value → value.2.server.identity = e.native.shared.2.server.server.identity := by
        intro value found
        rcases PqxdhRegistrationResponse.build_publication (associatedData := PqxdhTranscriptAd.adOf digest) _ setup.source token.pending token.root payload (PqxdhTranscriptAd.adOf digest)
            e.native.shared.2.server [] result resultMember with same | ⟨_, candidate, kernel, bytes, _, _, same⟩
        · rw [same] at found
          cases found
          rfl
        · rw [same] at found
          cases found
          rfl
      obtain ⟨identity, replied⟩ := settle_wrote codec _ _ kept wrote
      exact ⟨identity, by unfold pins; exact strip_pins _, replied⟩

/-- The forwarded split build keeps the Server identity and writes its response, for any other replies. -/
theorem buildSplitFwd_wrote (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ p ∈ support ((PqxdhDeploymentEnvironment.buildSplitFwd (n := n) setup codec checks material token payload associatedData
      server).run []),
      (∀ value, p.1 = ok value → value.2.server.identity = server.server.identity) ∧
        Wrote codec server.server.identity p.1 := by
  intro p member
  rw [PqxdhDeploymentSplitFactor.buildSplitFwd_free, StateT.run_map, support_map] at member
  obtain ⟨y, yMember, rfl⟩ := member
  have free := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ yMember
  have built := PqxdhDeploymentIdealEnvBuild.freeBuild_shape (associatedData := associatedData) _ _ _ _ _ y.1 free
  have forwarded : y.1 ∈ support (simulateQ (PqxdhDeploymentEnvironment.nativeTailFwd (n := n) setup codec checks)
      (PqxdhDeploymentSplitFactor.freeBuild (associatedData := associatedData) setup.source (PqxdhServerAuthCtxMaterial.factor
        (PqxdhDeploymentHiddenLayout.joinOutput material PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload
        server)) := by
    rw [← PqxdhDeploymentEnvironment.tailFwd_forget setup codec checks _ [], support_map]
    exact ⟨y, yMember, rfl⟩
  rw [← nativeTailFwd_writeImpl setup codec checks, QueryImpl.simulateQ_compose] at forwarded
  have wrote := freeBuild_wrote (associatedData := associatedData) codec _ _ _ _ server y.1
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ forwarded)
  dsimp only
  rcases hy : y.1 with ⟨_ | response, after⟩ | error | _
  · rw [hy] at built
    refine ⟨fun value found => ?_, trivial⟩
    change ok (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel (none, after)) =
      ok value at found
    cases found
    change after.server.identity = server.server.identity
    rw [built]
  · rw [hy] at built wrote
    obtain ⟨candidate, kernel, _, _, published⟩ := built
    refine ⟨fun value found => ?_, wrote⟩
    change ok (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel
      (some response, after)) = ok value at found
    cases found
    rw [published]
    rfl
  · exact ⟨fun value found => (by cases found), trivial⟩
  · exact ⟨fun value found => (by cases found), trivial⟩

open PqxdhDeploymentIdealSteps (SplitBk) in
/-- The marked build keeps the Server identity and the pins, and a reply carries the Phase 2 writer output of fields with the Server identity. -/
theorem buildCachedEnv_pin (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e),
      serverId v.2 = serverId e ∧ pins v.2 = pins e ∧ ReplyWrote codec (serverId e) v.1 := by
  intro v member
  change v ∈ support (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords e) at member
  unfold PqxdhDeploymentIdealEnv.buildCachedEnv at member
  split at member
  · split at member
    · rename_i j token _ _ _ material _
      split at member
      · obtain rfl := eq_of_mem_support_pure _ member
        exact ⟨rfl, by unfold pins; exact strip_pins _, fun _ found => by cases found⟩
      · rw [mem_support_bind_iff] at member
        obtain ⟨digest, _, member⟩ := member
        rw [mem_support_bind_iff] at member
        obtain ⟨result, resultMember, member⟩ := member
        rw [support_pure, Set.mem_singleton_iff] at member
        subst member
        unfold PqxdhDeploymentEnvironment.buildSplitEnv at resultMember
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at resultMember
        obtain ⟨p, pMember, _, _, rfl⟩ := resultMember
        obtain ⟨kept, wrote⟩ := buildSplitFwd_wrote (associatedData := PqxdhTranscriptAd.adOf digest) setup codec checks material token payload e.native.shared.2.server p
          pMember
        obtain ⟨identity, replied⟩ := settle_wrote codec _ _ kept wrote
        exact ⟨identity, by unfold pins; exact strip_pins _, replied⟩
    · simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, fun _ found => by cases found⟩
  · simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl, fun _ found => by cases found⟩


end BuildSteps


/-! ### The ideal environment step -/

section Combined
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ} {Bk : Type}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentInterface (Command CommandSpec)

/-- An environment step's move with its command and reply: the Server identity is kept, the pins follow the public summary's owner update for the command and its reply, and the entry is shaped as a build of the Server identity. -/
def PinMove (command : Command) (reply : CommandSpec command) (e e' : EnvState KemSK Bk) : Prop :=
  serverId e' = serverId e ∧
    (∀ summary : PqxdhDeploymentTranscript.Summary, summary.owners.map Prod.fst = pins e →
      (PqxdhDeploymentTranscript.stepCommand summary command reply).owners.map Prod.fst = pins e') ∧
    PqxdhDeploymentEligibility.BuildShaped codec (serverId e) ⟨.inl (.inr command), reply⟩

/-- A command other than create leaves the summary's owners unchanged. -/
theorem stepCommand_owners (summary : PqxdhDeploymentTranscript.Summary) (command : Command)
    (reply : CommandSpec command) (notCreate : ∀ pin keyId, command ≠ .create pin keyId) :
    (PqxdhDeploymentTranscript.stepCommand summary command reply).owners = summary.owners := by
  cases command with
  | create pin keyId => exact absurd rfl (notCreate pin keyId)
  | bundle owner =>
      cases reply <;> simp only [PqxdhDeploymentTranscript.stepCommand] <;> split_ifs <;> rfl
  | finish owner raw =>
      cases reply <;> simp only [PqxdhDeploymentTranscript.stepCommand] <;> split_ifs <;> rfl
  | _ => rfl

/-- A move of a command other than create and build: the Server identity and the pins are kept. -/
theorem pinMove_quiet (command : Command) (reply : CommandSpec command) (e e' : EnvState KemSK Bk)
    (notCreate : ∀ pin keyId, command ≠ .create pin keyId)
    (notBuild : ∀ session payload, command ≠ .build session payload)
    (identity : serverId e' = serverId e) (same : pins e' = pins e) : PinMove codec command reply e e' := by
  refine ⟨identity, fun summary agree => ?_, ?_⟩
  · rw [stepCommand_owners summary command reply notCreate, agree, same]
  · cases command with
    | build session payload => exact absurd rfl (notBuild session payload)
    | _ => trivial

/-- A build move: the Server identity and the pins are kept and a response is written with the Server identity. -/
theorem pinMove_build (session : ℕ) (payload : Option Pqxdh.Bytes)
    (reply : Option PqxdhServerRegistrationPublication.Response) (e e' : EnvState KemSK Bk)
    (identity : serverId e' = serverId e) (same : pins e' = pins e) (wrote : ReplyWrote codec (serverId e) reply) :
    PinMove codec (.build session payload) reply e e' := by
  refine ⟨identity, fun summary agree => ?_, ?_⟩
  · rw [stepCommand_owners summary (Command.build session payload) reply (fun _ _ wrong => by cases wrong), agree, same]
  · rcases reply with _ | response
    · simp [PqxdhDeploymentEligibility.BuildShaped]
    · exact wrote response rfl

/-- Every outcome of the ideal environment step moves the state with its command and reply. -/
theorem idealStep_move (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e),
      PinMove codec query.val v.1 e v.2 := by
  intro v member
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      change v ∈ support ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup (p.pool t) pin keyId).run e)
        at member
      obtain ⟨identity, (⟨noReply, same⟩ | ⟨word, index, parsed, replied, appended⟩)⟩ :=
        createPoolStep_pin setup (p.pool t) pin keyId e v member
      · refine ⟨identity, fun summary agree => ?_, trivial⟩
        rw [show v.1 = Option.none from noReply]
        simp only [PqxdhDeploymentTranscript.stepCommand]
        rw [agree, same]
      · refine ⟨identity, fun summary agree => ?_, trivial⟩
        rw [replied]
        simp only [PqxdhDeploymentTranscript.stepCommand, parsed, List.map_append, List.map_cons, List.map_nil]
        rw [agree, appended]
  | bundle owner =>
      change v ∈ support ((PqxdhDeploymentEnvironment.bundleStep (n := 2) setup codec owner).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      obtain ⟨identity, same⟩ := bundleStep_pin setup codec owner _ v member
      exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) identity
        same
  | accept raw =>
      change v ∈ support (if e.backend.2.2.accepts = t.accept then _ else _) at member
      split at member
      · obtain ⟨identity, same⟩ := acceptSelectedEnv_pin setup codec checks p raw e v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
      · change v ∈ support ((PqxdhDeploymentEnvironment.acceptStep (n := 2) setup codec checks raw).run
          (PqxdhDeploymentEnvironment.snapped _ _)) at member
        obtain ⟨identity, same⟩ := acceptStep_pin setup codec checks raw _ v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
  | build session payload =>
      change v ∈ support (match e.backend.2.2.marks with
        | some (index, coords) => if index = session ∧ (e.native.shared.2.pending session).isSome then
            (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
        | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e)
        at member
      split at member
      · split at member
        · obtain ⟨identity, same, wrote⟩ := buildCachedEnv_pin setup codec checks session payload _ e v member
          exact pinMove_build codec session payload v.1 e v.2 identity same wrote
        · change v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := 2) setup codec checks session payload).run
            (PqxdhDeploymentEnvironment.snapped _ e)) at member
          obtain ⟨identity, same, wrote⟩ := buildStep_pin setup codec checks session payload _ v member
          exact pinMove_build codec session payload v.1 e v.2 identity same wrote
      · change v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := 2) setup codec checks session payload).run
          (PqxdhDeploymentEnvironment.snapped _ e)) at member
        obtain ⟨identity, same, wrote⟩ := buildStep_pin setup codec checks session payload _ v member
        exact pinMove_build codec session payload v.1 e v.2 identity same wrote
  | finish owner raw =>
      change v ∈ support (if e.backend.2.2.active = true ∧ owner = t.kem.val ∧
        PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true then _ else _) at member
      split at member
      · obtain ⟨identity, same⟩ := finishChallengeEnv_pin setup codec p owner raw e v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
      · change v ∈ support ((PqxdhDeploymentEnvironment.finishStep (n := 2) setup codec owner raw).run
          (PqxdhDeploymentEnvironment.snapped _ e)) at member
        obtain ⟨identity, same⟩ := finishStep_pin setup codec owner raw _ v member
        exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong)
          identity same
  | hmac key message =>
      change v ∈ support ((PqxdhDeploymentEnvironment.hmacStep (n := 2) setup key message).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      obtain ⟨identity, same⟩ := hmacStep_pin setup key message _ v member
      exact pinMove_quiet codec _ _ e v.2 (fun _ _ wrong => by cases wrong) (fun _ _ wrong => by cases wrong) identity
        same
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id


/-- Every outcome of the ideal environment of a target's step moves the state with its command and reply. -/
theorem envGD_move {A : Type} (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (query : PqxdhRecordLiftInterface.EnvQuery)
    (e : EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × SplitBk)) :
    ∀ v ∈ support (((PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime).step query).run e),
      PinMove codec query.val v.1 e v.2 := by
  intro v member
  change v ∈ support (Prod.map id (PqxdhDeploymentEnvironmentDraw.withE e.backend.1) <$>
    (PqxdhDeploymentIdealEnv.idealStep setup codec checks t e.backend.1 query).run
      (PqxdhDeploymentEnvironmentDraw.dropE e)) at member
  rw [support_map] at member
  obtain ⟨u, uMember, rfl⟩ := member
  exact idealStep_move setup codec checks t e.backend.1 query _ u uMember


/-- Every startup outcome of the ideal environment of a target is a constructed Server's initial environment state: no owner and the constructed Server's identity. -/
theorem envGD_start {A : Type} (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (created : PqxdhLiveServerConstruction.Created PqxdhTranscriptAd.AssociatedData)
    (initial : EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × SplitBk))
    (started : some (created, initial) ∈ support
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime).start) :
    serverId initial = created.server.server.identity ∧ pins initial = [] := by
  change some (created, initial) ∈ support (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
    PqxdhDeploymentEnvironment.start setup ensureInit identityIndex runtime
      (fun created => (p, PqxdhDeploymentIdealSteps.splitInit created))) at started
  rw [mem_support_bind_iff] at started
  obtain ⟨p, _, startedAt⟩ := started
  have same := PqxdhDeploymentEnvironment.start_initial setup ensureInit identityIndex runtime _ created initial startedAt
  subst same
  exact ⟨rfl, rfl⟩

end Combined

end Moves

section Installs

open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthNative (NativeState)
open PqxdhDeploymentEnvironment (EnvState coins)
open PqxdhRecordLiftInterface (EnvEffects Capability EffectKind)
open PqxdhRefinement
open PqxdhDeploymentHeadlinePinCollision (Receipt)
open PqxdhDeploymentHeadlinePinEffects (restricted project)
variable {KemSK Bk : Type} {n : Nat}

/-- Every newly established phase carries a cached transcript certifying the before owner's stored Server pin. -/
def InstallPin (cache : CtxRomAuth.CtxRO.QueryCache) (before after : PqxdhRegistrationSchedule.Owner KemSK) : Prop :=
  ∀ control ad kernel, after.beacon.phase = .established control ad kernel →
    ¬ RawCtxBeaconLifecycle.Established before.beacon.phase → Receipt cache (absBytes before.beacon.serverIdentity) ad

/-- An installation's complete AD certifies the source role's public Server identity in the same ambient cache. -/
def InstallOk (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk) : (EnvEffects n).Domain → Prop
  | .inr (.installServer _ binding _) => Receipt cache (absBytes e.native.shared.2.server.server.identity) binding.associatedData
  | .inr (.installBeacon owner shell _) => ∃ before, e.native.owners[owner]? = some before ∧
      Receipt cache (absBytes before.beacon.serverIdentity) shell.associatedData
  | _ => True

open Classical in
/-- Inadmissible installation requests in the cache-restricted effect tree. -/
noncomputable def badInstall (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (query : (EnvEffects n).Domain) : Bool := decide (¬ InstallOk cache e query)

/-- Every bad installation is an administrative request. -/
theorem badInstall_admin (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (query : (EnvEffects n).Domain) (bad : badInstall cache e query = true) :
    PqxdhRecordLiftInterface.effectKind query = .administrative := by
  rcases query with coin | capability
  · simp [badInstall, InstallOk] at bad
  · cases capability with
    | hash bytes => simp [badInstall, InstallOk] at bad
    | _ => rfl

/-- Restriction changes only reply ranges, preserving every original all-reply query budget. -/
theorem restricted_bound {X : Type} (cache : CtxRomAuth.CtxRO.QueryCache)
    (predicate : (EnvEffects n).Domain → Prop) [DecidablePred predicate]
    (work : OracleComp (EnvEffects n) X) (cap : Nat) (bounded : work.IsQueryBoundP predicate cap) :
    (restricted cache work).IsQueryBoundP predicate cap := by
  unfold restricted
  refine bounded.simulateQ_of_step ?_ ?_
  · intro query paid
    simp only [project, isQueryBoundP_map_iff]
    rw [isQueryBoundP_query_iff]
    intro _
    exact Nat.one_pos
  · intro query free
    simp only [project, isQueryBoundP_map_iff]
    rw [isQueryBoundP_query_iff]
    intro paid
    exact (free paid).elim

/-- Administrative-free source work emits no bad installation in the restricted tree. -/
theorem noAdmin_ok_cached {X : Type} (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (work : OracleComp (EnvEffects n) X)
    (quiet : work.IsQueryBoundP (fun query => PqxdhRecordLiftInterface.effectKind query = .administrative) 0) :
    (restricted cache work).IsQueryBoundP (fun query => badInstall cache e query = true) 0 :=
  IsQueryBoundP.of_imp (fun query bad => badInstall_admin cache e query bad)
    (restricted_bound cache _ work 0 quiet)

/-- Coins do not issue installations. -/
theorem coins_ok_cached {X : Type} (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (work : ProbComp X) :
    (restricted cache (coins (n := n) work)).IsQueryBoundP (fun query => badInstall cache e query = true) 0 :=
  noAdmin_ok_cached cache e _ (PqxdhDeploymentEnvironmentReal.coins_noAdmin work)

/-- A certified capability request emits no bad installation, for every reply. -/
theorem issue_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (capability : Capability n) (ok : InstallOk cache e (.inr capability)) :
    (restricted cache (PqxdhDeploymentEnvironment.issue capability)).IsQueryBoundP
      (fun query => badInstall cache e query = true) 0 := by
  apply restricted_bound
  unfold PqxdhDeploymentEnvironment.issue PqxdhDeploymentEnvironment.request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl fun bad => ?_, fun _ => trivial⟩
  simp only [badInstall, decide_eq_true_eq] at bad
  exact bad ok


/-- Publishing a newly established owner uses its cached transcript pin receipt. -/
theorem ownerEffect_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk) (index : ℕ) (before after : PqxdhRegistrationSchedule.Owner KemSK)
    (found : e.native.owners[index]? = some before) (pinned : InstallPin cache before after) :
    (restricted cache (PqxdhDeploymentEnvironment.ownerEffect (n := n) index before after)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.ownerEffect
  split
  · trivial
  · rename_i previous control associatedData kernel afterPhase notEstablished
    refine issue_ok_cached cache e _ ⟨before, found, pinned control associatedData kernel afterPhase fun established => ?_⟩
    cases phase : before.beacon.phase with
    | established c a k => exact notEstablished c a k phase
    | _ => simp [phase, RawCtxBeaconLifecycle.Established] at established
  · split
    · split
      · trivial
      · exact issue_ok_cached cache e _ trivial
    · trivial

/-- Publishing a hidden owner's change with the install pin issues no inadmissible request. -/
theorem hiddenOwnerEffect_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk) (slot : PqxdhRecordLiftInterface.Slot n) (index : ℕ)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (found : e.native.owners[index]? = some before)
    (pinned : InstallPin cache before after) :
    (restricted cache (PqxdhDeploymentEnvironment.hiddenOwnerEffect slot index before after)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.hiddenOwnerEffect
  split
  · trivial
  · rename_i previous control associatedData kernel afterPhase notEstablished
    refine issue_ok_cached cache e _ ⟨before, found, pinned control associatedData kernel afterPhase fun established => ?_⟩
    cases phase : before.beacon.phase with
    | established c a k => exact notEstablished c a k phase
    | _ => simp [phase, RawCtxBeaconLifecycle.Established] at established
  · split
    · split
      · trivial
      · exact issue_ok_cached cache e _ trivial
    · trivial

/-- Restricted forwarded owner work replays on the ambient cache and supplies a receipt for every new installation. -/
theorem ownerFinishFwd_installPin {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (state : NativeState KemSK)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support (restricted cache
      ((PqxdhDeploymentEnvironment.ownerFinishFwd (n := n) setup codec retained raw before).run state))) :
    InstallPin cache before result.1.2 := by
  have replay := PqxdhDeploymentHeadlinePinEffects.replay_noAdmin cache PqxdhDeploymentEnvironmentReal.ctxAdmin
    _ (PqxdhDeploymentEnvironmentReal.ownerFinishFwd_noAdmin setup codec retained raw before state) result supported
  have source : (result.1, PqxdhDeploymentBackend.gameCtxLens.set result.2 cache) ∈ support
      ((PqxdhRegistrationSchedule.ownerFinish setup codec retained raw before).run
        (PqxdhDeploymentBackend.gameCtxLens.set state cache)) := by
    rw [PqxdhDeploymentEnvironmentReal.ownerFinish_factor setup codec PqxdhDeploymentEnvironmentReal.ctxAdmin,
      PqxdhDeploymentEnvironmentReal.ownerFinishFwd_frame setup codec, simulateQ_map, StateT.run_map,
      Functor.map_map, support_map]
    exact ⟨(result, cache), replay, rfl⟩
  intro control ad kernel established inactive
  obtain ⟨init, fields, digest, _, _, cached, assembled, identity, width⟩ := nativeOwnerFinish_new_receipt setup codec
    retained raw before _ _ source control ad kernel established inactive
  exact ⟨PqxdhTranscriptAd.initOf init, fields, digest, width, identity, cached, assembled⟩

/-- A restricted bind is installation-admissible when its prefix and each supported continuation are. -/
theorem restricted_bind_zero {X Y : Type} (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (work : OracleComp (EnvEffects n) X) (next : X → OracleComp (EnvEffects n) Y)
    (first : (restricted cache work).IsQueryBoundP (fun query => badInstall cache e query = true) 0)
    (rest : ∀ value ∈ support (restricted cache work),
      (restricted cache (next value)).IsQueryBoundP (fun query => badInstall cache e query = true) 0) :
    (restricted cache (work >>= next)).IsQueryBoundP (fun query => badInstall cache e query = true) 0 := by
  rw [restricted, simulateQ_bind]
  exact isQueryBoundP_bind first rest

/-- The real owner's finish installs only an AD certified by its cached registration transcript. -/
theorem finishStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    (restricted cache ((PqxdhDeploymentEnvironment.finishStep (n := n) setup codec owner raw).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.finishStep
  dsimp only [StateT.run]
  split
  · trivial
  · rename_i before found
    refine restricted_bind_zero cache e _ _
      (noAdmin_ok_cached cache e _ (PqxdhDeploymentEnvironmentReal.ownerFinishFwd_noAdmin setup codec _ raw before
        e.native.shared)) fun result member => ?_
    refine restricted_bind_zero cache e _ _
      (ownerEffect_ok_cached cache e owner before result.1.2 found
        (ownerFinishFwd_installPin cache setup codec _ raw before e.native.shared result member)) fun _ _ => ?_
    trivial

/-- A built peer receives exactly the AD metadata supplied to the source builder. -/
theorem built_peer_metadata
    (server : PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (ad : PqxdhTranscriptAd.AssociatedData)
    (value : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes)))
    (built : PqxdhDeploymentEnvironmentReal.Built server ad value)
    (response : PqxdhServerRegistrationPublication.Response)
    (peer : RawCtxServerRouting.Peer PqxdhTranscriptAd.AssociatedData)
    (returned : (PqxdhServerAuthExperiment.settle server value).1 = some response)
    (found : (PqxdhServerAuthExperiment.settle server value).2.server.peers response.keyId = some peer) :
    peer.metadata = ad := by
  rcases value with ⟨_ | reply, after⟩ | error | _
  · cases returned
  · obtain ⟨candidate, kernel, keyEq, _, published⟩ := built
    simp only [PqxdhServerAuthExperiment.settle, Option.some.injEq] at returned
    subst response
    simp only [published, keyEq, PqxdhServerAuthExperiment.settle, PqxdhServerRegistrationPublication.publish,
      Function.update_self, Option.some.injEq] at found
    subst peer
    rfl
  · cases returned
  · cases returned

/-- Publishing a source peer with certified exact AD metadata is admissible. -/
theorem serverEffect_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (settled : Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit PqxdhTranscriptAd.AssociatedData (List Pqxdh.Bytes))
    (ad : PqxdhTranscriptAd.AssociatedData)
    (receipt : Receipt cache (absBytes e.native.shared.2.server.server.identity) ad)
    (metadata : ∀ response peer, settled.1 = some response → settled.2.server.peers response.keyId = some peer →
      peer.metadata = ad) :
    (restricted cache (PqxdhDeploymentEnvironment.serverEffect (n := n) settled)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.serverEffect
  split
  · trivial
  · rename_i response returned
    split
    · trivial
    · rename_i peer found
      apply issue_ok_cached cache e
      change Receipt cache (absBytes e.native.shared.2.server.server.identity) peer.metadata
      rw [metadata response peer returned found]
      exact receipt

/-- The real Server build installs exactly its transcript digest's AD, whose cached response certifies the Server identity. -/
theorem buildStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (session : Nat) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    (restricted cache ((PqxdhDeploymentEnvironment.buildStep (n := n) setup codec checks session payload).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.buildStep
  dsimp only [StateT.run]
  split
  · trivial
  · rename_i token pending
    split
    · trivial
    · rename_i candidate passed
      refine restricted_bind_zero cache e _ _ (noAdmin_ok_cached cache e _ ?_) fun digest hashedMember => ?_
      · simpa only [reduceCtorEq, ite_false] using PqxdhDeploymentEnvironment.request_hash_bound (n := n)
          (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
            (PqxdhTranscriptAd.serverResponse candidate)) .administrative
      · have hashSupport : digest ∈ support (project (n := n) cache (.inr (.hash
            (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
              (PqxdhTranscriptAd.serverResponse candidate))))) := by
          simpa only [restricted, PqxdhDeploymentEnvironment.request, simulateQ_spec_query] using hashedMember
        have cached : cache (PqxdhTranscriptAd.query (PqxdhTranscriptAd.initOf token.init)
            (PqxdhTranscriptAd.serverResponse candidate)) = some digest :=
          (PqxdhDeploymentHeadlinePinEffects.project_support (n := n) cache (.inr (.hash
            (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
              (PqxdhTranscriptAd.serverResponse candidate)))) digest).mp hashSupport
        have receipt : Receipt cache (absBytes e.native.shared.2.server.server.identity) (PqxdhTranscriptAd.adOf digest) := by
          refine ⟨PqxdhTranscriptAd.initOf token.init, PqxdhTranscriptAd.serverResponse candidate, digest,
            PqxdhTranscriptAd.serverResponse_wellFormed candidate, ?_, cached, rfl⟩
          change absBytes candidate.server_identity_public_key = absBytes e.native.shared.2.server.server.identity
          rw [(PqxdhServerAuthNegativeControl.prehash_fields _ token.pending payload candidate passed).2.1]
        refine restricted_bind_zero cache e _ _ (noAdmin_ok_cached cache e _ ?_) fun result resultMember => ?_
        · have bound := PqxdhDeploymentEnvironment.build_fwd_bound (n := n)
            setup codec checks token.pending token.root payload (PqxdhTranscriptAd.adOf digest)
            e.native.shared.2.server [] .administrative
          simp only [reduceCtorEq, ite_false] at bound
          convert bound using 1
          rfl
        · have tailMember := PqxdhDeploymentEnvironment.support_simulateQ_subset (project cache) _ resultMember
          have sourced := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ tailMember
          have built := PqxdhDeploymentEnvironmentReal.build_shape (PqxdhTranscriptAd.adOf digest) setup.source
            token.pending token.root payload (PqxdhTranscriptAd.adOf digest) e.native.shared.2.server result.1 sourced
          refine restricted_bind_zero cache e _ _
            (serverEffect_ok_cached cache e _ (PqxdhTranscriptAd.adOf digest) receipt
              (built_peer_metadata _ _ _ built)) fun _ _ => ?_
          trivial

/-- A staged outcome retains the given control binding and the computed per-call AD. -/
def StagedForAd (control : beaconcrypt_core.pqxdh.BeaconInitSent) (ad : PqxdhTranscriptAd.AssociatedData)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) : Prop :=
  ∀ value, staged = some value → value.authenticated.candidate.server_binding = control.expected_server_binding ∧
    value.associatedData = ad

/-- The outer source commit turns a control-certified transcript receipt into the owner's stored-pin receipt. -/
theorem finish_installPin (cache : CtxRomAuth.CtxRO.QueryCache) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (ad : PqxdhTranscriptAd.AssociatedData)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) (stagedFor : StagedForAd control ad staged)
    (receipt : Receipt cache (absBytes control.expected_server_binding.identity_public_key) ad) :
    InstallPin cache before (PqxdhBeaconPhase2Publication.finish control before staged).2 := by
  intro afterControl recordAd kernel established _
  cases staged with
  | none => cases established
  | some value =>
    simp only [PqxdhBeaconPhase2Publication.finish] at established
    split_ifs at established with key pin
    · cases established
    · cases established
    · obtain ⟨bindingEq, adEq⟩ := stagedFor value rfl
      change RawCtxBeaconLifecycle.Phase.established _ value.associatedData value.kernel =
        .established afterControl recordAd kernel at established
      have sameAd := (RawCtxBeaconLifecycle.Phase.established.inj established).2.1
      have pinEq : absBytes before.beacon.serverIdentity =
          absBytes control.expected_server_binding.identity_public_key := by
        rw [← bindingEq]
        exact not_ne_iff.mp pin
      rw [← sameAd, adEq, pinEq]
      exact receipt

/-- Committing a staged result with a certified per-call AD issues only admissible installations. -/
theorem commitEnv_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (owner : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (owned : e.native.owners[owner]? = some before) (shared : NativeState KemSK)
    (ad : PqxdhTranscriptAd.AssociatedData) (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (stagedFor : StagedForAd control ad staged)
    (receipt : Receipt cache (absBytes control.expected_server_binding.identity_public_key) ad) :
    (restricted cache (PqxdhDeploymentIdealEnvFinish.commitEnv e owner control before shared staged)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvFinish.commitEnv
  exact restricted_bind_zero cache e _ _
    (ownerEffect_ok_cached cache e owner before _ owned (finish_installPin cache control before ad staged stagedFor receipt))
    fun _ _ => by trivial

/-- Every staged hidden forwarded finish retains the supplied metadata binding and its actual per-call AD. -/
theorem finishSplitFwd_for_ad {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (material : PqxdhDeploymentHiddenLayout.Material) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (binding : pending.metadata.binding = control.expected_server_binding) :
    ∀ staged ∈ support (PqxdhDeploymentEnvironment.finishSplitFwd (n := n) setup codec material pending),
      StagedForAd control pending.metadata.associatedData staged := by
  intro staged member value found
  unfold PqxdhDeploymentEnvironment.finishSplitFwd at member
  have inner := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  rw [support_map] at inner
  obtain ⟨y, yMember, rfl⟩ := inner
  rw [support_map] at yMember
  obtain ⟨z, zMember, rfl⟩ := yMember
  obtain ⟨value0, found0, rfl⟩ := Option.map_eq_some_iff.mp found
  unfold PqxdhDeploymentHiddenKernels.finishErased at zMember
  rw [mem_support_bind_iff] at zMember
  obtain ⟨raw, _, zMember⟩ := zMember
  rcases raw with _ | raw
  · simp only [support_pure, Set.mem_singleton_iff] at zMember
    subst zMember
    cases found0
  · dsimp only at zMember
    split_ifs at zMember
    · rw [support_map] at zMember
      obtain ⟨w, wMember, rfl⟩ := zMember
      unfold PqxdhDeploymentHiddenKernels.factoredBody at wMember
      rw [mem_support_bind_iff] at wMember
      obtain ⟨result, _, wMember⟩ := wMember
      rw [support_pure, Set.mem_singleton_iff] at wMember
      subst wMember
      obtain ⟨candidateEq, adEq⟩ := PqxdhDeploymentIdealPostGoodFinish.staged_opening _ _ _ _ value0 found0
      refine ⟨?_, adEq⟩
      change value0.authenticated.candidate.server_binding = control.expected_server_binding
      rw [candidateEq]
      exact binding
    · simp only [support_pure, Set.mem_singleton_iff] at zMember
      subst zMember
      cases found0

/-- Restricting a mapped source result preserves that result map. -/
theorem restricted_map {X Y : Type} (cache : CtxRomAuth.CtxRO.QueryCache) (f : X → Y)
    (work : OracleComp (EnvEffects n) X) : restricted cache (f <$> work) = f <$> restricted cache work := by
  simp only [restricted, simulateQ_map]

/-- An absent staged result aborts and cannot issue an establishment install. -/
theorem commitEnv_none_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (owner : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (owned : e.native.owners[owner]? = some before) (shared : NativeState KemSK) :
    (restricted cache (PqxdhDeploymentIdealEnvFinish.commitEnv e owner control before shared none)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvFinish.commitEnv
  refine restricted_bind_zero cache e _ _ (ownerEffect_ok_cached cache e owner before _ owned ?_) fun _ _ => ?_
  · intro _ _ _ established _
    cases established
  · trivial

/-- Every branch of the erased hidden grouped finish preserves its supplied metadata receipt up to the outer stored-pin check. -/
theorem groupEnv_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (owned : e.native.owners[owner]? = some before)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (binding : pending.metadata.binding = control.expected_server_binding)
    (receipt : Receipt cache (absBytes control.expected_server_binding.identity_public_key) pending.metadata.associatedData) :
    (restricted cache (PqxdhDeploymentIdealEnvFinish.groupEnv setup codec owner control before e pending)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvFinish.groupEnv
  split
  · split_ifs
    · refine restricted_bind_zero cache e _ _ (coins_ok_cached cache e _) fun read _ => ?_
      split
      · rw [restricted_map, isQueryBoundP_map_iff]
        unfold PqxdhDeploymentEnvironment.finishSplitEnv
        refine restricted_bind_zero cache e _ _
          (noAdmin_ok_cached cache e _ (PqxdhDeploymentIdealEnvFinish.finishSplitFwd_noAdmin setup codec _ _))
          fun staged stagedMember => ?_
        have original := PqxdhDeploymentEnvironment.support_simulateQ_subset (project cache) _ stagedMember
        refine restricted_bind_zero cache e _ _ (hiddenOwnerEffect_ok_cached cache e _ owner before _ owned
          (finish_installPin cache control before pending.metadata.associatedData staged
            (finishSplitFwd_for_ad setup codec _ control _ binding staged original) receipt)) fun _ _ => ?_
        trivial
      · exact commitEnv_none_ok_cached cache e owner control before owned _
    · exact commitEnv_none_ok_cached cache e owner control before owned _
  · refine restricted_bind_zero cache e _ _ (coins_ok_cached cache e _) fun r _ => ?_
    split
    · exact commitEnv_none_ok_cached cache e owner control before owned _
    · rename_i root _
      refine restricted_bind_zero cache e _ _
        (noAdmin_ok_cached cache e _ (PqxdhDeploymentIdealEnvFinish.knownFwd_noAdmin setup codec _))
        fun staged stagedMember => ?_
      have original := PqxdhDeploymentEnvironment.support_simulateQ_subset (project cache) _ stagedMember
      refine commitEnv_ok_cached cache e owner control before owned _ pending.metadata.associatedData staged ?_ receipt
      intro value found
      obtain ⟨kernel, reply, opened⟩ := PqxdhDeploymentIdealPostGoodFinish.afterRoot_opening codec.frameRead pending root
        staged (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ original) value found
      obtain ⟨candidateEq, adEq⟩ := PqxdhDeploymentIdealPostGoodFinish.staged_opening _ _ kernel reply value opened
      refine ⟨?_, adEq⟩
      rw [candidateEq]
      exact binding

/-- A hash reply in the restricted tree is recorded in the chosen ambient cache. -/
theorem request_hash_cached (cache : CtxRomAuth.CtxRO.QueryCache) (bytes : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest)
    (supported : digest ∈ support (restricted cache (PqxdhDeploymentEnvironment.request (n := n) (.hash bytes)))) :
    cache ((), bytes) = some digest := by
  apply (PqxdhDeploymentHeadlinePinEffects.project_support (n := n) cache (.inr (.hash bytes)) digest).mp
  simpa only [restricted, PqxdhDeploymentEnvironment.request, simulateQ_spec_query] using supported

/-- The actual hidden challenge finish installs only the AD of its cached, pin-checked registration transcript. -/
theorem finishChallengeEnv_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} {count : Nat}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (p : PqxdhDeploymentIdealParams.Params KemSK count) (owner : Nat) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) :
    (restricted cache ((PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvFinish.finishChallengeEnv
  dsimp only [StateT.run]
  split
  · rename_i before owned
    split
    · rename_i control prekey oneTime kem phase
      cases retained : e.native.inits owner with
      | none =>
        dsimp only
        exact commitEnv_none_ok_cached cache e owner control before owned _
      | some init =>
        cases decoded : PqxdhServerAuthExperiment.responseOf codec raw with
        | none =>
          dsimp only
          exact commitEnv_none_ok_cached cache e owner control before owned _
        | some fields =>
          dsimp only
          refine restricted_bind_zero cache e _ _ (noAdmin_ok_cached cache e _ ?_) fun digest digestMember => ?_
          · simpa only [reduceCtorEq, ite_false] using PqxdhDeploymentEnvironment.request_hash_bound (n := 2)
              (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields) .administrative
          · have cached := request_hash_cached cache (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf init) fields)
              digest digestMember
            refine restricted_bind_zero cache e _ _ (coins_ok_cached cache e _) fun prepared preparedMember => ?_
            cases prepared with
            | none => exact commitEnv_none_ok_cached cache e owner control before owned _
            | some pending =>
              have originalCoins := PqxdhDeploymentEnvironment.support_simulateQ_subset (project cache) _ preparedMember
              have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ originalCoins
              obtain ⟨response, read, metadata⟩ := PqxdhDeploymentIdealPostGoodFinish.prepareCE_facts setup codec p.challenge
                (PqxdhTranscriptAd.completedOf control digest) control before.beacon.identity prekey oneTime kem raw pending
                original
              have identity := nativeOwnerFinish_prepareCE_pin setup codec p.challenge
                (PqxdhTranscriptAd.completedOf control digest) control before.beacon.identity prekey oneTime kem raw
                pending original fields decoded
              have receipt : Receipt cache (absBytes control.expected_server_binding.identity_public_key)
                  (PqxdhTranscriptAd.adOf digest) :=
                ⟨PqxdhTranscriptAd.initOf init, fields, digest, (nativeOwnerFinish_response_fields codec raw fields decoded).1,
                  identity, cached, rfl⟩
              apply groupEnv_ok_cached cache setup codec owner control before e owned pending (by rw [metadata])
              rw [metadata]
              exact receipt
    · trivial
  · trivial

/-- Replacing only a built peer's kernel preserves the exact supplied AD metadata. -/
theorem built_replaceRaw
    (server : PqxdhServerAuthEntryFactor.ServerState) (ad : PqxdhTranscriptAd.AssociatedData)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel)
    (value : RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState))
    (built : PqxdhDeploymentEnvironmentReal.Built server ad value) :
    PqxdhDeploymentEnvironmentReal.Built server ad (PqxdhDeploymentHiddenSplit.replaceRaw kernel <$> value) := by
  rcases value with ⟨_ | response, after⟩ | error | _
  · exact built
  · obtain ⟨candidate, previous, keyEq, vacant, published⟩ := built
    refine ⟨candidate, kernel, keyEq, vacant, ?_⟩
    rw [published, keyEq, PqxdhDeploymentHiddenSplit.publish_setPeerKernel]
  · trivial
  · trivial

/-- A hidden Server install uses the same certified complete AD as its source build. -/
theorem hiddenServerEffect_ok_cached (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (slot : PqxdhRecordLiftInterface.Slot n)
    (settled : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState)
    (ad : PqxdhTranscriptAd.AssociatedData)
    (receipt : Receipt cache (absBytes e.native.shared.2.server.server.identity) ad)
    (metadata : ∀ response peer, settled.1 = some response → settled.2.server.peers response.keyId = some peer →
      peer.metadata = ad) :
    (restricted cache (PqxdhDeploymentEnvironment.hiddenServerEffect slot settled)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.hiddenServerEffect
  split
  · trivial
  · rename_i response returned
    split
    · trivial
    · rename_i peer found
      apply issue_ok_cached cache e
      change Receipt cache (absBytes e.native.shared.2.server.server.identity) peer.metadata
      rw [metadata response peer returned found]
      exact receipt

/-- The actual split hidden build publishes only its supplied, certified metadata. -/
theorem buildSplitEnv_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (e : EnvState KemSK Bk) (material : PqxdhDeploymentHiddenLayout.Material) (slot : PqxdhRecordLiftInterface.Slot 2)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes) (ad : PqxdhTranscriptAd.AssociatedData)
    (server : PqxdhServerAuthEntryFactor.ServerState)
    (receipt : Receipt cache (absBytes e.native.shared.2.server.server.identity) ad) :
    (restricted cache ((PqxdhDeploymentEnvironment.buildSplitEnv setup codec checks material slot token payload ad
      server).run [])).IsQueryBoundP (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.buildSplitEnv
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  refine restricted_bind_zero cache e _ _
    (noAdmin_ok_cached cache e _ (PqxdhDeploymentIdealEnvBuild.buildSplitFwd_noAdmin setup codec checks material token
      payload ad server [])) fun result resultMember => ?_
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset (project cache) _ resultMember
  rw [PqxdhDeploymentSplitFactor.buildSplitFwd_free ad, StateT.run_map, support_map] at original
  obtain ⟨raw, rawMember, rfl⟩ := original
  have free := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ rawMember
  have built := PqxdhDeploymentIdealEnvBuild.freeBuild_shape ad setup.source
    (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material
      PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload server raw.1 free
  refine restricted_bind_zero cache e _ _
    (hiddenServerEffect_ok_cached cache e slot _ ad receipt
      (built_peer_metadata server ad _ (built_replaceRaw server ad _ raw.1 built))) fun _ _ => ?_
  trivial

/-- The marked Server build's actual transcript hash certifies the AD passed to its hidden install. -/
theorem buildCachedEnv_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) :
    (restricted cache ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnv.buildCachedEnv
  dsimp only [StateT.run]
  split
  · rename_i slot token foundSlot foundToken
    split
    · rename_i material foundMaterial
      split
      · trivial
      · rename_i candidate passed
        refine restricted_bind_zero cache e _ _ (noAdmin_ok_cached cache e _ ?_) fun digest digestMember => ?_
        · simpa only [reduceCtorEq, ite_false] using PqxdhDeploymentEnvironment.request_hash_bound (n := 2)
            (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
              (PqxdhTranscriptAd.serverResponse candidate)) .administrative
        · have cached := request_hash_cached cache
            (PqxdhTranscriptAd.transcript (PqxdhTranscriptAd.initOf token.init)
              (PqxdhTranscriptAd.serverResponse candidate)) digest digestMember
          have receipt : Receipt cache (absBytes e.native.shared.2.server.server.identity) (PqxdhTranscriptAd.adOf digest) := by
            refine ⟨PqxdhTranscriptAd.initOf token.init, PqxdhTranscriptAd.serverResponse candidate, digest,
              PqxdhTranscriptAd.serverResponse_wellFormed candidate, ?_, cached, rfl⟩
            change absBytes candidate.server_identity_public_key = absBytes e.native.shared.2.server.server.identity
            rw [(PqxdhServerAuthNegativeControl.prehash_fields _ token.pending payload candidate passed).2.1]
          refine restricted_bind_zero cache e _ _
            (buildSplitEnv_ok_cached cache setup codec checks e material slot token payload (PqxdhTranscriptAd.adOf digest)
              e.native.shared.2.server receipt) fun _ _ => ?_
          trivial
    · trivial
  · trivial

/-- An unchanged phase cannot be a new establishment. -/
theorem installPin_refl_cached (cache : CtxRomAuth.CtxRO.QueryCache) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    InstallPin cache owner owner := by
  intro control ad kernel established inactive
  exact (inactive (by rw [established]; trivial)).elim

/-- An inactive output cannot issue an establishment install. -/
theorem installPin_inactive_cached (cache : CtxRomAuth.CtxRO.QueryCache)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (inactive : ¬ RawCtxBeaconLifecycle.Established after.beacon.phase) :
    InstallPin cache before after := by
  intro control ad kernel established _
  exact (inactive (by rw [established]; trivial)).elim

/-- A bundle only preserves its owner or advances it to InitSent. -/
theorem bundled_installPin (cache : CtxRomAuth.CtxRO.QueryCache)
    (before after : PqxdhRegistrationSchedule.Owner KemSK) (shape : PqxdhDeploymentEnvironmentReal.Bundled before after) :
    InstallPin cache before after := by
  rcases shape with rfl | ⟨⟨control, prekey, oneTime, kem, rfl⟩, _⟩
  · exact installPin_refl_cached cache _
  · exact installPin_inactive_cached cache _ _ (by simp [RawCtxBeaconLifecycle.Established])

/-- Bundling cannot newly establish an owner, and its phase-change request is admissible. -/
theorem bundleStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (e : EnvState KemSK Bk) :
    (restricted cache ((PqxdhDeploymentEnvironment.bundleStep (n := n) setup codec owner).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.bundleStep
  dsimp only [StateT.run]
  refine restricted_bind_zero cache e _ _ (coins_ok_cached cache e _) fun r rMember => ?_
  refine restricted_bind_zero cache e _ _ ?_ fun _ _ => by trivial
  have sourceCoins := PqxdhDeploymentEnvironment.support_simulateQ_subset (project cache) _ rMember
  have inner : r ∈ support ((PqxdhRegistrationSchedule.bundle setup codec owner).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ sourceCoins
  unfold PqxdhDeploymentEnvironment.ownerChange
  cases owned : e.native.owners[owner]? with
  | none => trivial
  | some current =>
    rw [PqxdhDeploymentEnvironmentReal.bundle_run_found setup codec owner _ current owned, support_map] at inner
    obtain ⟨b, bMember, rfl⟩ := inner
    have sourced := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ bMember
    have shape := PqxdhDeploymentEnvironmentReal.bundle_shape _ current b.1 sourced
    have below := (List.getElem?_eq_some_iff.mp owned).1
    simp only [List.getElem?_set_self below]
    exact ownerEffect_ok_cached cache e owner current b.1.2 owned (bundled_installPin cache current b.1.2 shape)

/-- Native accept work only draws coins and emits no installation. -/
theorem acceptStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    (restricted cache ((PqxdhDeploymentEnvironment.acceptStep (n := n) setup codec checks raw).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.acceptStep
  change (restricted cache (_ <$> coins _)).IsQueryBoundP _ 0
  rw [restricted_map, isQueryBoundP_map_iff]
  exact coins_ok_cached cache e _

/-- Public HMAC work only draws coins and emits no installation. -/
theorem hmacStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    (restricted cache ((PqxdhDeploymentEnvironment.hmacStep (n := n) setup key message).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv
  change (restricted cache (_ <$> coins _)).IsQueryBoundP _ 0
  rw [restricted_map, isQueryBoundP_map_iff]
  exact coins_ok_cached cache e _

/-- The selected accept only draws source/slot coins and emits no installation. -/
theorem acceptSelectedEnv_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} {count : Nat}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (p : PqxdhDeploymentIdealParams.Params KemSK count) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) :
    (restricted cache ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  change (restricted cache (_ <$> coins _)).IsQueryBoundP _ 0
  rw [restricted_map, isQueryBoundP_map_iff]
  exact coins_ok_cached cache e _


/-- Pool creation draws coins and appends a fresh inactive owner. -/
theorem createPoolStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK)
    (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : EnvState KemSK Bk) :
    (restricted cache ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := n) setup pool pin keyId).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep
  split
  · trivial
  · simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
    refine restricted_bind_zero cache e _ _ ?_ fun _ _ => ?_
    · change (restricted cache (_ <$> coins _)).IsQueryBoundP _ 0
      rw [restricted_map, isQueryBoundP_map_iff]
      exact coins_ok_cached cache e _
    · exact restricted_bind_zero cache e _ _ (issue_ok_cached cache e _ trivial) fun _ _ => by trivial

/-- Installation admissibility reads the native source state, including its Server identity. -/
theorem badInstall_congr {Bk' : Type} (cache : CtxRomAuth.CtxRO.QueryCache)
    (e : EnvState KemSK Bk) (e' : EnvState KemSK Bk') (same : e.native = e'.native) :
    badInstall (n := n) cache e = badInstall cache e' := by
  funext query
  unfold badInstall InstallOk
  rw [same]

/-- The ideal environment step issues no inadmissible request. -/
theorem idealStep_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} {count : Nat}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (query : PqxdhRecordLiftInterface.EnvQuery) (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) :
    (restricted cache ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId => exact createPoolStep_ok_cached cache setup (p.pool t) pin keyId e
  | bundle owner =>
      have ok := bundleStep_ok_cached cache (n := 2) setup codec owner (PqxdhDeploymentEnvironment.snapped ⟨.bundle owner, allowed⟩ e)
      rw [badInstall_congr cache (PqxdhDeploymentEnvironment.snapped ⟨.bundle owner, allowed⟩ e) e rfl] at ok
      exact ok
  | accept raw =>
      show OracleComp.IsQueryBoundP (restricted cache (if e.backend.2.2.accepts = t.accept then
          (PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e
        else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.accept raw, allowed⟩).run
          { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend }))
        (fun effect => badInstall cache e effect = true) 0
      split
      · exact acceptSelectedEnv_ok_cached cache setup codec checks p raw e
      · have ok := acceptStep_ok_cached cache (n := 2) setup codec checks raw (PqxdhDeploymentEnvironment.snapped ⟨.accept raw, allowed⟩
          { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend })
        rw [badInstall_congr cache (PqxdhDeploymentEnvironment.snapped ⟨.accept raw, allowed⟩
          { e with backend := PqxdhDeploymentIdealEnvStep.bump e.backend }) e rfl] at ok
        exact ok
  | build session payload =>
      show OracleComp.IsQueryBoundP (restricted cache (match e.backend.2.2.marks with
        | some (index, coords) => if index = session ∧ (e.native.shared.2.pending session).isSome then
            (PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e
          else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e
        | none => (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.build session payload, allowed⟩).run e))
        (fun effect => badInstall cache e effect = true) 0
      have real := buildStep_ok_cached cache (n := 2) setup codec checks session payload
        (PqxdhDeploymentEnvironment.snapped ⟨.build session payload, allowed⟩ e)
      rw [badInstall_congr cache (PqxdhDeploymentEnvironment.snapped ⟨.build session payload, allowed⟩ e) e rfl] at real
      split
      · split
        · exact buildCachedEnv_ok_cached cache setup codec checks session payload _ e
        · exact real
      · exact real
  | finish owner raw =>
      show OracleComp.IsQueryBoundP (restricted cache (if e.backend.2.2.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true then
          (PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e
        else (PqxdhDeploymentEnvironment.realStep setup codec checks ⟨.finish owner raw, allowed⟩).run e))
        (fun effect => badInstall cache e effect = true) 0
      split
      · exact finishChallengeEnv_ok_cached cache setup codec p owner raw e
      · have ok := finishStep_ok_cached cache (n := 2) setup codec owner raw (PqxdhDeploymentEnvironment.snapped ⟨.finish owner raw, allowed⟩ e)
        rw [badInstall_congr cache (PqxdhDeploymentEnvironment.snapped ⟨.finish owner raw, allowed⟩ e) e rfl] at ok
        exact ok
  | hmac key message =>
      have ok := hmacStep_ok_cached cache (n := 2) setup key message (PqxdhDeploymentEnvironment.snapped ⟨.hmac key message, allowed⟩ e)
      rw [badInstall_congr cache (PqxdhDeploymentEnvironment.snapped ⟨.hmac key message, allowed⟩ e) e rfl] at ok
      exact ok
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- Every actual ideal-environment step emits only cache-certified installations. -/
theorem envGD_ok_cached {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type} {count : Nat} {A : Type}
    (cache : CtxRomAuth.CtxRO.QueryCache) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (runtime : A) (query : PqxdhRecordLiftInterface.EnvQuery)
    (e : EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × PqxdhDeploymentIdealSteps.SplitBk)) :
    (restricted cache (((PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime).step query).run e)).IsQueryBoundP
      (fun effect => badInstall cache e effect = true) 0 := by
  change (restricted cache (Prod.map id (PqxdhDeploymentEnvironmentDraw.withE e.backend.1) <$>
    (PqxdhDeploymentIdealEnv.idealStep setup codec checks t e.backend.1 query).run
      (PqxdhDeploymentEnvironmentDraw.dropE e))).IsQueryBoundP _ 0
  rw [restricted_map, isQueryBoundP_map_iff, badInstall_congr cache e (PqxdhDeploymentEnvironmentDraw.dropE e) rfl]
  exact idealStep_ok_cached cache setup codec checks t e.backend.1 query _

open Classical in
/-- A request is flagged exactly when its current cache certificate is absent. -/
theorem badInstall_iff (cache : CtxRomAuth.CtxRO.QueryCache) (e : EnvState KemSK Bk)
    (query : (EnvEffects n).Domain) : badInstall cache e query = true ↔ ¬ InstallOk cache e query := by
  simp only [badInstall, decide_eq_true_eq]

end Installs

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_response_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_response_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_collect_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_collect_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_native_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_native_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_receipt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_new_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_new_receipt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_finish_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_finish_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_owner_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_owner_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_native_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_native_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_collectCE_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_collectCE_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_prepareCE_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_prepareCE_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_groupedCE_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_groupedCE_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_hashedCE_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_hashedCE_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_hidden_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_hidden_receipt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_new_hidden_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_new_hidden_receipt

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_hidden_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeOwnerFinish_hidden_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerFinishFwd_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerFinishFwd_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.strip_pins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.strip_pins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pins_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pins_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishedEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishedEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_member

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.markedRoot_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.markedRoot_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_member

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundled_serverIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundled_serverIdentity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptLogged_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptLogged_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailBad_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailBad_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailCE_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailCE_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tail_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tail_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptExposed_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptExposed_server

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.wrote_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.wrote_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.after_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.after_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidate_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidate_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.build_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.build_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.afterInitializationG_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.afterInitializationG_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.continueRust_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.continueRust_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidateG_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.candidateG_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.genericBuild_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.genericBuild_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeTailFwd_writeImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.nativeTailFwd_writeImpl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailFwd_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.tailFwd_det

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.freeBuild_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.freeBuild_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.settle_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.settle_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildSplitFwd_wrote' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildSplitFwd_wrote

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_pin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.stepCommand_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.stepCommand_owners

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.pinMove_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_move

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_start

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_admin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_admin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.restricted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.restricted_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.noAdmin_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.noAdmin_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.coins_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.coins_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.issue_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.issue_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerEffect_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerEffect_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenOwnerEffect_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenOwnerEffect_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerFinishFwd_installPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.ownerFinishFwd_installPin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.restricted_bind_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.restricted_bind_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.built_peer_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.built_peer_metadata

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.serverEffect_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.serverEffect_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_installPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finish_installPin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishSplitFwd_for_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishSplitFwd_for_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.restricted_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.restricted_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_none_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.commitEnv_none_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.groupEnv_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.request_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.request_hash_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.finishChallengeEnv_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.built_replaceRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.built_replaceRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenServerEffect_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hiddenServerEffect_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildSplitEnv_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildSplitEnv_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.buildCachedEnv_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_refl_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_refl_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_inactive_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.installPin_inactive_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundled_installPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundled_installPin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.bundleStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.hmacStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.acceptSelectedEnv_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.createPoolStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.idealStep_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_ok_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.envGD_ok_cached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv.badInstall_iff
