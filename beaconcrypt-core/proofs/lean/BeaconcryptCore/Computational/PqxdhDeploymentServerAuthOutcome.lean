-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrace

/-! The common authentication failure of the Server-authentication game from public journal facts (CE-8). On every outcome of the Server-authentication game, a successful finish in the public journal means the target accepted (`game_accepted`): a successful finish writes the acceptance snapshot (`finish_some`) and every later step keeps it (`path_grows`). The common event's generation receipt fixes the target's published Phase 1 bytes, whose identity key and key tuple, read back with `Phase1ReadBack`, are the target's (`generation_keys`); its agreement receipt gives an accept of the matching session in the journal whose raw candidate the source attached verification accepts with those same keys (`agreement_keys`). Hence (`game_failure`) an outcome whose journal has a successful finish and no session with both an earlier publication of the accepted decoded record (`RecordPublished`) and an accept carrying the published keys of the target is a failure of the common event. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhServerAuthRootOccurrences (Call Path callback)
open PqxdhServerAuthRootExecution (Outcome publicCall)
open PqxdhDeploymentTranscript (candidateOf acceptedKeys)
open PqxdhDeploymentServerAuthEvent (keysOfBundle)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A successful finish writes the acceptance snapshot. -/
theorem finish_some (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (beaconSeed : IdentitySeed) (raw payload : Pqxdh.Bytes)
    (before after : GameState KemSK)
    (supported : (some payload, after) ∈ support ((finishOracle setup codec publicValue beaconSeed raw).run before)) :
    ∃ snap, after.ghost.acceptance = some snap := by
  simp only [finishOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases active : before.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [active, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, _, supported⟩ := supported
      simp only [StateT.run_get, StateT.run_set, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, _, rfl, same⟩ := supported
      have resultEq := congrArg Prod.fst same
      have stateEq := congrArg Prod.snd same
      dsimp only at resultEq stateEq
      rw [stateEq]
      cases stagedValue : staged.1 with
      | none =>
          rw [stagedValue] at resultEq
          simp [PqxdhBeaconPhase2Publication.finish, PqxdhBeaconPhase2Preparation.abort] at resultEq
      | some value =>
          rw [stagedValue] at resultEq
          rw [← resultEq]
          simp only [acceptedOf, Option.isSome_some, ite_true, Option.map_some]
          unfold Ghost.accept
          cases hold : staged.2.ghost.acceptance with
          | none => simp
          | some old => exact ⟨old, by simpa using hold⟩
  | _ =>
      simp only [active, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      cases supported.1

/-- Every completed callback of a path grows its state, and so does the whole path. -/
theorem path_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (start final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar start calls final) :
    Grows start.1 final.1 ∧ ∀ call ∈ calls, Grows call.before call.after ∧ Grows call.after final.1 := by
  induction path with
  | nil state primitive => exact ⟨Grows.refl state, by simp⟩
  | cons call before middle suffix final reached rest ih =>
      have source := PqxdhServerAuthRootOccurrences.callback_source setup codec checks publicValue beaconSeed seed scalar
        call before middle reached
      have original := PqxdhServerAuthRootOccurrences.interpreted_source setup seed scalar _ _ _ source
      have grows := (authHandler_step (setup := setup) (publicValue := publicValue) codec checks beaconSeed call.query call.before
        (call.reply, call.after) original).2.1
      refine ⟨grows.trans ih.1, fun found member => ?_⟩
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact ⟨grows, ih.1⟩
      · exact ih.2 found later

/-- On every outcome of the game, a successful finish in the public journal means the target accepted. -/
theorem game_accepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (PqxdhServerAuthRootExecution.game setup codec checks false adversary))
    (raw payload : Pqxdh.Bytes)
    (finished : (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      result.state.2.map publicCall) :
    ∃ snap, result.state.1.ghost.acceptance = some snap := by
  obtain ⟨_, _, path⟩ := PqxdhServerAuthRootExecution.game_path setup codec checks false adversary result supported
  obtain ⟨call, member, same⟩ := List.mem_map.mp finished
  obtain ⟨_, growsAll⟩ := path_grows setup codec checks _ _ _ _ _ _ _ path
  obtain ⟨earlier, later, primitive, middle, _, _, reached, _⟩ :=
    PqxdhServerAuthRootOccurrences.path_occurrence setup codec checks _ _ _ _ _ _ _ path call member
  have source := PqxdhServerAuthRootOccurrences.callback_source setup codec checks _ _ _ _ call primitive middle reached
  have original := PqxdhServerAuthRootOccurrences.interpreted_source setup _ _ _ _ _ source
  obtain ⟨_, after⟩ := growsAll call member
  cases call with
  | mk query reply before final roots =>
      change (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) = _ at same
      cases same
      obtain ⟨snap, accepted⟩ := finish_some setup codec _ _ raw payload before final original
      exact ⟨snap, after.acceptance snap accepted⟩

/-- The target's identity key and key tuple. -/
def targetKeys (setup : Setup baseSpec KemSK) (context : PqxdhServerAuthEntryFactor.Context KemSK) :
    PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple :=
  ((setup.joint.publicKeys context.beaconSeed).ed25519,
    ⟨(context.publicValue setup).prekey, setup.dh.publicKey context.oneTime, context.keys.1⟩)

/-- The generation receipt fixes the target's published Phase 1 bytes, which read back to the target's keys. -/
theorem generation_keys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (result : Outcome KemSK)
    (generation : PqxdhServerAuthRootCommon.Generation setup codec result) :
    keysOfBundle codec result.context.published.1 = some (targetKeys setup result.context) := by
  obtain ⟨_, _, bytes, written, published⟩ := generation
  rw [published]
  have read := PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written
  simp [keysOfBundle, read, PqxdhServerAuthNegativeControl.beaconCandidate, PqxdhJointPhase1SourceWriter.candidate,
    PqxdhDeploymentPublishedTuple.candidateTuple, targetKeys]

/-- The agreement receipt gives an accept of the session in the journal whose raw candidate the source attached verification accepts with the target's keys. -/
theorem agreement_keys (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) (index : Nat) (agreement : PqxdhServerAuthRootCommon.Agreement setup codec checks result index) :
    ∃ acceptRaw candidate,
      (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
        result.state.2.map publicCall ∧
      candidateOf codec acceptRaw = some candidate ∧
      acceptedKeys setup.source.crypto candidate = some (targetKeys setup result.context) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, token, _, _, _, _, acceptCall, acceptRaw, input, consumed,
    _, _, _, _, acceptMember, acceptEq, prefixed, _, _, _, sessionEq, _⟩ := agreement
  have native : (some (PqxdhServerStaticDhSource.concreteInputs setup.joint result.context.seed input), consumed) ∈
      support ((nativePrefix setup codec checks result.context.seed acceptRaw).run acceptCall.before.server.consumed) := by
    rw [native_prefix, StateT.run_map, support_map]
    exact ⟨(some input, consumed), prefixed, rfl⟩
  obtain ⟨candidateEq, acceptedEq⟩ := PqxdhRegistrationJointRawSignatures.prefix_candidate setup codec checks
    result.context.seed acceptRaw _ consumed _ native
  refine ⟨acceptRaw, input.verified.candidate, ?_, candidateEq, ?_⟩
  · exact List.mem_map.mpr ⟨acceptCall, acceptMember, acceptEq⟩
  · have prekey : input.verified.keys.prekey = (result.context.publicValue setup).prekey :=
      congrArg PqxdhServerAuthRootSession.Session.prekey sessionEq
    have oneTime : input.verified.keys.oneTime = setup.dh.publicKey result.context.oneTime :=
      congrArg PqxdhServerAuthRootSession.Session.oneTime sessionEq
    have pqKey : input.verified.keys.pqKey = result.context.keys.1 :=
      congrArg PqxdhServerAuthRootSession.Session.pqKey sessionEq
    have initKex : PqxdhServerAuthPhase1Projection.unsigned input.verified.identity input.verified.keys =
        PqxdhServerAuthPhase1Projection.unsigned (setup.joint.publicKeys result.context.beaconSeed).ed25519
          (PqxdhServerAuthPhase1Identity.contextMaterial setup result.context).keyTuple :=
      congrArg PqxdhServerAuthRootSession.Session.initKex sessionEq
    have identityBytes := congrArg (fun kex : pqxdh.InitKex => absBytes kex.identity_key) initKex
    simp only [(PqxdhServerAuthPhase1Projection.unsigned_bytes _ _).1] at identityBytes
    have identity : input.verified.identity = (setup.joint.publicKeys result.context.beaconSeed).ed25519 := by
      have parsed := congrArg PqxdhEd25519EufCma.parseIdentity identityBytes
      simpa using parsed
    have keys : input.verified.keys = ⟨(result.context.publicValue setup).prekey, setup.dh.publicKey result.context.oneTime,
        result.context.keys.1⟩ := by
      rw [← prekey, ← oneTime, ← pqKey]
    simp only [PqxdhServerStaticDhSource.concreteInputs] at acceptedEq
    change PqxdhJointPhase1Reports.sourceAccept (fun publicKey => setup.source.crypto.verify publicKey.toList)
      input.verified.candidate = _
    rw [acceptedEq, identity, keys]
    rfl

/-- Public failure of the common event: an outcome whose journal has a successful finish and no session with both an earlier publication of the accepted decoded record and an accept whose raw candidate the source attached verification accepts with the published keys of the target is a failure of the common authentication event. -/
theorem game_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (adversary : Adversary) (result : Outcome KemSK)
    (supported : result ∈ support (PqxdhServerAuthRootExecution.game setup codec checks false adversary))
    (raw payload : Pqxdh.Bytes)
    (finished : (⟨.inr (.finish raw), some payload⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      result.state.2.map publicCall)
    (unmatched : ∀ index, PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index (result.state.2.map publicCall) →
      ∀ acceptRaw candidate keys,
        (⟨.inr (.accept acceptRaw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
          result.state.2.map publicCall →
        candidateOf codec acceptRaw = some candidate → acceptedKeys setup.source.crypto candidate = some keys →
        keysOfBundle codec result.context.published.1 ≠ some keys) :
    PqxdhServerAuthCommonEvent.Failure setup codec checks result := by
  refine ⟨game_accepted setup codec checks adversary result supported raw payload finished, ?_⟩
  rintro ⟨index, ⟨generation, _, agreement⟩, published⟩
  obtain ⟨acceptRaw, candidate, member, candidateEq, keysEq⟩ := agreement_keys setup codec checks result index agreement
  exact unmatched index published acceptRaw candidate _ member candidateEq keysEq
    (generation_keys setup codec phase1 result generation)

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.finish_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.finish_some

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.path_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.path_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.game_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.game_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.generation_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.generation_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.agreement_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.agreement_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.game_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthOutcome.game_failure
