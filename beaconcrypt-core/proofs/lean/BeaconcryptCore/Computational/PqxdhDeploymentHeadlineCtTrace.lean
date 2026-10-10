-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost

/-!
# The transcript's ciphertext collision is a ghost collision (CE-12 P2b, design-v2 section 7.4)

The second half of design-v2's `ct_collision_game`: on every outcome of the ghost-instrumented experiment (`PqxdhDeploymentHeadlineCtGhost.gameG`) of a budget-respecting adversary, the public ciphertext-collision event `CtCollEvent` of the transcript (`PqxdhDeploymentHeadlineCollision`) is the ghost collision of a triple `(k, i, j)` with `k < qCreate` and `i < j < qAccept` (`ctColl_triple`). Under the approved Phase 1 and Phase 2 read-back contracts; no other premise.

- Native links. The logged accept: a prefix that collected an input logged the verified candidate's PQ key with the input's ciphertext (`prefixEnc_input`, through `PqxdhRegistrationJointRawSignatures.verifyInput_source` and `PqxdhRegistrationJointKemCollected.interpreted_fields`); the accept core stores that ciphertext in the pending token (`nativeClient_token`, through `PqxdhRegistrationInputs.accepted_used` and `PqxdhServerClearedRoot.accepted_cleared`), which the tail publishes at the old session counter (`tail_token`, `tail_none`, `acceptEnc_token`); the session counter and the other tokens move as `PqxdhDeploymentCompileFootprint.accept_footprint` says (`nativeAccept_footprint`). The build: a published response is the Phase 2 writer's output on fields carrying the consumed token's ciphertext (`buildOracle_ciphertext`, from `PqxdhServerAuthNegativeControl.build_published`; `nativeBuild_footprint`).
- Transcript functions on an appended entry (`acceptOf_quiet`, `buildOf_quiet`, `bundleOf_quiet`, `acceptCount_quiet`, `acceptOf_accept`, `buildOf_build`, `bundleOf_bundle`, `acceptCount_accept`).
- The run invariant `Tracks` of the instrumented experiment: the ghost has one encapsulation entry per raw accept attempt, at the session index the attempt allocated; the accept that returned a session verified to a candidate whose PQ key is the key of that session's logged encapsulation; a pending token carries its session's logged ciphertext; the first successful build response of a session reads back, with the Phase 2 reader, to its logged ciphertext; the ghost has one key per owner, the KEM public key the owner still holds; and the first successful bundle of an owner carries the owner's logged key in its PQ field. It holds initially (`tracks_initial`) and after every query (`tracks_step`): commands that keep the Server's sessions and pending tokens and every owner's KEM key (`native_kept`, `coinSend_kept` for the secrecy commands, `finish_kept`, `serverStep_kept`, `beaconStep_kept`) through `tracks_frame` (`quiet_step`, `secrecy_step`), and the create (`create_step`), bundle (`bundle_step`, with `Phase1ReadBack`: `PqxdhDeploymentKeyMatch.candidateOf_written`, `publishedPq_candidate`), build (`build_step`, with `Phase2ReadBack`) and raw accept (`accept_step`). Hence it holds on every outcome (`tracks_game`).
- Event. A session that carries a ciphertext to a PQ key (`CarriesTo`) logged that encapsulation (`carries_logged`, through `PqxdhDeploymentKeyMatch.verified_keys`), so a transcript collision of a triple is its ghost collision (`ctColl_logged`). The ranges come from the transcript counts of the experiment: every query class has at most its cap of entries (`game_counts`, by `PqxdhDeploymentSecrecy.run_wrap` and `PqxdhDeploymentTargetRange.ledger_count`), the ghost's attempts are the accept entries (`acceptCount_classCount`), and its keys are the native owners, counted by the transcript summary (`PqxdhDeploymentEligibility.agree_game`, `PqxdhDeploymentTargetRange.owners_count`).

These are support facts of programs; no security claim is made here, and no assumption or contract beyond the two read-back contracts is used.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerRootPreparation (Inputs)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentHeadlineCtGhost (Enc Ghost prefixEnc acceptEnc collectEnc collectVerifiedEnc)

/-! ### The logged accept: its encapsulation is the token's ciphertext -/

section Accept
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhServerAuthNative (NativeState nativeAccept nativeClient)

/-- A logged native prefix that collected an input logged the encapsulation of the verified candidate's PQ key with the input's ciphertext. -/
theorem prefixEnc_input (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (result : (Option (Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) × Option Enc) × List Pqxdh.Bytes)
    (member : result ∈ support ((prefixEnc setup codec checks seed raw).run consumed))
    (input : Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) (collected : result.1.1 = some input) :
    ∃ verified, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some verified ∧
      result.1.2 = some (verified.keys.pqKey, input.ciphertext) := by
  unfold prefixEnc collectEnc at member
  rw [simulateQ_bind, StateT.run_bind, PqxdhRegistrationJointRawSignatures.verifyInput_source, pure_bind] at member
  cases found : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
  | none =>
      rw [found] at member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      cases collected
  | some verified =>
      rw [found] at member
      refine ⟨verified, rfl, ?_⟩
      dsimp only at member
      unfold collectVerifiedEnc at member
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨⟨ephemeral, before⟩, _, member⟩ := member
      cases ephemeral with
      | none =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
          subst member
          cases collected
      | some ephemeral =>
          dsimp only at member
          rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
          obtain ⟨⟨reply, middle⟩, _, member⟩ := member
          rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
          obtain ⟨⟨finished, after⟩, reached, member⟩ := member
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
          subst member
          dsimp only at collected
          subst collected
          obtain ⟨_, _, replied⟩ := PqxdhRegistrationJointKemCollected.interpreted_fields _ verified ephemeral reply middle
            after input reached
          rw [replied]
          rfl

/-- The Server's accept core under the native client: a returned token's pending registration carries the input's ciphertext (`server_accept` stores the encapsulation's ciphertext; clearing the root input keeps it). -/
theorem nativeClient_token (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) (state : NativeState KemSK)
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × NativeState KemSK)
    (member : result ∈ support ((nativeClient hmac index control binding input).run state))
    (token : PqxdhServerRelatedRootConsumer.Returned) (returned : result.1 = RustM.ok (some token)) :
    token.pending.kem_ciphertext = input.ciphertext := by
  unfold nativeClient at member
  cases accepted : PqxdhServerRelatedRootInput.accept control binding input with
  | ok value =>
      rcases value with ⟨final, original⟩ | error
      · rw [accepted] at member
        simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨_, _, _, _, rfl⟩ := member
        simp only [RustM.ok.injEq, Option.some.injEq] at returned
        subst returned
        have used := PqxdhRegistrationInputs.accepted_used control final _ .Fresh binding _ _ original accepted
        rw [used.1] at accepted
        rw [PqxdhServerClearedRoot.accepted_cleared binding input control original accepted]
        rfl
      · rw [accepted] at member
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
        subst member
        cases returned
  | fail error =>
      rw [accepted] at member
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      cases returned
  | div =>
      rw [accepted] at member
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      cases returned

/-- The native accept tail on a collected input: a returned session is the old session counter, and its pending token carries the input's ciphertext. -/
theorem tail_token (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (game : PqxdhServerAuthExperiment.GameState KemSK) (input : Inputs Reader PqxdhJointGapDh.ScalarBytes Word32)
    (consumed : List Pqxdh.Bytes) (shared : NativeState KemSK) (result : Option Nat × NativeState KemSK)
    (member : result ∈ support ((PqxdhRegistrationJointServerAccept.tail setup publicIdentity game
      (some input, consumed)).run shared))
    (session : Nat) (returned : result.1 = some session) :
    session = game.sessions ∧ ∃ token, result.2.2.pending session = some token ∧
      token.pending.kem_ciphertext = input.ciphertext := by
  rw [PqxdhDeploymentBackend.tail_eq, PqxdhDeploymentBackend.nativeSet_run_bind] at member
  unfold PqxdhDeploymentBackend.acceptRest at member
  dsimp only at member
  rw [StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨answered, clientMember, member⟩ := member
  rcases answered with ⟨(_ | token) | error | _, after⟩
  · simp only at member
    subst member
    cases returned
  · simp only [StateT.run_bind, PqxdhServerAuthNative.nativeModify, StateT.run_pure] at member
    change result ∈ support (pure (some game.sessions, (after.1, { after.2 with
      pending := Function.update after.2.pending game.sessions (some token) })) : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    simp only [Option.some.injEq] at returned
    subst returned
    refine ⟨rfl, token, Function.update_self .., ?_⟩
    exact nativeClient_token setup.hmac game.sessions game.server.control _ input _ _ clientMember token rfl
  · simp only at member
    subst member
    cases returned
  · simp only at member
    subst member
    cases returned

/-- The native accept tail without a collected input returns no session. -/
theorem tail_none (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (game : PqxdhServerAuthExperiment.GameState KemSK) (consumed : List Pqxdh.Bytes) (shared : NativeState KemSK)
    (result : Option Nat × NativeState KemSK)
    (member : result ∈ support ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup publicIdentity game
      (none, consumed)).run shared)) :
    result.1 = none := by
  rw [PqxdhDeploymentBackend.tail_eq, PqxdhDeploymentBackend.nativeSet_run_bind] at member
  unfold PqxdhDeploymentBackend.acceptRest at member
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
  subst member
  rfl

/-- The logged native accept: a returned session's pending token carries the ciphertext of the logged encapsulation, whose key is the verified candidate's PQ key. -/
theorem acceptEnc_token (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK)
    (result : (Option Nat × Option Enc) × NativeState KemSK)
    (member : result ∈ support (acceptEnc setup codec checks seed raw shared)) (session : Nat)
    (returned : result.1.1 = some session) :
    ∃ verified token, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some verified ∧
      result.2.2.pending session = some token ∧ result.1.2 = some (verified.keys.pqKey, token.pending.kem_ciphertext) := by
  unfold acceptEnc at member
  rw [mem_support_bind_iff] at member
  obtain ⟨collected, collectedMember, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨answer, answerMember, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  rcases collected with ⟨⟨_ | input, logged⟩, consumed⟩
  · have none := tail_none setup _ shared.2 consumed shared answer answerMember
    rw [none] at returned
    cases returned
  · obtain ⟨_, token, found, ciphertext⟩ := tail_token setup _ shared.2 input consumed shared answer answerMember
      session returned
    obtain ⟨verified, checked, entry⟩ := prefixEnc_input setup codec checks seed raw shared.2.server.consumed
      ((some input, logged), consumed) collectedMember input rfl
    refine ⟨verified, token, checked, found, ?_⟩
    rw [ciphertext]
    exact entry

/-- The native raw accept's footprint on the Server: the session counter advances by one, pending tokens other than at the old counter are kept, a failed accept keeps all of them, and a returned session is the old counter (`accept_footprint` through `accept_native`). -/
theorem nativeAccept_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK)
    (result : Option Nat × NativeState KemSK)
    (member : result ∈ support ((nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run
      shared)) :
    result.2.2.sessions = shared.2.sessions + 1 ∧
      (∀ session, session ≠ shared.2.sessions → result.2.2.pending session = shared.2.pending session) ∧
      (result.1 = none → result.2.2.pending = shared.2.pending) ∧
      (∀ session, result.1 = some session → session = shared.2.sessions) := by
  rw [← PqxdhServerAuthNative.accept_native setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw]
    at member
  have reached := PqxdhServerAuthNative.evaluate_support setup seed PqxdhRegistrationSchedule.observationScalar _ shared
    result member
  obtain ⟨_, _, sessions, others, none, some⟩ := PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw
    shared.2 _ reached
  exact ⟨sessions, others, none, fun session returned => (some session returned).1⟩

end Accept


/-! ### The build writes the pending token's ciphertext -/

section Build
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhServerAuthNative (NativeState nativeBuild)

/-- A published response of the Server build is the Phase 2 writer's output on fields carrying the KEM ciphertext of the session's pending token (`PqxdhServerAuthNegativeControl.build_published`). -/
theorem buildOracle_ciphertext (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (game : PqxdhServerAuthExperiment.GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthExperiment.GameState KemSK)
    (member : result ∈ support ((PqxdhServerAuthExperiment.buildOracle setup codec checks session payload).run game))
    (response : PqxdhServerRegistrationPublication.Response) (returned : result.1 = some response) :
    ∃ token, game.pending session = some token ∧ ∃ fields : PqxdhServerRegistrationPublication.ResponseFields,
      codec.write2 fields = some response.serialized ∧ fields.kemCiphertext = token.pending.kem_ciphertext := by
  simp only [PqxdhServerAuthExperiment.buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at member
  cases found : game.pending session with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      cases returned
  | some token =>
      simp only [found, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨built, lifted, member⟩ := member
      obtain ⟨builtMember, same⟩ := PqxdhServerAuthExperiment.liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨_, rfl, rfl⟩ := member
      obtain ⟨candidate, _, _, frameBytes, _, _, _, _, carried, _, _, _, _, _, written, _⟩ :=
        PqxdhServerAuthNegativeControl.build_published setup codec checks token.pending token.root payload game.server
          game.ctx built.1 builtMember response returned
      exact ⟨token, rfl, ⟨candidate.key_id, candidate.ephemeral_public_key, candidate.server_identity_public_key,
        candidate.kem_ciphertext, frameBytes⟩, written, carried⟩

/-- The native build's footprint on the Server: the session counter is kept, the built session's pending token is consumed, every other token is kept, and a published response carries the consumed token's ciphertext in the Phase 2 writer's fields. -/
theorem nativeBuild_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes) (shared : NativeState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × NativeState KemSK)
    (member : result ∈ support ((nativeBuild setup codec checks session payload).run shared)) :
    result.2.2.sessions = shared.2.sessions ∧
      (∀ other, other ≠ session → result.2.2.pending other = shared.2.pending other) ∧
      result.2.2.pending session = none ∧
      (∀ response, result.1 = some response → ∃ token, shared.2.pending session = some token ∧
        ∃ fields : PqxdhServerRegistrationPublication.ResponseFields,
          codec.write2 fields = some response.serialized ∧ fields.kemCiphertext = token.pending.kem_ciphertext) := by
  rw [← PqxdhServerAuthNative.build_native setup codec checks seed PqxdhRegistrationSchedule.observationScalar session
    payload] at member
  have reached := PqxdhServerAuthNative.evaluate_support setup seed PqxdhRegistrationSchedule.observationScalar _ shared
    result member
  obtain ⟨_, _, sessions, others, consumed, _, _⟩ := PqxdhDeploymentCompileFootprint.build_footprint setup codec checks
    session payload shared.2 _ reached
  exact ⟨sessions, others, consumed, fun response returned =>
    buildOracle_ciphertext setup codec checks session payload shared.2 _ reached response returned⟩

end Build

/-! ### Transcript functions on an appended entry -/

section Transcript
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (acceptOf buildOf bundleOf acceptCount)

/-- The queries other than a raw accept. -/
def NotAccept : PqxdhDeploymentInterface.Query → Prop
  | .inl (.inr (.accept _)) => False
  | _ => True

/-- The queries other than a build. -/
def NotBuild : PqxdhDeploymentInterface.Query → Prop
  | .inl (.inr (.build _ _)) => False
  | _ => True

/-- The queries other than a bundle. -/
def NotBundle : PqxdhDeploymentInterface.Query → Prop
  | .inl (.inr (.bundle _)) => False
  | _ => True

/-- The queries whose entries change neither the accepts, the builds, the bundles nor the accept count of a transcript. -/
def Quiet (query : PqxdhDeploymentInterface.Query) : Prop := NotAccept query ∧ NotBuild query ∧ NotBundle query

/-- An appended entry: the first match of the transcript, else the entry's own. -/
theorem findSome?_snoc {α β : Type} (list : List α) (last : α) (f : α → Option β) :
    (list ++ [last]).findSome? f = (list.findSome? f).or (f last) := by
  rw [List.findSome?_append]
  simp

/-- An entry other than a raw accept keeps the accepts of a transcript. -/
theorem acceptOf_quiet (transcript : List Entry) (entry : Entry) (quiet : NotAccept entry.query) (session : Nat) :
    acceptOf (transcript ++ [entry]) session = acceptOf transcript session := by
  unfold acceptOf
  rw [findSome?_snoc]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · simp
  · cases command <;> simp_all [NotAccept]
  · simp

/-- An entry other than a build keeps the builds of a transcript. -/
theorem buildOf_quiet (transcript : List Entry) (entry : Entry) (quiet : NotBuild entry.query) (session : Nat) :
    buildOf (transcript ++ [entry]) session = buildOf transcript session := by
  unfold buildOf
  rw [findSome?_snoc]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · simp
  · cases command <;> simp_all [NotBuild]
  · simp

/-- An entry other than a bundle keeps the bundles of a transcript. -/
theorem bundleOf_quiet (transcript : List Entry) (entry : Entry) (quiet : NotBundle entry.query) (owner : Nat) :
    bundleOf (transcript ++ [entry]) owner = bundleOf transcript owner := by
  unfold bundleOf
  rw [findSome?_snoc]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · simp
  · cases command <;> simp_all [NotBundle]
  · simp

/-- An entry other than a raw accept keeps the accept count. -/
theorem acceptCount_quiet (transcript : List Entry) (entry : Entry) (quiet : NotAccept entry.query) :
    acceptCount (transcript ++ [entry]) = acceptCount transcript := by
  unfold acceptCount
  rw [List.countP_append]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · simp
  · cases command <;> simp_all [NotAccept]
  · simp

/-- A raw accept entry adds one accept attempt. -/
theorem acceptCount_accept (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option Nat) :
    acceptCount (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) = acceptCount transcript + 1 := by
  unfold acceptCount
  rw [List.countP_append]
  simp

/-- A raw accept entry adds its session to the accepts unless an earlier accept returned it. -/
theorem acceptOf_accept (transcript : List Entry) (raw : Pqxdh.Bytes) (reply : Option Nat) (session : Nat) :
    acceptOf (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) session =
      (acceptOf transcript session).or (if reply = some session then some raw else none) := by
  unfold acceptOf
  rw [findSome?_snoc]
  cases reply with
  | none => simp
  | some handle => by_cases same : handle = session <;> simp [same]

/-- A build entry adds its response to the builds unless an earlier build of the session succeeded. -/
theorem buildOf_build (transcript : List Entry) (built : Nat) (payload : Option Pqxdh.Bytes)
    (reply : Option PqxdhServerRegistrationPublication.Response) (session : Nat) :
    buildOf (transcript ++ [⟨.inl (.inr (.build built payload)), reply⟩]) session =
      (buildOf transcript session).or (if built = session then reply else none) := by
  unfold buildOf
  rw [findSome?_snoc]
  cases reply with
  | none => by_cases same : built = session <;> simp [same]
  | some response => by_cases same : built = session <;> simp [same]

/-- A bundle entry adds its bytes to the bundles unless an earlier bundle of the owner succeeded. -/
theorem bundleOf_bundle (transcript : List Entry) (index : Nat) (reply : Option Pqxdh.Bytes) (owner : Nat) :
    bundleOf (transcript ++ [⟨.inl (.inr (.bundle index)), reply⟩]) owner =
      (bundleOf transcript owner).or (if index = owner then reply else none) := by
  unfold bundleOf
  rw [findSome?_snoc]
  cases reply with
  | none => by_cases same : index = owner <;> simp [same]
  | some bytes => by_cases same : index = owner <;> simp [same]

end Transcript


/-! ### The run invariant between the transcript, the native state and the ghost -/

section Invariant
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (acceptOf buildOf bundleOf acceptCount candidateOf publishedPq)
open PqxdhDeploymentEligibility (kemPublic)

/-- The run invariant of the instrumented experiment. The ghost has one encapsulation entry per raw accept attempt (`sessions`, `attempts`); the accept that returned a session verified to a candidate whose PQ key is the key of that session's logged encapsulation (`accepts`); a pending token carries its session's logged ciphertext (`pending`); the first successful build response of a session reads back, with the Phase 2 reader, to its logged ciphertext (`builds`); the ghost has one key per owner (`owners`), equal to the KEM public key the owner still holds (`keys`); and the first successful bundle of an owner carries, in its PQ field, the owner's logged key (`bundles`). -/
structure Tracks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (state : PqxdhDeploymentSecrecy.State KemSK × Ghost) : Prop where
  sessions : state.2.encs.length = state.1.2.native.shared.2.sessions
  attempts : state.2.encs.length = acceptCount state.1.1.transcript
  accepts : ∀ session raw, acceptOf state.1.1.transcript session = some raw → ∃ verified c,
    PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some verified ∧
      state.2.encs[session]? = some (some (verified.keys.pqKey, c))
  pending : ∀ session token, state.1.2.native.shared.2.pending session = some token →
    ∃ key, state.2.encs[session]? = some (some (key, token.pending.kem_ciphertext))
  builds : ∀ session response, buildOf state.1.1.transcript session = some response →
    ∃ key c, state.2.encs[session]? = some (some (key, c)) ∧
      (codec.read2 response.serialized).bind codec.ciphertext = some c
  owners : state.2.keys.length = state.1.2.native.owners.length
  keys : ∀ (k : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey),
    state.1.2.native.owners[k]? = some owner → kemPublic owner.beacon.phase = some key → state.2.keys[k]? = some key
  bundles : ∀ k bytes published key, bundleOf state.1.1.transcript k = some bytes →
    candidateOf codec bytes = some published → publishedPq published = some key → state.2.keys[k]? = some key

/-- The invariant holds at the start of the experiment: empty transcript, no owner, no session, empty ghost. -/
theorem tracks_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    Tracks setup codec checks ((PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial created),
      Ghost.empty) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro session raw found
    simp [PqxdhDeploymentSecrecy.Ledger.empty, acceptOf] at found
  · intro session token found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro session response found
    simp [PqxdhDeploymentSecrecy.Ledger.empty, buildOf] at found
  · intro k owner key found
    simp [PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · intro k bytes published key found
    simp [PqxdhDeploymentSecrecy.Ledger.empty, bundleOf] at found

/-- Owners whose number is kept and who hold no KEM public key they did not hold before. -/
def KeysKept (before after : PqxdhRegistrationSchedule.State KemSK) : Prop :=
  after.owners.length = before.owners.length ∧
    ∀ (k : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey),
      after.owners[k]? = some owner → kemPublic owner.beacon.phase = some key →
        ∃ old : PqxdhRegistrationSchedule.Owner KemSK, before.owners[k]? = some old ∧ kemPublic old.beacon.phase = some key

/-- Equal owner views keep the KEM public keys. -/
theorem alike_keys (before after : PqxdhRegistrationSchedule.State KemSK)
    (alike : PqxdhDeploymentEligibility.Alike before after) : KeysKept before after := by
  refine ⟨alike.2.1, fun k owner key found held => ?_⟩
  have same := alike.2.2 k
  rw [found] at same
  cases old : before.owners[k]? with
  | none => rw [old] at same; cases same
  | some previous =>
      rw [old] at same
      simp only [Option.map_some, Option.some.injEq] at same
      refine ⟨previous, rfl, ?_⟩
      have field := congrArg (fun view => view.2.2.2.2) same
      simp only [PqxdhDeploymentEligibility.view] at field
      rw [← field]
      exact held

/-- A step that appends a quiet entry, keeps the ghost, the session counter, the pending tokens and the owners' KEM public keys keeps the invariant. -/
theorem tracks_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (before after : PqxdhDeploymentSecrecy.State KemSK × Ghost) (tracks : Tracks setup codec checks before)
    (entry : Entry) (quiet : Quiet entry.query)
    (transcript : after.1.1.transcript = before.1.1.transcript ++ [entry]) (ghost : after.2 = before.2)
    (sessions : after.1.2.native.shared.2.sessions = before.1.2.native.shared.2.sessions)
    (pending : after.1.2.native.shared.2.pending = before.1.2.native.shared.2.pending)
    (kept : KeysKept before.1.2.native after.1.2.native) : Tracks setup codec checks after := by
  refine ⟨?_, ?_, fun session raw found => ?_, fun session token found => ?_, fun session response found => ?_, ?_,
    fun k owner key found held => ?_, fun k bytes published key found read pq => ?_⟩
  · rw [ghost, sessions]
    exact tracks.sessions
  · rw [ghost, transcript, acceptCount_quiet _ _ quiet.1]
    exact tracks.attempts
  · rw [transcript, acceptOf_quiet _ _ quiet.1] at found
    rw [ghost]
    exact tracks.accepts session raw found
  · rw [pending] at found
    rw [ghost]
    exact tracks.pending session token found
  · rw [transcript, buildOf_quiet _ _ quiet.2.1] at found
    rw [ghost]
    exact tracks.builds session response found
  · rw [ghost, kept.1]
    exact tracks.owners
  · obtain ⟨old, oldFound, oldHeld⟩ := kept.2 k owner key found held
    rw [ghost]
    exact tracks.keys k old key oldFound oldHeld
  · rw [transcript, bundleOf_quiet _ _ quiet.2.2] at found
    rw [ghost]
    exact tracks.bundles k bytes published key found read pq

/-- A step that appends a bundle entry keeps the invariant when it keeps the rest and a published bundle carries the owner's logged key. -/
theorem tracks_bundle_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (before after : PqxdhDeploymentSecrecy.State KemSK × Ghost) (tracks : Tracks setup codec checks before)
    (index : Nat) (reply : Option Pqxdh.Bytes)
    (transcript : after.1.1.transcript = before.1.1.transcript ++ [⟨.inl (.inr (.bundle index)), reply⟩])
    (ghost : after.2 = before.2)
    (sessions : after.1.2.native.shared.2.sessions = before.1.2.native.shared.2.sessions)
    (pending : after.1.2.native.shared.2.pending = before.1.2.native.shared.2.pending)
    (kept : KeysKept before.1.2.native after.1.2.native)
    (fresh : ∀ bytes published key, reply = some bytes → candidateOf codec bytes = some published →
      publishedPq published = some key → before.2.keys[index]? = some key) : Tracks setup codec checks after := by
  have notAccept : NotAccept (Entry.query ⟨.inl (.inr (.bundle index)), reply⟩) := trivial
  have notBuild : NotBuild (Entry.query ⟨.inl (.inr (.bundle index)), reply⟩) := trivial
  refine ⟨?_, ?_, fun session raw found => ?_, fun session token found => ?_, fun session response found => ?_, ?_,
    fun k owner key found held => ?_, fun k bytes published key found read pq => ?_⟩
  · rw [ghost, sessions]
    exact tracks.sessions
  · rw [ghost, transcript, acceptCount_quiet _ _ notAccept]
    exact tracks.attempts
  · rw [transcript, acceptOf_quiet _ _ notAccept] at found
    rw [ghost]
    exact tracks.accepts session raw found
  · rw [pending] at found
    rw [ghost]
    exact tracks.pending session token found
  · rw [transcript, buildOf_quiet _ _ notBuild] at found
    rw [ghost]
    exact tracks.builds session response found
  · rw [ghost, kept.1]
    exact tracks.owners
  · obtain ⟨old, oldFound, oldHeld⟩ := kept.2 k owner key found held
    rw [ghost]
    exact tracks.keys k old key oldFound oldHeld
  · rw [transcript, bundleOf_bundle] at found
    rw [ghost]
    cases earlier : bundleOf before.1.1.transcript k with
    | some first =>
        rw [earlier, Option.some_or, Option.some.injEq] at found
        subst found
        exact tracks.bundles k first published key earlier read pq
    | none =>
        rw [earlier, Option.none_or] at found
        by_cases same : index = k
        · subst same
          simp only [ite_true] at found
          exact fresh bytes published key found read pq
        · simp [same] at found

/-- A step that appends a build entry keeps the invariant when it removes pending tokens only, keeps the rest, and a published response reads back to the session's logged ciphertext. -/
theorem tracks_build_frame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (before after : PqxdhDeploymentSecrecy.State KemSK × Ghost) (tracks : Tracks setup codec checks before)
    (built : Nat) (payload : Option Pqxdh.Bytes) (reply : Option PqxdhServerRegistrationPublication.Response)
    (transcript : after.1.1.transcript = before.1.1.transcript ++ [⟨.inl (.inr (.build built payload)), reply⟩])
    (ghost : after.2 = before.2)
    (sessions : after.1.2.native.shared.2.sessions = before.1.2.native.shared.2.sessions)
    (pending : ∀ session token, after.1.2.native.shared.2.pending session = some token →
      before.1.2.native.shared.2.pending session = some token)
    (kept : KeysKept before.1.2.native after.1.2.native)
    (fresh : ∀ response, reply = some response → ∃ key c, before.2.encs[built]? = some (some (key, c)) ∧
      (codec.read2 response.serialized).bind codec.ciphertext = some c) : Tracks setup codec checks after := by
  have notAccept : NotAccept (Entry.query ⟨.inl (.inr (.build built payload)), reply⟩) := trivial
  have notBundle : NotBundle (Entry.query ⟨.inl (.inr (.build built payload)), reply⟩) := trivial
  refine ⟨?_, ?_, fun session raw found => ?_, fun session token found => ?_, fun session response found => ?_, ?_,
    fun k owner key found held => ?_, fun k bytes published key found read pq => ?_⟩
  · rw [ghost, sessions]
    exact tracks.sessions
  · rw [ghost, transcript, acceptCount_quiet _ _ notAccept]
    exact tracks.attempts
  · rw [transcript, acceptOf_quiet _ _ notAccept] at found
    rw [ghost]
    exact tracks.accepts session raw found
  · rw [ghost]
    exact tracks.pending session token (pending session token found)
  · rw [transcript, buildOf_build] at found
    rw [ghost]
    cases earlier : buildOf before.1.1.transcript session with
    | some first =>
        rw [earlier, Option.some_or, Option.some.injEq] at found
        subst found
        exact tracks.builds session first earlier
    | none =>
        rw [earlier, Option.none_or] at found
        by_cases same : built = session
        · subst same
          simp only [ite_true] at found
          exact fresh response found
        · simp [same] at found
  · rw [ghost, kept.1]
    exact tracks.owners
  · obtain ⟨old, oldFound, oldHeld⟩ := kept.2 k owner key found held
    rw [ghost]
    exact tracks.keys k old key oldFound oldHeld
  · rw [transcript, bundleOf_quiet _ _ notBundle] at found
    rw [ghost]
    exact tracks.bundles k bytes published key found read pq

end Invariant


/-! ### Native steps that keep the Server's sessions and pending tokens and every owner's KEM key -/

section NativeSteps
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhDeploymentInterface (Spec)

/-- The Server's session counter and pending tokens are kept. -/
def ServerKept (before after : PqxdhRegistrationSchedule.State KemSK) : Prop :=
  after.shared.2.sessions = before.shared.2.sessions ∧ after.shared.2.pending = before.shared.2.pending

/-- Kept owners and Server fields from a step that keeps the native state. -/
theorem kept_refl (state : PqxdhRegistrationSchedule.State KemSK) : KeysKept state state ∧ ServerKept state state :=
  ⟨⟨rfl, fun _ owner _ found held => ⟨owner, found, held⟩⟩, rfl, rfl⟩

/-- Composition of kept steps. -/
theorem kept_trans (first second third : PqxdhRegistrationSchedule.State KemSK)
    (left : KeysKept first second ∧ ServerKept first second) (right : KeysKept second third ∧ ServerKept second third) :
    KeysKept first third ∧ ServerKept first third := by
  refine ⟨⟨right.1.1.trans left.1.1, fun k owner key found held => ?_⟩, right.2.1.trans left.2.1,
    right.2.2.trans left.2.2⟩
  obtain ⟨middle, middleFound, middleHeld⟩ := right.1.2 k owner key found held
  exact left.1.2 k middle key middleFound middleHeld

/-- A Server record step keeps the owners, the session counter and the pending tokens. -/
theorem serverStep_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.serverStep setup codec route query).run state)) :
    KeysKept state.native result.2.native ∧ ServerKept state.native result.2.native := by
  obtain ⟨owners, _, _, pending, sessions, _⟩ :=
    PqxdhDeploymentNative.serverStep_fields setup codec route query state result supported
  refine ⟨⟨by rw [owners], fun k owner key found held => ⟨owner, by rw [← owners]; exact found, held⟩⟩, sessions, pending⟩

/-- A Beacon record step keeps the owners' KEM keys, the session counter and the pending tokens. -/
theorem beaconStep_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhDeploymentNative.State KemSK)
    (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentNative.beaconStep setup codec index query).run state)) :
    KeysKept state.native result.2.native ∧ ServerKept state.native result.2.native := by
  obtain ⟨_, _, _, pending, sessions, _⟩ :=
    PqxdhDeploymentNative.beaconStep_fields setup codec index query state result supported
  exact ⟨alike_keys _ _ (PqxdhDeploymentEligibility.beaconStep_alike setup codec index query state result supported),
    sessions, pending⟩

/-- A native-interface program that issues only coins and sends keeps the owners' KEM keys, the session counter and the pending tokens (the secrecy commands, `PqxdhDeploymentSecrecy.secrecy_frame`). -/
theorem coinSend_kept {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (program : OracleComp Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (state : PqxdhDeploymentNative.State KemSK) (result : Value × PqxdhDeploymentNative.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      program).run state)) :
    KeysKept state.native result.2.native ∧ ServerKept state.native result.2.native := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact kept_refl _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have firstKept : KeysKept state.native middle.native ∧ ServerKept state.native middle.native := by
        rcases query with coin | command
        · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at first
          obtain ⟨_, _, same⟩ := first
          cases same
          exact kept_refl _
        · cases command with
          | serverSend kid plaintext => exact serverStep_kept setup codec route (.inl (plaintext, kid)) state _ first
          | beaconSend index plaintext => exact beaconStep_kept setup codec index (.inl plaintext) state _ first
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      exact kept_trans _ _ _ firstKept (ih reply restBound middle second)

/-- A finish keeps the Server's sessions and pending tokens, and leaves the finished owner either unchanged or without a KEM key (aborted or established). -/
theorem finish_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes)
    (native : PqxdhRegistrationSchedule.State KemSK) (inner : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK)
    (member : inner ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed
      (.inr (.finish index raw))).run native)) :
    KeysKept native inner.2 ∧ ServerKept native inner.2 := by
  have shared := PqxdhRegistrationSchedule.owner_fields setup codec checks serverSeed (.inr (.finish index raw)) trivial
    native inner member
  have server : ServerKept native inner.2 := ⟨by rw [shared], by rw [shared]⟩
  refine ⟨?_, server⟩
  cases found : native.owners[index]? with
  | none =>
      change inner ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run native) at member
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw native found, support_pure,
        Set.mem_singleton_iff] at member
      subst member
      exact (kept_refl native).1
  | some owner =>
      change inner ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw native) at member
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw native owner found, support_map] at member
      obtain ⟨reached, reachedMember, rfl⟩ := member
      obtain ⟨failed, finished⟩ := PqxdhDeploymentCompileFootprint.finish_owner setup codec raw owner native.shared reached
        reachedMember
      have bound : index < native.owners.length := (List.getElem?_eq_some_iff.mp found).1
      refine ⟨List.length_set .., fun k next key nextFound held => ?_⟩
      by_cases same : k = index
      · subst same
        rw [List.getElem?_set_self bound, Option.some.injEq] at nextFound
        subst nextFound
        rcases reply : reached.1.1 with _ | plaintext
        · rcases failed reply with unchanged | ⟨control, _, _, _, _, aborted⟩
          · rw [unchanged] at held
            exact ⟨owner, found, held⟩
          · rw [aborted] at held
            simp [PqxdhBeaconPhase2Preparation.abort, PqxdhDeploymentEligibility.kemPublic] at held
        · obtain ⟨_, _, _, _, _, _, _, _, installed⟩ := finished plaintext reply
          rw [installed] at held
          simp [PqxdhDeploymentEligibility.kemPublic] at held
      · rw [List.getElem?_set_ne (Ne.symm same)] at nextFound
        exact ⟨next, nextFound, held⟩

/-- Every native command other than create, bundle, raw accept and build keeps every owner's KEM key, the Server's session counter and its pending tokens. -/
theorem native_kept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (query : Spec.Domain)
    (kind : match query with
      | .inr (.create _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) => False
      | _ => True)
    (state : PqxdhDeploymentNative.State KemSK) (answer : Spec.Range query × PqxdhDeploymentNative.State KemSK)
    (member : answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run state)) :
    KeysKept state.native answer.2.native ∧ ServerKept state.native answer.2.native := by
  rcases query with coin | command
  · simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact kept_refl _
  · cases command with
    | create => exact False.elim kind
    | bundle => exact False.elim kind
    | accept => exact False.elim kind
    | build => exact False.elim kind
    | finish index raw =>
        simp only [PqxdhDeploymentNative.handler] at member
        obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state answer member
        exact finish_kept setup codec checks serverSeed index raw state.native inner innerMember
    | hmac key message =>
        simp only [PqxdhDeploymentNative.handler] at member
        obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state answer member
        have keys := alike_keys _ _ (PqxdhDeploymentEligibility.shared_alike setup codec checks serverSeed
          (.hmac key message) trivial _ inner innerMember)
        simp only [PqxdhRegistrationSchedule.handler,
          ← PqxdhServerAuthNative.hmac_native setup serverSeed PqxdhRegistrationSchedule.observationScalar] at innerMember
        obtain ⟨_, reached⟩ := PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state.native inner
          innerMember
        obtain ⟨_, _, pending, sessions⟩ := PqxdhDeploymentCompileFootprint.hmac_fixed key message _ _ reached
        exact ⟨keys, sessions, pending⟩
    | hash bytes =>
        simp only [PqxdhDeploymentNative.handler] at member
        obtain ⟨inner, innerMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state answer member
        have keys := alike_keys _ _ (PqxdhDeploymentEligibility.shared_alike setup codec checks serverSeed
          (.hash bytes) trivial _ inner innerMember)
        simp only [PqxdhRegistrationSchedule.handler,
          ← PqxdhServerAuthNative.hash_native setup serverSeed PqxdhRegistrationSchedule.observationScalar] at innerMember
        obtain ⟨_, reached⟩ := PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state.native inner
          innerMember
        obtain ⟨_, _, pending, sessions⟩ := PqxdhDeploymentCompileFootprint.hash_fixed bytes _ _ reached
        exact ⟨keys, sessions, pending⟩
    | serverSend kid plaintext => exact serverStep_kept setup codec route (.inl (plaintext, kid)) state answer member
    | serverRaw raw => exact serverStep_kept setup codec route (.inr raw) state answer member
    | beaconSend index plaintext => exact beaconStep_kept setup codec index (.inl plaintext) state answer member
    | beaconRaw index raw => exact beaconStep_kept setup codec index (.inr raw) state answer member

end NativeSteps


/-! ### Every query of the instrumented experiment keeps the invariant -/

section Steps
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhDeploymentInterface (Spec FreshBounds Entry parsePin)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentTranscript (acceptOf buildOf bundleOf acceptCount candidateOf publishedPq)
open PqxdhDeploymentEligibility (kemPublic)
open PqxdhDeploymentHeadlineCtGhost (handlerG createdKey)

/-- A forwarded coin or command of the CE handler is the native handler's step, recorded in the ledger. -/
theorem forward_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (command : Spec.Domain) (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (result : Spec.Range command × PqxdhDeploymentSecrecy.State KemSK)
    (member : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds
      (.inl command)).run (ledger, native))) :
    ∃ answer ∈ support ((PqxdhDeploymentNative.handler setup codec checks route serverSeed command).run native),
      result = (answer.1, (ledger.record (.inl command) answer.1, answer.2)) := by
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at member
  obtain ⟨reached, member, rfl⟩ := member
  rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map]
    at member
  obtain ⟨answer, answerMember, rfl⟩ := member
  exact ⟨answer, answerMember, rfl⟩

/-- A quiet native command keeps the invariant. -/
theorem quiet_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (command : Spec.Domain)
    (kind : match command with
      | .inr (.create _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) => False
      | _ => True)
    (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK) (ghost : Ghost)
    (tracks : Tracks setup codec checks ((ledger, native), ghost))
    (result : Spec.Range command × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((fun result => (result.1, (result.2, ghost))) <$>
      (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds (.inl command)).run (ledger, native))) :
    Tracks setup codec checks result.2 := by
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  obtain ⟨answer, answerMember, rfl⟩ := forward_support setup codec checks route serverSeed bounds command ledger native
    inner innerMember
  have kept := native_kept setup codec checks route serverSeed command kind native answer answerMember
  have quiet : Quiet (.inl command : PqxdhDeploymentInterface.Query) := by
    rcases command with coin | command
    · exact ⟨trivial, trivial, trivial⟩
    · cases command <;> first | exact False.elim kind | exact ⟨trivial, trivial, trivial⟩
  exact tracks_frame setup codec checks _ _ tracks ⟨.inl command, answer.1⟩ quiet rfl rfl kept.2.1 kept.2.2 kept.1

/-- A secrecy command keeps the invariant: it issues only coins and sends and appends its own entry. -/
theorem secrecy_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (secrecy : PqxdhDeploymentInterface.Secrecy) (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (ghost : Ghost) (tracks : Tracks setup codec checks ((ledger, native), ghost))
    (result : Option RawCtxSourceSend.Encrypted × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((fun result => (result.1, (result.2, ghost))) <$>
      (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds (.inr secrecy)).run (ledger, native))) :
    Tracks setup codec checks result.2 := by
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  rw [PqxdhDeploymentEligibility.handler_run, support_map] at innerMember
  obtain ⟨reached, reachedMember, rfl⟩ := innerMember
  have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId
      bounds (.inr secrecy)).run ledger) := by
    apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
      _ native
    rw [StateT.run'_eq, support_map]
    exact ⟨reached, reachedMember, rfl⟩
  have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
    ledger reached.1 value
  have kept := coinSend_kept setup codec checks route serverSeed _
    (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy ledger) native
    reached reachedMember
  exact tracks_frame setup codec checks _ _ tracks ⟨.inr secrecy, reached.1.1⟩ ⟨trivial, trivial, trivial⟩ recorded rfl
    kept.2.1 kept.2.2 kept.1

/-- A create keeps the invariant: a created owner holds the KEM key the ghost appends. -/
theorem create_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (pin : Pqxdh.Bytes) (keyId : Aeneas.Std.U64) (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK)
    (ghost : Ghost) (tracks : Tracks setup codec checks ((ledger, native), ghost))
    (result : Option Nat × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((fun result => (result.1, (result.2, { ghost with keys := ghost.keys ++
      (createdKey result.1 result.2).toList }))) <$> (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed
        bounds (.inl (.inr (.create pin keyId)))).run (ledger, native))) :
    Tracks setup codec checks result.2 := by
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  obtain ⟨answer, answerMember, rfl⟩ := forward_support setup codec checks route serverSeed bounds
    (.inr (.create pin keyId)) ledger native inner innerMember
  simp only [PqxdhDeploymentNative.handler] at answerMember
  cases parsed : parsePin pin with
  | none =>
      rw [parsed, StateT.run_pure, support_pure, Set.mem_singleton_iff] at answerMember
      subst answerMember
      have ghostSame : { ghost with keys := ghost.keys ++ (createdKey none (ledger.record
          (.inl (.inr (.create pin keyId))) none, native)).toList } = ghost := by
        cases ghost
        simp [createdKey]
      refine tracks_frame setup codec checks _ _ tracks ⟨.inl (.inr (.create pin keyId)), none⟩ ⟨trivial, trivial, trivial⟩
        rfl ghostSame rfl rfl (kept_refl native.native).1
  | some word =>
      rw [parsed, StateT.run_map, support_map] at answerMember
      obtain ⟨created, createdMember, rfl⟩ := answerMember
      obtain ⟨inner', inner'Member, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native created createdMember
      change inner' ∈ support ((PqxdhRegistrationSchedule.create setup word keyId).run native.native) at inner'Member
      obtain ⟨seed, prekey, keys, rfl⟩ := PqxdhDeploymentEligibility.create_support setup word keyId native.native inner'
        inner'Member
      have keyEq : createdKey (some native.native.owners.length) (ledger.record (.inl (.inr (.create pin keyId)))
          (some native.native.owners.length), { native with native := { native.native with owners :=
            native.native.owners ++ [⟨⟨seed, keyId, word, .fresh ⟨⟨word, keyId⟩⟩ prekey keys⟩, 0⟩] } }) = some keys.1 := by
        simp [createdKey, kemPublic]
      simp only [keyEq, Option.toList_some]
      have lengths : ghost.keys.length = native.native.owners.length := tracks.owners
      have entryQuiet : Quiet (Entry.query ⟨.inl (.inr (.create pin keyId)), some native.native.owners.length⟩) :=
        ⟨trivial, trivial, trivial⟩
      simp only [PqxdhDeploymentSecrecy.Ledger.record]
      refine ⟨tracks.sessions, ?_, fun session raw found => ?_, tracks.pending, fun session response found => ?_, ?_,
        fun k owner key found held => ?_, fun k bytes published key found read pq => ?_⟩
      · rw [acceptCount_quiet _ _ entryQuiet.1]
        exact tracks.attempts
      · rw [acceptOf_quiet _ _ entryQuiet.1] at found
        exact tracks.accepts session raw found
      · rw [buildOf_quiet _ _ entryQuiet.2.1] at found
        exact tracks.builds session response found
      · simp only [List.length_append, List.length_singleton]
        rw [lengths]
      · simp only at found
        by_cases below : k < native.native.owners.length
        · rw [List.getElem?_append_left below] at found
          rw [List.getElem?_append_left (by omega)]
          exact tracks.keys k owner key found held
        · by_cases same : k = native.native.owners.length
          · subst same
            rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at found
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst found
            simp only [kemPublic, Option.some.injEq] at held
            subst held
            rw [← lengths, List.getElem?_append_right (le_refl _), Nat.sub_self]
            rfl
          · rw [List.getElem?_eq_none (by simp; omega)] at found
            cases found
      · rw [bundleOf_quiet _ _ entryQuiet.2.2] at found
        have old := tracks.bundles k bytes published key found read pq
        have below : k < ghost.keys.length := (List.getElem?_eq_some_iff.mp old).1
        rw [List.getElem?_append_left below]
        exact old

/-- A bundle keeps the invariant: a published bundle is the Phase 1 writer's output on the owner's own candidate, whose PQ field carries the owner's KEM key, which the ghost logged at the create (`Phase1ReadBack`). -/
theorem bundle_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (index : Nat) (ledger : Ledger)
    (native : PqxdhDeploymentNative.State KemSK) (ghost : Ghost) (tracks : Tracks setup codec checks ((ledger, native), ghost))
    (result : Option Pqxdh.Bytes × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((fun result => (result.1, (result.2, ghost))) <$>
      (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds (.inl (.inr (.bundle index)))).run
        (ledger, native))) :
    Tracks setup codec checks result.2 := by
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  obtain ⟨answer, answerMember, rfl⟩ := forward_support setup codec checks route serverSeed bounds (.inr (.bundle index))
    ledger native inner innerMember
  simp only [PqxdhDeploymentNative.handler] at answerMember
  obtain ⟨inner', inner'Member, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer answerMember
  have shared := PqxdhRegistrationSchedule.owner_fields setup codec checks serverSeed (.inr (.bundle index)) trivial
    native.native inner' inner'Member
  have facts : KeysKept native.native inner'.2 ∧ ∀ bytes published key, inner'.1 = some bytes →
      candidateOf codec bytes = some published → publishedPq published = some key → ghost.keys[index]? = some key := by
    cases found : native.native.owners[index]? with
    | none =>
        have run : (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.bundle index))).run
            native.native = pure (none, native.native) := by
          simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.bundle, StateT.run_bind,
            StateT.run_get, pure_bind, found, StateT.run_pure]
        rw [run, support_pure, Set.mem_singleton_iff] at inner'Member
        subst inner'Member
        exact ⟨(kept_refl _).1, fun bytes _ _ returned => by cases returned⟩
    | some owner =>
        change inner' ∈ support (PqxdhRegistrationSchedule.bundle setup codec index native.native) at inner'Member
        rw [PqxdhRegistrationSchedule.bundle_source setup codec index native.native owner found, support_map]
          at inner'Member
        obtain ⟨reached, reachedMember, rfl⟩ := inner'Member
        obtain ⟨rejected, published⟩ := PqxdhDeploymentEligibility.bundle_candidate setup codec index owner reached
          reachedMember
        have bound : index < native.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
        rcases outcome : reached.1 with _ | bytes
        · have same := rejected outcome
          refine ⟨⟨List.length_set .., fun k next key nextFound held => ?_⟩, fun bytes _ _ returned => ?_⟩
          · by_cases atIndex : k = index
            · subst atIndex
              rw [List.getElem?_set_self bound, Option.some.injEq, same] at nextFound
              subst nextFound
              exact ⟨_, found, held⟩
            · rw [List.getElem?_set_ne (Ne.symm atIndex)] at nextFound
              exact ⟨next, nextFound, held⟩
          · cases returned
        · obtain ⟨fresh, prekey, oneTime, kem, s1, s2, s3, wasFresh, installed, written⟩ := published bytes outcome
          have ownerKey : kemPublic owner.beacon.phase = some kem.1 := by
            rcases wasFresh with isFresh | isFresh <;> rw [isFresh] <;> rfl
          refine ⟨⟨List.length_set .., fun k next key nextFound held => ?_⟩,
            fun bytes' published key returned read pq => ?_⟩
          · by_cases atIndex : k = index
            · subst atIndex
              rw [List.getElem?_set_self bound, Option.some.injEq] at nextFound
              subst nextFound
              rw [installed] at held
              exact ⟨owner, found, by rw [ownerKey]; exact held⟩
            · rw [List.getElem?_set_ne (Ne.symm atIndex)] at nextFound
              exact ⟨next, nextFound, held⟩
          · rw [Option.some.injEq] at returned
            subst returned
            rw [PqxdhDeploymentKeyMatch.candidateOf_written codec phase1 _ bytes written, Option.some.injEq] at read
            subst read
            rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pq
            subst pq
            exact tracks.keys index owner kem.1 found ownerKey
  exact tracks_bundle_frame setup codec checks _ _ tracks index inner'.1 rfl rfl (by rw [shared]) (by rw [shared])
    facts.1 facts.2

/-- A build keeps the invariant: it consumes the session's pending token and a published response carries the token's ciphertext in the Phase 2 writer's fields, which the Phase 2 reader reads back (`Phase2ReadBack`). -/
theorem build_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (session : Nat) (payload : Option Pqxdh.Bytes)
    (ledger : Ledger) (native : PqxdhDeploymentNative.State KemSK) (ghost : Ghost)
    (tracks : Tracks setup codec checks ((ledger, native), ghost))
    (result : Option PqxdhServerRegistrationPublication.Response × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((fun result => (result.1, (result.2, ghost))) <$>
      (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds
        (.inl (.inr (.build session payload)))).run (ledger, native))) :
    Tracks setup codec checks result.2 := by
  rw [support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  obtain ⟨answer, answerMember, rfl⟩ := forward_support setup codec checks route serverSeed bounds
    (.inr (.build session payload)) ledger native inner innerMember
  simp only [PqxdhDeploymentNative.handler] at answerMember
  obtain ⟨inner', inner'Member, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ native answer answerMember
  change inner' ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeBuild setup codec checks
    session payload)).run native.native) at inner'Member
  rw [PqxdhRegistrationSchedule.onShared_run, support_map] at inner'Member
  obtain ⟨built, builtMember, rfl⟩ := inner'Member
  obtain ⟨sessions, others, consumed, published⟩ := nativeBuild_footprint setup codec checks serverSeed session payload
    native.native.shared built builtMember
  refine tracks_build_frame setup codec checks _ _ tracks session payload built.1 rfl rfl sessions
    (fun other token found => ?_) ⟨rfl, fun _ owner _ found held => ⟨owner, found, held⟩⟩ (fun response returned => ?_)
  · by_cases same : other = session
    · subst same
      simp only at found
      rw [consumed] at found
      cases found
    · simp only at found
      rw [others other same] at found
      exact found
  · obtain ⟨token, pending, fields, written, carried⟩ := published response returned
    obtain ⟨key, logged⟩ := tracks.pending session token pending
    obtain ⟨read, readFound, ciphertext, _, _, _, _⟩ := phase2 fields response.serialized written
    refine ⟨key, token.pending.kem_ciphertext, logged, ?_⟩
    rw [readFound, Option.bind_some, ciphertext, carried]

/-- An entry the ghost already holds survives an appended entry. -/
theorem encs_extend (ghost : Ghost) (entry : Option Enc) (session : Nat) (value : Option Enc)
    (found : ghost.encs[session]? = some value) : (ghost.encs ++ [entry])[session]? = some value := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- A raw accept keeps the invariant: it allocates the next session, appends its logged encapsulation at that index, and a returned session's pending token carries the logged ciphertext of the verified candidate's PQ key. -/
theorem accept_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (ledger : Ledger)
    (native : PqxdhDeploymentNative.State KemSK) (ghost : Ghost) (tracks : Tracks setup codec checks ((ledger, native), ghost))
    (result : Option Nat × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((fun result => (result.1.1, ((ledger.record (.inl (.inr (.accept raw))) result.1.1,
      { native with native := { native.native with shared := result.2 } }),
      { ghost with encs := ghost.encs ++ [result.1.2] }))) <$>
        PqxdhDeploymentHeadlineCtGhost.acceptEnc setup codec checks serverSeed raw native.native.shared)) :
    Tracks setup codec checks result.2 := by
  rw [support_map] at member
  obtain ⟨answer, answerMember, rfl⟩ := member
  have projected : (answer.1.1, answer.2) ∈ support ((PqxdhServerAuthNative.nativeAccept setup codec checks serverSeed
      PqxdhRegistrationSchedule.observationScalar raw).run native.native.shared) := by
    rw [← PqxdhDeploymentHeadlineCtGhost.acceptEnc_fst, support_map]
    exact ⟨answer, answerMember, rfl⟩
  obtain ⟨sessions, others, failedKeeps, returnedAt⟩ := nativeAccept_footprint setup codec checks serverSeed raw
    native.native.shared _ projected
  have lengthEq : ghost.encs.length = native.native.shared.2.sessions := tracks.sessions
  have entryNotBuild : NotBuild (Entry.query ⟨.inl (.inr (.accept raw)), answer.1.1⟩) := trivial
  have entryNotBundle : NotBundle (Entry.query ⟨.inl (.inr (.accept raw)), answer.1.1⟩) := trivial
  have below : ∀ session value, ghost.encs[session]? = some value → session ≠ native.native.shared.2.sessions :=
    fun session value found same => by
      have bound := (List.getElem?_eq_some_iff.mp found).1
      omega
  have newEntry : (ghost.encs ++ [answer.1.2])[native.native.shared.2.sessions]? = some answer.1.2 := by
    rw [← lengthEq]
    simp
  simp only [PqxdhDeploymentSecrecy.Ledger.record]
  refine ⟨?_, ?_, fun session raw' found => ?_, fun session token found => ?_, fun session response found => ?_,
    tracks.owners, tracks.keys, fun k bytes published key found read pq => ?_⟩
  · simp only [List.length_append, List.length_singleton]
    rw [lengthEq]
    exact sessions.symm
  · simp only [List.length_append, List.length_singleton]
    rw [acceptCount_accept, tracks.attempts]
  · rw [acceptOf_accept] at found
    cases earlier : acceptOf ledger.transcript session with
    | some first =>
        rw [earlier, Option.some_or, Option.some.injEq] at found
        subst found
        obtain ⟨verified, c, checked, logged⟩ := tracks.accepts session first earlier
        exact ⟨verified, c, checked, encs_extend ghost _ session _ logged⟩
    | none =>
        rw [earlier, Option.none_or] at found
        by_cases returned : answer.1.1 = Option.some session
        · simp only [returned, ite_true, Option.some.injEq] at found
          subst found
          obtain ⟨verified, token, checked, _, entry⟩ := PqxdhDeploymentHeadlineCtTrace.acceptEnc_token setup codec
            checks serverSeed raw native.native.shared answer answerMember session returned
          have atSession := returnedAt session returned
          subst atSession
          refine ⟨verified, token.pending.kem_ciphertext, checked, ?_⟩
          rw [newEntry, entry]
        · simp [returned] at found
  · by_cases same : session = native.native.shared.2.sessions
    · subst same
      cases returned : answer.1.1 with
      | none =>
          have kept := failedKeeps returned
          simp only at found
          rw [kept] at found
          obtain ⟨_, logged⟩ := tracks.pending _ token found
          exact absurd rfl (below _ _ logged)
      | some returnedSession =>
          have atSession := returnedAt returnedSession returned
          subst atSession
          obtain ⟨verified, token', _, pending', entry⟩ := PqxdhDeploymentHeadlineCtTrace.acceptEnc_token setup codec
            checks serverSeed raw native.native.shared answer answerMember _ returned
          simp only at found
          rw [pending', Option.some.injEq] at found
          subst found
          exact ⟨verified.keys.pqKey, by rw [newEntry, entry]⟩
    · simp only at found
      rw [others session same] at found
      obtain ⟨key, logged⟩ := tracks.pending session token found
      exact ⟨key, encs_extend ghost _ session _ logged⟩
  · rw [buildOf_quiet _ _ entryNotBuild] at found
    obtain ⟨key, c, logged, read⟩ := tracks.builds session response found
    exact ⟨key, c, encs_extend ghost _ session _ logged, read⟩
  · rw [bundleOf_quiet _ _ entryNotBundle] at found
    exact tracks.bundles k bytes published key found read pq

end Steps


/-! ### Along the instrumented experiment -/

section Game
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhDeploymentInterface (Spec FreshBounds Entry Mode ModeSpec asModeO Budget queryClass)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentTranscript (acceptOf buildOf bundleOf acceptCount candidateOf acceptedKeys publishedPq)
open PqxdhDeploymentHeadlineCtGhost (handlerG gameG forget GhostColl TripleColl)
open PqxdhDeploymentHeadlineCollision (CarriesTo CtCollAt CtCollEvent ctCollEvent)

/-- Every query of the instrumented experiment keeps the invariant, under the approved Phase 1 and Phase 2 read-back contracts. -/
theorem tracks_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.State KemSK × Ghost) (tracks : Tracks setup codec checks state)
    (result : PqxdhDeploymentInterface.FullSpec.Range query × (PqxdhDeploymentSecrecy.State KemSK × Ghost))
    (member : result ∈ support ((handlerG setup codec checks route serverSeed bounds query).run state)) :
    Tracks setup codec checks result.2 := by
  rcases state with ⟨⟨ledger, native⟩, ghost⟩
  rcases query with (coin | command) | secrecy
  · exact quiet_step setup codec checks route serverSeed bounds (.inl coin) trivial ledger native ghost tracks result
      member
  · cases command with
    | create pin keyId =>
        exact create_step setup codec checks route serverSeed bounds pin keyId ledger native ghost tracks result member
    | bundle index =>
        exact bundle_step setup codec checks route serverSeed bounds phase1 index ledger native ghost tracks result member
    | accept raw => exact accept_step setup codec checks serverSeed raw ledger native ghost tracks result member
    | build session payload =>
        exact build_step setup codec checks route serverSeed bounds phase2 session payload ledger native ghost tracks
          result member
    | finish index raw =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.finish index raw)) trivial ledger native ghost
          tracks result member
    | hmac key message =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.hmac key message)) trivial ledger native
          ghost tracks result member
    | hash bytes =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.hash bytes)) trivial ledger native ghost
          tracks result member
    | serverSend kid plaintext =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.serverSend kid plaintext)) trivial ledger
          native ghost tracks result member
    | serverRaw raw =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.serverRaw raw)) trivial ledger native ghost
          tracks result member
    | beaconSend index plaintext =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.beaconSend index plaintext)) trivial ledger
          native ghost tracks result member
    | beaconRaw index raw =>
        exact quiet_step setup codec checks route serverSeed bounds (.inr (.beaconRaw index raw)) trivial ledger native
          ghost tracks result member
  · exact secrecy_step setup codec checks route serverSeed bounds secrecy ledger native ghost tracks result member

/-- On every outcome of the instrumented experiment, the final state satisfies the invariant. -/
theorem tracks_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      (PqxdhDeploymentSecrecy.State KemSK × Ghost)) × A)
    (supported : outcome ∈ support ((gameG setup codec checks route ensureInit identityIndex bounds mode adversary).run
      runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK × Ghost) (reached : outcome.1 = some (created, output, final)) :
    Tracks setup codec checks final := by
  simp only [gameG, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    exact OracleComp.simulateQ_run_preserves_inv_of_query (handlerG setup codec checks route constructed.seed bounds)
      (Tracks setup codec checks)
      (fun query state holds result member => tracks_step setup codec checks route constructed.seed bounds phase1 phase2
        query state holds result member)
      (asModeO mode adversary) _ (tracks_initial setup codec checks constructed) _ executedMember

/-- A session that carries a ciphertext to a PQ key logged exactly that encapsulation. -/
theorem carries_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (state : PqxdhDeploymentSecrecy.State KemSK × Ghost) (tracks : Tracks setup codec checks state)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (session : Nat)
    (carries : CarriesTo setup.source.crypto codec state.1.1.transcript ciphertext pqKey session) :
    state.2.encs[session]? = some (some (pqKey, ciphertext)) := by
  obtain ⟨response, accepted, keys, buildFound, readBack, acceptFound, keysFound, pqEq⟩ := carries
  obtain ⟨key, c, logged, read⟩ := tracks.builds session response buildFound
  rw [readBack, Option.some.injEq] at read
  subst read
  obtain ⟨raw, rawFound, candidateFound⟩ := Option.bind_eq_some_iff.mp acceptFound
  obtain ⟨verified, c', checked, logged'⟩ := tracks.accepts session raw rawFound
  rw [logged, Option.some.injEq, Option.some.injEq, Prod.mk.injEq] at logged'
  obtain ⟨keyEq, _⟩ := logged'
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup codec checks raw verified checked
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  rw [logged, keyEq, ← pqEq]

/-- A transcript ciphertext collision of a triple is the ghost collision of that triple. -/
theorem ctColl_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (state : PqxdhDeploymentSecrecy.State KemSK × Ghost) (tracks : Tracks setup codec checks state) (k i j : Nat)
    (coll : CtCollAt setup.source.crypto codec state.1.1.transcript k i j) : GhostColl k i j state.2 := by
  obtain ⟨_, ciphertext, published, pqKey, publishedFound, pqFound, first, second⟩ := coll
  obtain ⟨bytes, bytesFound, read⟩ := Option.bind_eq_some_iff.mp publishedFound
  exact ⟨pqKey, ciphertext, tracks.bundles k bytes published pqKey bytesFound read pqFound,
    carries_logged setup codec checks state tracks ciphertext pqKey i first,
    carries_logged setup codec checks state tracks ciphertext pqKey j second⟩

/-- The accept count is the number of accept-class entries. -/
theorem acceptCount_classCount (transcript : List Entry) :
    acceptCount transcript = PqxdhDeploymentTargetRange.classCount 3 transcript := by
  unfold acceptCount PqxdhDeploymentTargetRange.classCount
  refine List.countP_congr fun entry _ => ?_
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · simp [queryClass]
  · cases command <;> simp [queryClass]
  · rcases secrecy with ⟨_, _, _⟩ | ⟨_, _⟩ <;> simp [queryClass]

/-- On every outcome of the experiment of a budget-respecting adversary, every query class has at most its cap of transcript entries. -/
theorem game_counts (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex
      bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (final : PqxdhDeploymentSecrecy.State KemSK) (reached : outcome.1 = some (created, output, final)) (kind : Fin 14) :
    PqxdhDeploymentTargetRange.classCount kind final.1.transcript ≤ budget.cap kind := by
  simp only [PqxdhDeploymentSecrecy.game, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    cases reached
    have wrapped := PqxdhDeploymentSecrecy.run_wrap setup codec checks route constructed.seed bounds
      (asModeO mode adversary) (PqxdhDeploymentNative.initial constructed)
    simp only [StateT.run] at wrapped
    rw [wrapped, support_map] at executedMember
    obtain ⟨inner, innerMember, same⟩ := executedMember
    obtain ⟨_, rfl⟩ := Prod.mk.inj same
    have ledgerMember : inner.1 ∈ support (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId
        bounds (asModeO mode adversary)) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentNative.handler setup codec checks route
        constructed.seed) _ (PqxdhDeploymentNative.initial constructed)
      rw [StateT.run'_eq, support_map]
      exact ⟨inner, innerMember, rfl⟩
    have count := PqxdhDeploymentTargetRange.ledger_count setup.source.crypto codec setup.serverKeyId bounds kind
      (asModeO mode adversary) (budget.cap kind) (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget
        respects kind) Ledger.empty inner.1 ledgerMember
    simpa [Ledger.empty, PqxdhDeploymentTargetRange.classCount] using count

/-- On every outcome of the instrumented experiment of a budget-respecting adversary, a transcript ciphertext collision (`CtCollEvent`, read through `forget`) is the ghost collision of a triple `(k, i, j)` with `k < qCreate` and `i < j < qAccept`. Under the approved Phase 1 and Phase 2 read-back contracts. -/
theorem ctColl_triple (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      (PqxdhDeploymentSecrecy.State KemSK × Ghost)) × A)
    (supported : outcome ∈ support ((gameG setup codec checks route ensureInit identityIndex bounds mode adversary).run
      runtime))
    (event : PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) (forget outcome) = true) :
    ∃ k < budget.create, ∃ j < budget.accept, ∃ i < j, TripleColl k i j outcome := by
  rcases outcome with ⟨_ | ⟨created, output, final⟩, after⟩
  · simp [forget, PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame] at event
  · simp only [forget, PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.observeGame, Option.map_some,
      Option.any_some, ctCollEvent, decide_eq_true_eq] at event
    obtain ⟨k, i, j, coll⟩ := event
    have tracks := tracks_game setup codec checks route ensureInit identityIndex phase1 phase2 bounds mode adversary
      runtime _ supported created output final rfl
    obtain ⟨key, c, keyFound, firstFound, secondFound⟩ := ctColl_logged setup codec checks final tracks k i j coll
    have forgotten : forget (some (created, output, final), after) ∈ support ((PqxdhDeploymentSecrecy.game setup codec
        checks route ensureInit identityIndex bounds mode adversary).run runtime) := by
      rw [PqxdhDeploymentHeadlineCtGhost.game_ghost, support_map]
      exact ⟨_, supported, rfl⟩
    have counts := game_counts setup codec checks route ensureInit identityIndex bounds mode adversary budget respects
      runtime _ forgotten created output final.1 rfl
    have agree := PqxdhDeploymentEligibility.agree_game setup codec checks route ensureInit identityIndex bounds mode
      adversary runtime _ forgotten created output final.1 rfl
    have jBound : j < final.2.encs.length := (List.getElem?_eq_some_iff.mp secondFound).1
    rw [tracks.attempts, acceptCount_classCount] at jBound
    have kBound : k < final.2.keys.length := (List.getElem?_eq_some_iff.mp keyFound).1
    rw [tracks.owners, ← agree.count] at kBound
    have owners := PqxdhDeploymentTargetRange.owners_count final.1.1.transcript
    have creates : budget.cap 1 = budget.create := rfl
    have accepts : budget.cap 3 = budget.accept := rfl
    refine ⟨k, ?_, j, ?_, i, coll.1, created, output, final, rfl, key, c, keyFound, firstFound, secondFound⟩
    · rw [← creates]
      exact lt_of_lt_of_le kBound (owners.trans (counts 1))
    · rw [← accepts]
      exact lt_of_lt_of_le jBound (counts 3)

end Game

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.prefixEnc_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.prefixEnc_input

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.nativeClient_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.nativeClient_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tail_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tail_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tail_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tail_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptEnc_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptEnc_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.nativeAccept_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.nativeAccept_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.buildOracle_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.buildOracle_ciphertext

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.nativeBuild_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.nativeBuild_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.findSome?_snoc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.findSome?_snoc

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptOf_quiet' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptOf_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.buildOf_quiet' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.buildOf_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.bundleOf_quiet' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.bundleOf_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptCount_quiet' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptCount_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptCount_accept' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptCount_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptOf_accept' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptOf_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.buildOf_build' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.buildOf_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.bundleOf_bundle' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.bundleOf_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.alike_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.alike_keys

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_bundle_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_bundle_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_build_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_build_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.kept_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.kept_refl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.kept_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.kept_trans

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.serverStep_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.serverStep_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.beaconStep_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.beaconStep_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.coinSend_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.coinSend_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.finish_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.finish_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.native_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.native_kept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.forward_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.forward_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.quiet_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.quiet_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.secrecy_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.secrecy_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.create_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.create_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.bundle_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.bundle_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.build_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.encs_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.encs_extend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.accept_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.accept_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.tracks_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.carries_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.carries_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.ctColl_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.ctColl_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptCount_classCount' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.acceptCount_classCount

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.game_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.game_counts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.ctColl_triple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace.ctColl_triple
