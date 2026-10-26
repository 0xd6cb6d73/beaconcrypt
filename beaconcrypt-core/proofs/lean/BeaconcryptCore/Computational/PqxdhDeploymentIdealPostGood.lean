-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGoodFinish

/-!
# The CE side of the middle invariant (CE-11b, unit U6, fourth part)

`PqxdhDeploymentIdealPostReduce.activeBranch_of_middle` reduces the active branch of the second compile lemma to a CE side of the invariant of the middle execution: a family of invariants on the local copies and the middle state that implies CE-3's merge invariant and is kept by every compiled step under the middle source handler (`MiddleInv`), and that holds after the selected accept on every outcome of every active cut (`MiddleStart`). This module gives one: `GoodMid`, CE-3's full invariant `PqxdhDeploymentCompileInvariant.Good` on the local copies and the native state of the annotated source state, with the selected accept behind the accept counter.

- Real commands: `real_shape` (a command that is real at the merged state runs its compiled program under the middle source handler as item 2's annotated pool source, the program equation inside `PqxdhDeploymentIdealPostSource.step_real`) and `good_real` (such a command keeps CE-3's invariant, through `PqxdhDeploymentIdealPoolSource.programPool_native` and `PqxdhDeploymentIdealPool.good_step_pool`, and never decreases the accept counter).
- `GoodMid` and `middleInv`: `GoodMid` is a `MiddleInv` under the approved Phase 1 and Phase 2 read-back contracts; the selected raw accept is never reached again, the marked build keeps it (`PqxdhDeploymentIdealPostGoodBuild.good_buildHidden`) and so does owner k's challenge finish (`PqxdhDeploymentIdealPostGoodFinish.good_challenge`).
- The selected accept's footprint: `identityOf_verified` (the identity key read from raw accept bytes that pass the Server's verification is the verified identity), `suffix_verified` (item 2's candidate-free suffix keeps the verified tuple), `accept_token` (the marker representation's token carries the verified tuple's Beacon identity), `tailCE_client_footprint` and `tailCE_tail_footprint` (the marker client and tail under `tailCE` keep the Server's routing record and key ID, advance the session counter by one and publish at most the new session's token, with that Beacon identity), and `acceptAfter_footprint` (the steps after encapsulation through the allocator have the footprint of CE-3's `accept_footprint`).
- `good_of_accept` (CE-3's invariant survives every raw accept with that footprint, the argument of `good_accept` from the footprint alone) and `middleStart`: `GoodMid` holds after the selected accept on every outcome of every active cut, from the cut relation's `Good` (`PqxdhDeploymentIdealCut.CutRel.good`).

These are support facts and invariant preservation under the approved codec contracts. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid compiledMid mergeX RealAt buildHiddenAt finishHiddenAt)
open PqxdhDeploymentCompile (Local compileImpl)
open PqxdhDeploymentCompileInvariant (Good)

/-! ### The real steps of the middle execution -/

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A deployment command that is real at the merged state runs its compiled program under the middle source handler as item 2's annotated pool source on the annotated source state, with the backend advanced on a raw accept and the seed table kept (the program equation inside `PqxdhDeploymentIdealPostSource.step_real`). -/
theorem real_shape (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local) (m : Mid KemSK)
    (real : RealAt t query (mergeX copies m)) :
    (simulateQ (sourceMid setup codec route checks t p created)
      ((compileImpl setup codec route query).run copies)).run m =
      (fun result => (result.1, { m with joint := result.2, backend := PqxdhDeploymentIdealCut.bump query m.backend })) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
          created.server.server.metadata.identityIndex (p.pool t)) ((compileImpl setup codec route query).run copies)).run
          m.joint := by
  by_cases hidden : PqxdhDeploymentCompileBudget.commandKind query = 3 ∨
      PqxdhDeploymentCompileBudget.commandKind query = 4 ∨ PqxdhDeploymentCompileBudget.commandKind query = 5
  · rcases query with coin | command
    · simp [PqxdhDeploymentCompileBudget.commandKind] at hidden
    · cases command with
      | accept raw =>
          have step : (sourceMid setup codec route checks t p created (.inl (.inr (.accept raw)))).run m =
              (PqxdhDeploymentIdealPostSource.realMid setup codec checks t p created
                (.inl (.inr (.accept raw)))).run m := by
            change (if m.backend.2.2.accepts = t.accept then _ else _) = _
            exact ite_eq_right_of_eq_false _ _ (eq_false real)
          exact PqxdhDeploymentIdealPostSource.sourceMid_single setup codec route checks t p created
            (.inl (.inr (.accept raw)))
            (fun answer => (answer, { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) answer }))
            m step
      | build session payload =>
          have notHidden : buildHiddenAt m session = false := by
            unfold buildHiddenAt
            rcases marked : m.backend.2.2.marks with _ | ⟨index, coords⟩
            · rfl
            · have other := real index coords marked
              exact decide_eq_false other
          have step : (sourceMid setup codec route checks t p created (.inl (.inr (.build session payload)))).run m =
              (PqxdhDeploymentIdealPostSource.realMid setup codec checks t p created
                (.inl (.inr (.build session payload)))).run m := by
            change (if buildHiddenAt m session then _ else _) = _
            rw [notHidden]
            rfl
          exact PqxdhDeploymentIdealPostSource.sourceMid_single setup codec route checks t p created
            (.inl (.inr (.build session payload)))
            (fun answer => (answer, { copies with
              log := PqxdhDeploymentCompile.logReply copies.log (.build session payload) answer })) m step
      | finish owner raw =>
          have notHidden : finishHiddenAt t m owner = false := by
            unfold finishHiddenAt
            have merged := PqxdhDeploymentIdealPostSource.initSentAt_merge copies
              (PqxdhRegistrationJointSchedule.source m.joint).owners owner
            have other : ¬ (m.backend.2.2.active = true ∧ owner = t.kem.val ∧
                PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners owner =
                  true) := by
              rw [← merged]
              exact real
            exact decide_eq_false other
          have step : (sourceMid setup codec route checks t p created (.inl (.inr (.finish owner raw)))).run m =
              (PqxdhDeploymentIdealPostSource.realMid setup codec checks t p created
                (.inl (.inr (.finish owner raw)))).run m := by
            change (if finishHiddenAt t m owner then _ else _) = _
            rw [notHidden]
            rfl
          exact PqxdhDeploymentIdealPostSource.sourceMid_single setup codec route checks t p created
            (.inl (.inr (.finish owner raw)))
            (fun answer => (answer, { copies with
              log := PqxdhDeploymentCompile.logReply copies.log (.finish owner raw) answer })) m step
      | _ => simp [PqxdhDeploymentCompileBudget.commandKind] at hidden
  · have other : PqxdhDeploymentCompileBudget.commandKind query ≠ 3 ∧
        PqxdhDeploymentCompileBudget.commandKind query ≠ 4 ∧ PqxdhDeploymentCompileBudget.commandKind query ≠ 5 := by
      omega
    rw [PqxdhDeploymentIdealPool.simulateQ_congr_none (sourceMid setup codec route checks t p created)
      (PqxdhDeploymentIdealPostSource.realMid setup codec checks t p created) PqxdhDeploymentIdealPostSource.HiddenKind
      (PqxdhDeploymentIdealPostSource.sourceMid_other setup codec route checks t p created) _
      (PqxdhDeploymentIdealPostSource.compile_noHidden setup codec route query copies other)]
    have noAccept : ((compileImpl setup codec route query).run copies).IsQueryBoundP
        (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
      have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) (.inl 3) query copies
      have zero : PqxdhDeploymentCompileBudget.cost (.inl 3) (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
        rcases query with coin | command
        · rfl
        · cases command <;> simp [PqxdhDeploymentCompileBudget.commandKind] at other ⊢ <;> rfl
      rwa [zero] at bound
    rw [PqxdhDeploymentIdealPostSource.realMid_frame setup codec checks t p created _ noAccept m]
    have kept : PqxdhDeploymentIdealCut.bump query m.backend = m.backend := by
      rcases query with coin | command
      · rfl
      · cases command <;> first | rfl | simp [PqxdhDeploymentCompileBudget.commandKind] at other
    rw [kept]

/-- A deployment command that is real at the merged state keeps CE-3's invariant on the local copies and the native state of the annotated source state (`PqxdhDeploymentIdealPool.good_step_pool` through the erasure `PqxdhDeploymentIdealPoolSource.programPool_native`), under the approved codec contracts, and never decreases the accept counter. -/
theorem good_real (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (query : PqxdhDeploymentInterface.Spec.Domain)
    (copies : Local) (m : Mid KemSK) (real : RealAt t query (mergeX copies m))
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (result : PqxdhDeploymentInterface.Spec.Range query × (Local × Mid KemSK))
    (supported : result ∈ support ((compiledMid setup codec route checks t p created query).run (copies, m))) :
    Good setup codec result.2.1 (PqxdhRegistrationJointSchedule.source result.2.2.joint) ∧
      m.backend.2.2.accepts ≤ result.2.2.backend.2.2.accepts := by
  change result ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((compileImpl setup codec route query).run copies)).run m) at supported
  rw [real_shape setup codec route checks t p created query copies m real, Functor.map_map, support_map] at supported
  obtain ⟨x, xMember, rfl⟩ := supported
  have pooled : (x.1.1, (x.1.2, PqxdhRegistrationJointSchedule.source x.2)) ∈
      support ((PqxdhDeploymentIdealPool.compiledPool setup codec checks route created.seed (p.pool t) query).run
        (copies, PqxdhRegistrationJointSchedule.source m.joint)) := by
    change _ ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhDeploymentIdealPool.revealPool setup codec checks created.seed (p.pool t))
        ((compileImpl setup codec route query).run copies)).run (PqxdhRegistrationJointSchedule.source m.joint))
    rw [← PqxdhDeploymentIdealPoolSource.programPool_native setup codec checks created.seed
      created.server.server.metadata.identityIndex (p.pool t), Functor.map_map, support_map]
    exact ⟨x, xMember, rfl⟩
  refine ⟨PqxdhDeploymentIdealPool.good_step_pool setup codec checks route created.seed (p.pool t) phase1 phase2 query
    copies _ good _ pooled, ?_⟩
  rcases query with coin | command
  · exact le_refl _
  · cases command
    all_goals first | exact le_refl _ | exact Nat.le_succ _

end Real

/-! ### The CE side of the middle invariant -/

section Invariant
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The CE side of the invariant of the middle execution: CE-3's invariant on the local copies and the native state of the annotated source state, with the selected accept behind the accept counter. -/
def GoodMid {count : ℕ} (t : Target count) (copies : Local) (m : Mid KemSK) : Prop :=
  Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint) ∧ t.accept < m.backend.2.2.accepts

/-- `GoodMid` is a CE side of the middle invariant (`PqxdhDeploymentIdealPostReduce.MiddleInv`), under the approved codec contracts: it implies CE-3's merge invariant, real commands keep it (`good_real`), the selected raw accept is never reached again, the marked build keeps it (`PqxdhDeploymentIdealPostGoodBuild.good_buildHidden`) and owner k's challenge finish keeps it (`PqxdhDeploymentIdealPostGoodFinish.good_challenge`). -/
theorem middleInv (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) {count : ℕ} (t : Target count)
    (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit) :
    PqxdhDeploymentIdealPostReduce.MiddleInv setup codec route checks t p created (GoodMid setup codec t) where
  sound copies m inv := PqxdhDeploymentCompileInvariant.good_inv setup codec copies _ inv.1
  preserved query copies m inv result supported := by
    by_cases real : RealAt t query (mergeX copies m)
    · obtain ⟨good, le⟩ := good_real setup codec route checks t p created phase1 phase2 query copies m real inv.1 result
        supported
      exact ⟨good, lt_of_lt_of_le inv.2 le⟩
    · rcases query with coin | command
      · exact absurd trivial real
      · cases command with
        | accept raw => exact absurd (Nat.ne_of_gt inv.2) real
        | build session payload =>
            have hidden : buildHiddenAt m session = true := by
              simp only [RealAt, not_forall, not_not] at real
              obtain ⟨index, coords, marked, same, pending⟩ := real
              subst same
              unfold buildHiddenAt
              rw [show m.backend.2.2.marks = some (index, coords) from marked]
              exact decide_eq_true ⟨rfl, pending⟩
            obtain ⟨good, accepts⟩ := PqxdhDeploymentIdealPostGoodBuild.good_buildHidden setup codec route checks t p
              created phase2 session payload copies m hidden inv.1 result supported
            exact ⟨good, accepts ▸ inv.2⟩
        | finish owner raw =>
            have hidden : finishHiddenAt t m owner = true := by
              have challenge := not_not.mp real
              unfold finishHiddenAt
              refine decide_eq_true ⟨challenge.1, challenge.2.1, ?_⟩
              have merged := PqxdhDeploymentIdealPostSource.initSentAt_merge copies
                (PqxdhRegistrationJointSchedule.source m.joint).owners owner
              rw [← merged]
              exact challenge.2.2
            obtain ⟨good, accepts⟩ := PqxdhDeploymentIdealPostGoodFinish.good_challenge setup codec route checks t p
              created owner raw copies m hidden inv.1 result supported
            exact ⟨good, accepts ▸ inv.2⟩
        | _ => exact absurd trivial real

end Invariant

/-! ### The selected accept's footprint -/

section Accept
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealSteps (tailCE liftS)

/-- The identity key read from raw accept bytes that pass the Server's verification is the verified identity. -/
theorem identityOf_verified (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (accepted : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value) :
    PqxdhDeploymentCompile.identityOf codec raw = some (PqxdhRootTableInitialization.rootArray value.identity) := by
  unfold PqxdhRegistrationJointRawSignatures.verified at accepted
  dsimp at accepted
  simp only [Option.bind_eq_some_iff] at accepted
  obtain ⟨reader, read, encoded, encodedField, identity, parsedIdentity, accepted⟩ := accepted
  split at accepted
  · cases accepted
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at accepted
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := accepted
    simp only [PqxdhDeploymentCompile.identityOf, read, encodedField, parsedIdentity, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]

/-- Item 2's candidate-free suffix returns prepared inputs carrying the verified tuple it was given, under any interpreter. -/
theorem suffix_verified {E Shared σ ι' : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (StateT σ (OracleComp spec')))
    (verified : PqxdhServerRootPreparation.Verified Reader) (ephemeral : PqxdhServerRootPreparation.Ephemeral E)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (state : σ) (prepared : Option (PqxdhRegistrationJointKemOpaqueSuffix.Prepared Reader E Shared) × σ)
    (member : prepared ∈ support ((simulateQ impl
      (PqxdhRegistrationJointKemOpaqueSuffix.program verified ephemeral ciphertext token)).run state)) :
    ∀ input, prepared.1 = some input → input.verified = verified := by
  have inner : prepared.1 ∈ support (PqxdhRegistrationJointKemOpaqueSuffix.program verified ephemeral ciphertext token) := by
    apply OracleComp.support_simulateQ_run'_subset impl _ state
    rw [StateT.run'_eq, support_map]
    exact ⟨prepared, member, rfl⟩
  intro input found
  rw [found, PqxdhRegistrationJointKemOpaqueSuffix.program, support_map] at inner
  obtain ⟨original, originalMember, mapped⟩ := inner
  rcases original with _ | original
  · cases mapped
  · simp only [Option.map_some, Option.some.injEq] at mapped
    subst mapped
    exact (PqxdhRegistrationJointKemCollected.after_fields verified ephemeral _ original originalMember).1

/-- The marker representation's accepted token carries the Beacon identity of its verified tuple. -/
theorem accept_token {E : Type} (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueSuffix.Prepared Reader E PqxdhBeaconPhase2Preparation.Word32)
    (final : beaconcrypt_core.pqxdh.ServerState) (token : beaconcrypt_core.pqxdh.PendingServerRegistration)
    (accepted : PqxdhRegistrationJointKemOpaqueCore.accept control binding input = .ok (.Ok (final, token))) :
    token.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray input.verified.identity := by
  rw [PqxdhRegistrationJointKemOpaqueCore.accept, PqxdhRegistrationJointKemOpaqueCore.cleared_shape] at accepted
  split_ifs at accepted
  · simp only [RustM.ok.injEq] at accepted
    injection accepted with accepted
    injection accepted with _ accepted
    subst accepted
    rfl
  · simp at accepted

/-- The marker client under `tailCE` with a challenge-marked input, from any state: it changes only the consumed registrations of the game state, and a returned token carries the Beacon identity of the input's verified tuple. -/
theorem tailCE_client_footprint (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) (marker : input.shared = .challenge)
    (s : PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord))
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) ×
      (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
      (PqxdhRegistrationJointKemOpaqueClient.client control binding input))).run s)) :
    (∃ consumed, result.2.1.2 = { s.1.2 with server := { s.1.2.server with consumed := consumed } }) ∧
      ∀ token, result.1 = RustM.ok (some token) →
        token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray input.verified.identity := by
  have auxStep : ∀ (query : PqxdhServerRelatedRootConsumer.Auxiliary) (st : PqxdhServerAuthNative.NativeState KemSK ×
      Option (ℕ × Coord)),
      (match query with
        | .consume _ => False
        | _ => True) →
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr query) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st = pure ((), st) := by
    intro query st kind
    cases query <;> simp only at kind <;> rfl
  have consumeStep : ∀ (rid : beaconcrypt_core.pqxdh.RegistrationId)
      (st : PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr (.consume rid)) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        pure ((), ((st.1.1, { st.1.2 with server := { st.1.2.server with
          consumed := st.1.2.server.consumed ++ [PqxdhRefinement.absBytes rid.bytes] } }), st.2)) := by
    intro rid st
    rfl
  have rootStep : ∀ st : PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inl input) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        (fun _ => (PqxdhServerAuthEntryFactor.sentinel, (st.1, some (index, PqxdhDeploymentIdealSteps.coordsOf input)))) <$>
          (PqxdhDeploymentIdealSlots.SlotSpec.query (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) :
            OracleComp PqxdhDeploymentIdealSlots.SlotSpec _) := by
    intro st
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      PqxdhRegistrationJointKemOpaqueTail.forward]
    simp only [tailCE, StateT.run, marker, map_eq_bind_pure_comp]
    rfl
  unfold PqxdhRegistrationJointKemOpaqueClient.client at member
  simp only [simulateQ_bind, StateT.run_bind, auxStep .eraseShared s trivial, pure_bind] at member
  split at member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨⟨s.1.2.server.consumed, rfl⟩, fun token same => by cases same⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨⟨s.1.2.server.consumed, rfl⟩, fun token same => by cases same⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨⟨s.1.2.server.consumed, rfl⟩, fun token same => by cases same⟩
  · rename_i final pending accepted
    simp only [simulateQ_bind, StateT.run_bind, rootStep, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨_, _, member⟩ := member
    simp only [auxStep .eraseInput _ trivial, consumeStep, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, rfl, _, rfl, rfl⟩ := member
    refine ⟨⟨_, rfl⟩, fun token same => ?_⟩
    simp only [RustM.ok.injEq, Option.some.injEq] at same
    subst same
    exact accept_token control binding input final pending accepted

/-- The marker tail under `tailCE` (`PqxdhDeploymentIdealKeymatch.tailCE_tail` with the Server fields): from the given game state it keeps the Server's routing record and key ID, advances the session counter by one, changes no other session's pending token and no token at all without a reply, and a returned session is the counter of the given state and holds a token with the Beacon identity of the collected input's verified tuple. -/
theorem tailCE_tail_footprint (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge)
    (s : PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord))
    (result : Option ℕ × (PqxdhServerAuthNative.NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run s)) :
    result.2.1.2.server.server = state.server.server ∧
      result.2.1.2.server.identityKeyId = state.server.identityKeyId ∧
      result.2.1.2.sessions = state.sessions + 1 ∧
      (∀ session, session ≠ state.sessions → result.2.1.2.pending session = state.pending session) ∧
      (result.1 = none → result.2.1.2.pending = state.pending) ∧
      (∀ session, result.1 = some session → session = state.sessions ∧ ∃ input token, collected.1 = some input ∧
        result.2.1.2.pending session = some token ∧
        token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray input.verified.identity) := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail at member
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at member
  obtain ⟨installed, installedMember, member⟩ := member
  change installed ∈ support ((fun r => (r.1, (r.2, s.2))) <$> liftS ((PqxdhRegistrationJointKemOpaqueTail.mutation
    (.install _)).run s.1)) at installedMember
  simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
    PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState, StateT.run, support_pure,
    Set.image_singleton, Set.mem_singleton_iff] at installedMember
  subst installedMember
  rcases found : collected.1 with _ | input
  · simp only [found, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun session none => by cases none⟩
  · simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨returned, returnedMember, member⟩ := member
    obtain ⟨⟨consumed, stateEq⟩, tokens⟩ := tailCE_client_footprint hmac index state.server.control
      ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input (marker input found) _
      returned returnedMember
    rcases outcome : returned.1 with (_ | token) | _ | _ <;> simp only [outcome] at member
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [stateEq]
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun session none => by cases none⟩
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨published, publishedMember, rfl⟩ := member
      change published ∈ support ((fun r => (r.1, (r.2, returned.2.2))) <$> liftS
        ((PqxdhRegistrationJointKemOpaqueTail.mutation (.publish _ _)).run returned.2.1)) at publishedMember
      simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
        PqxdhServerAuthNative.nativeModify, PqxdhServerAuthNative.localState, StateT.run, support_pure,
        Set.image_singleton, Set.mem_singleton_iff] at publishedMember
      subst publishedMember
      rw [stateEq]
      refine ⟨rfl, rfl, rfl, fun other different => Function.update_of_ne different _ _, (fun absent => by cases absent),
        fun session same => ?_⟩
      simp only [Option.some.injEq] at same
      subst same
      exact ⟨rfl, input, token, rfl, Function.update_self .., tokens token outcome⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [stateEq]
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun session none => by cases none⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rw [stateEq]
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun session none => by cases none⟩

/-- The selected accept's steps after encapsulation through the allocator, from any native state (CE-3's `PqxdhDeploymentCompileFootprint.accept_footprint` for `PqxdhDeploymentIdealActive.acceptAfter`): they keep the Server's routing record and key ID, advance the session counter by one, change no other session's pending token and no token at all without a reply, and a returned session is the counter before the call and holds a token with the Beacon identity of the verified tuple. -/
theorem acceptAfter_footprint (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (native : PqxdhServerAuthNative.NativeState KemSK)
    (slots : PqxdhDeploymentIdealPostSim.SlotState) (w : PqxdhDeploymentIdealPostItemRun.AcceptRun KemSK)
    (member : w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge value ephemeral consumed
        logged).run native)).run slots)) :
    w.1.2.2.server.server = native.2.server.server ∧ w.1.2.2.server.identityKeyId = native.2.server.identityKeyId ∧
      w.1.2.2.sessions = native.2.sessions + 1 ∧
      (∀ session, session ≠ native.2.sessions → w.1.2.2.pending session = native.2.pending session) ∧
      (w.1.1.1.1 = none → w.1.2.2.pending = native.2.pending) ∧
      (∀ session, w.1.1.1.1 = some session → session = native.2.sessions ∧ ∃ token,
        w.1.2.2.pending session = some token ∧
        token.pending.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray value.identity) := by
  have outer : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge value ephemeral
      consumed logged).run native) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ slots
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  change w.1 ∈ support (liftS _ >>= _) at outer
  rw [mem_support_bind_iff] at outer
  obtain ⟨prepared, preparedMember, outer⟩ := outer
  rw [liftS, support_liftComp] at preparedMember
  have marker := PqxdhDeploymentIdealKeymatch.program_marker _ value ephemeral
    (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge consumed prepared preparedMember
  have verified := suffix_verified _ value ephemeral (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge
    consumed prepared preparedMember
  rw [mem_support_bind_iff] at outer
  obtain ⟨answer, answerMember, outer⟩ := outer
  rw [support_pure, Set.mem_singleton_iff] at outer
  obtain ⟨server, keyId, sessions, others, rejected, accepted⟩ := tailCE_tail_footprint setup.hmac native.2.sessions
    setup.serverKeyId (setup.joint.publicKeys seed) native.2 prepared marker (native, none) answer answerMember
  rw [outer]
  refine ⟨server, keyId, sessions, others, rejected, fun session found => ?_⟩
  obtain ⟨same, input, token, inputFound, stored, identity⟩ := accepted session found
  exact ⟨same, token, stored, by rw [identity, verified input inputFound]⟩

end Accept

/-! ### The start of the CE side after the selected accept -/

section Start
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- CE-3's invariant survives every raw accept with the footprint of `PqxdhDeploymentCompileFootprint.accept_footprint` that keeps the owners, with the reply logged (the argument of CE-3's `PqxdhDeploymentCompileInvariant.good_accept`, from the footprint alone). -/
theorem good_of_accept (raw : Pqxdh.Bytes) (copies : Local) (native after : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) (reply : Option ℕ) (owners : after.owners = native.owners)
    (server : after.shared.2.server.server = native.shared.2.server.server)
    (keyId : after.shared.2.server.identityKeyId = native.shared.2.server.identityKeyId)
    (sessions : after.shared.2.sessions = native.shared.2.sessions + 1)
    (others : ∀ session, session ≠ native.shared.2.sessions →
      after.shared.2.pending session = native.shared.2.pending session)
    (rejected : reply = none → after.shared.2.pending = native.shared.2.pending)
    (accepted : ∀ session, reply = some session → session = native.shared.2.sessions ∧ ∃ token,
      after.shared.2.pending session = some token ∧
      PqxdhDeploymentCompile.identityOf codec raw = some token.pending.beacon_identity_public_key) :
    Good setup codec { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) reply } after := by
  have freshLog : copies.log.accepts native.shared.2.sessions = none := by
    cases logged : copies.log.accepts native.shared.2.sessions with
    | none => rfl
    | some old => exact absurd (good.accepts _ old logged) (Nat.lt_irrefl _)
  rcases reply with _ | handle
  · have pending := rejected rfl
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keyId]; exact good.keyId
    · intro kid current copied
      rw [server]
      exact good.installed kid current copied
    · rw [server]; exact good.serverVisible
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro session token found
      rw [pending] at found
      obtain ⟨below, logged⟩ := good.pending session token found
      exact ⟨by rw [sessions]; omega, logged⟩
    · intro session logged found
      have below := good.accepts session logged found
      rw [sessions]
      omega
  · obtain ⟨handleEq, token, stored, identified⟩ := accepted handle rfl
    subst handleEq
    simp only [PqxdhDeploymentCompile.logReply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keyId]; exact good.keyId
    · intro kid current copied
      rw [server]
      exact good.installed kid current copied
    · intro kid peer found
      rw [server] at found ⊢
      exact PqxdhDeploymentCompileInvariant.peerView_accept codec copies.log _ raw freshLog kid _
        (good.serverVisible kid peer found)
    · rw [owners]; exact good.count
    · intro index current copied
      rw [owners]
      exact good.copied index current copied
    · rw [owners]; exact good.owners
    · intro session found_token found
      by_cases same : session = native.shared.2.sessions
      · subst same
        rw [stored, Option.some.injEq] at found
        subst found
        refine ⟨by rw [sessions]; omega, raw, Function.update_self .., identified⟩
      · rw [others session same] at found
        obtain ⟨below, old, logged, oldIdentified⟩ := good.pending session found_token found
        exact ⟨by rw [sessions]; omega, old, by simp only [Function.update_of_ne same]; exact logged, oldIdentified⟩
    · intro session logged found
      rw [sessions]
      by_cases same : session = native.shared.2.sessions
      · omega
      · simp only [Function.update_of_ne same] at found
        have below := good.accepts session logged found
        omega

end Start

section Begin
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- `GoodMid` holds after the selected accept on every outcome of every active cut (`PqxdhDeploymentIdealPostReduce.MiddleStart`): the cut's relation carries CE-3's invariant (`PqxdhDeploymentIdealCut.CutRel.good`), the steps after encapsulation have the footprint of a raw accept (`acceptAfter_footprint`) whose token carries the identity key read from the accept bytes (`identityOf_verified`), and the accept counter is one past the selected ordinal. -/
theorem middleStart {A : Type} (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (p : Params KemSK budget.create) :
    PqxdhDeploymentIdealPostReduce.MiddleStart (Reader := Reader) setup codec route checks ensureInit bounds mode adversary
      budget g runtime p (fun _ => GoodMid setup codec (Target.ofCE budget g)) := by
  intro born _ created _ reached _ rel raw next _ value verified _ pre _ ephemeral _ w member
  refine ⟨?_, Nat.lt_succ_self _⟩
  obtain ⟨server, keyId, sessions, others, rejected, accepted⟩ := acceptAfter_footprint setup codec checks created.seed
    p.challenge value ephemeral pre.2 pre.1.2 reached.2.shared _ w member
  exact good_of_accept setup codec raw reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)
    ⟨w.1.2, (PqxdhRegistrationJointSchedule.source reached.2).owners⟩ rel.base.good w.1.1.1.1 rfl server keyId sessions
    others rejected (fun session found => by
      obtain ⟨same, token, stored, identity⟩ := accepted session found
      exact ⟨same, token, stored, by rw [identity]; exact identityOf_verified setup codec checks raw value verified⟩)

end Begin

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.real_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.real_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.good_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.good_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.middleInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.middleInv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.identityOf_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.identityOf_verified

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.suffix_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.suffix_verified

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.accept_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.accept_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.tailCE_client_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.tailCE_client_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.tailCE_tail_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.tailCE_tail_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.acceptAfter_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.acceptAfter_footprint

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.good_of_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.good_of_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.middleStart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostGood.middleStart
