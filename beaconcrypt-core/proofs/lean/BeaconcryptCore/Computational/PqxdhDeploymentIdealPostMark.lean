-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealActive

/-!
# The final mark of the active branch (CE-11b, unit U6, second part)

`PqxdhDeploymentIdealActive` reduces the second compile lemma of CE-11b to its active branch (`ActiveBranch`), whose CE side `activeCE` reads the decision together with whether the selected session is marked at the end of the run. Item 2's decision reads instead whether the selected accept returned a session (`PqxdhRegistrationJointAcceptCutTag.accepted`). This module shows that on the CE side the two agree: the selected accept from the steps after encapsulation marks the session exactly when it returns one, and no later step changes the mark.

- `tailCE_client_mark` and `tailCE_tail_mark` are the converses of `PqxdhDeploymentIdealKeymatch.tailCE_client` and `tailCE_tail` (finding 1 of the review of the first part of unit U6): under `tailCE`, item 2's marker client either leaves the mark unchanged or succeeds with a token, and item 2's marker tail either leaves the mark unchanged or returns a session.
- `acceptAfter_mark`: the selected accept from the steps after encapsulation (`PqxdhDeploymentIdealActive.acceptAfter`) is active, and it sets the mark exactly when it returns a session (from an unmarked state, with `tailCE_tail` for the other direction and `PqxdhDeploymentIdealKeymatch.program_marker` for the challenge marker of the prepared input).
- `activeCE_reply`: `activeCE` equals `activeReply`, the same computation with the decision reading whether the selected accept returned a session in place of the final mark (with `PqxdhDeploymentIdealKeymatch.run_settled`: once the accept counter is beyond the selected ordinal no step changes the mark).

These are support facts and one program equality. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthNative (NativeState)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (tailCE)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The marker client under `tailCE`: either the mark is unchanged or the client succeeded with a token. -/
theorem tailCE_client_mark (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader)
    (marker : input.shared = .challenge) (s : NativeState KemSK × Option (ℕ × Coord))
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
      (PqxdhRegistrationJointKemOpaqueClient.client control binding input))).run s)) :
    result.2.2 = s.2 ∨ ∃ token, result.1 = RustM.ok (some token) := by
  have auxStep : ∀ (query : PqxdhServerRelatedRootConsumer.Auxiliary) (st : NativeState KemSK × Option (ℕ × Coord)),
      (match query with
        | .consume _ => False
        | _ => True) →
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr query) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st = pure ((), st) := by
    intro query st kind
    cases query <;> simp only at kind <;> rfl
  have consumeStep : ∀ (rid : beaconcrypt_core.pqxdh.RegistrationId) (st : NativeState KemSK × Option (ℕ × Coord)),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr (.consume rid)) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        pure ((), ((st.1.1, { st.1.2 with server := { st.1.2.server with
          consumed := st.1.2.server.consumed ++ [absBytes rid.bytes] } }), st.2)) := by
    intro rid st
    rfl
  have rootStep : ∀ st : NativeState KemSK × Option (ℕ × Coord),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inl input) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        (fun _ => (PqxdhServerAuthEntryFactor.sentinel, (st.1, some (index, PqxdhDeploymentIdealSteps.coordsOf input)))) <$>
          (SlotSpec.query (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) : OracleComp SlotSpec _) := by
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
    exact Or.inl rfl
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact Or.inl rfl
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact Or.inl rfl
  · simp only [simulateQ_bind, StateT.run_bind, rootStep, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨_, _, member⟩ := member
    simp only [auxStep .eraseInput _ trivial, consumeStep, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, rfl, _, rfl, rfl⟩ := member
    exact Or.inr ⟨_, rfl⟩

/-- The marker tail under `tailCE`: either the mark is unchanged or a session is returned. -/
theorem tailCE_tail_mark (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge)
    (s : NativeState KemSK × Option (ℕ × Coord))
    (result : Option ℕ × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run s)) :
    result.2.2 = s.2 ∨ result.1.isSome = true := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail at member
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at member
  obtain ⟨installed, installedMember, member⟩ := member
  change installed ∈ support ((fun r => (r.1, (r.2, s.2))) <$> PqxdhDeploymentIdealSteps.liftS
    ((PqxdhRegistrationJointKemOpaqueTail.mutation (.install _)).run s.1)) at installedMember
  simp only [support_map, support_liftComp, PqxdhRegistrationJointKemOpaqueTail.mutation,
    PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState, StateT.run, support_pure,
    Set.image_singleton, Set.mem_singleton_iff] at installedMember
  subst installedMember
  rcases found : collected.1 with _ | input
  · simp only [found, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact Or.inl rfl
  · simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨returned, returnedMember, member⟩ := member
    have client := tailCE_client_mark hmac index state.server.control
      ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input (marker input found) _
      returned returnedMember
    rcases outcome : returned.1 with (_ | token) | _ | _ <;> simp only [outcome] at member
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rcases client with same | ⟨token, bad⟩
      · exact Or.inl same
      · rw [outcome] at bad
        cases bad
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨_, _, rfl⟩ := member
      exact Or.inr rfl
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rcases client with same | ⟨token, bad⟩
      · exact Or.inl same
      · rw [outcome] at bad
        cases bad
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      rcases client with same | ⟨token, bad⟩
      · exact Or.inl same
      · rw [outcome] at bad
        cases bad

section After
open PqxdhServerRootPreparation (Verified)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The selected accept from the steps after encapsulation (`PqxdhDeploymentIdealActive.acceptAfter`) is active, and it marks the session exactly when it returns one. -/
theorem acceptAfter_mark (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (value : Verified Reader) (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes) (s : NativeState KemSK)
    (r : PqxdhDeploymentIdealSteps.AcceptOut × NativeState KemSK)
    (member : r ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge value ephemeral
      consumed logged).run s)) :
    r.1.2.1 = true ∧ (r.1.2.2.isSome = r.1.1.1.isSome) := by
  change r ∈ support (do
    let prepared ← PqxdhDeploymentIdealSteps.liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec
      checks seed) (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := PqxdhBeaconPhase2Preparation.Word32) value
        ephemeral (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge)).run consumed)
    let answer ← (simulateQ (tailCE setup.hmac s.2.sessions)
      (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared)).run
        (s, none)
    pure (((answer.1, logged), (true, answer.2.2)), answer.2.1)) at member
  rw [mem_support_bind_iff] at member
  obtain ⟨prepared, preparedMember, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨answer, answerMember, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  rw [support_liftComp] at preparedMember
  have marker := PqxdhDeploymentIdealKeymatch.program_marker (PqxdhDeploymentIdealSteps.prefixNative setup codec checks
    seed) value _ _ _ _ prepared preparedMember
  have forward := PqxdhDeploymentIdealKeymatch.tailCE_tail setup.hmac s.2.sessions setup.serverKeyId
    (setup.joint.publicKeys seed) s.2 prepared marker (s, none) answer answerMember
  have converse := tailCE_tail_mark setup.hmac s.2.sessions setup.serverKeyId (setup.joint.publicKeys seed) s.2
    prepared marker (s, none) answer answerMember
  refine ⟨rfl, ?_⟩
  change answer.2.2.isSome = answer.1.isSome
  rcases returned : answer.1 with _ | session
  · rcases converse with same | some
    · rw [same]
      rfl
    · rw [returned] at some
      cases some
  · rw [(forward.2 session returned).2]
    rfl

end After

/-! ### The final mark of the active branch -/

section Reply
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (cutState)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The CE side of an active selected accept at the cut (`PqxdhDeploymentIdealActive.activeCE`) with the decision reading whether the selected accept returned a session in place of the final mark. -/
noncomputable def activeReply {Y : Type} (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool) (base : PqxdhDeploymentNative.State KemSK)
    (next : Option ℕ → OracleComp PqxdhDeploymentInterface.Spec Y) (value : Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) : ProbComp Bool :=
  (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.selectedStep (PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed
        p.challenge value ephemeral consumed logged)).run (PqxdhDeploymentIdealSlots.detach (cutState t created base)))).run
      ((cutState t created base).backend.2.1, (cutState t created base).backend.1) >>= fun r =>
    (fun outcome => decision (outcome.1, outcome.2.base, r.1.1.isSome)) <$>
      (simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route
        (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p created)) (next r.1.1)).run
        (PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)

/-- On the CE side of the active branch the final mark is whether the selected accept returned a session: the accept marks the session exactly when it returns one (`acceptAfter_mark`), and no later step changes the mark (`PqxdhDeploymentIdealKeymatch.run_settled`). -/
theorem activeCE_reply {Y : Type} (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool) (base : PqxdhDeploymentNative.State KemSK)
    (next : Option ℕ → OracleComp PqxdhDeploymentInterface.Spec Y) (value : Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) :
    PqxdhDeploymentIdealActive.activeCE setup codec route checks t p created decision base next value ephemeral consumed
        logged =
      activeReply setup codec route checks t p created decision base next value ephemeral consumed logged := by
  unfold PqxdhDeploymentIdealActive.activeCE activeReply
  rw [bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun r member => ?_
  have produced : r.1 ∈ support ((PqxdhDeploymentIdealActive.selectedStep (PqxdhDeploymentIdealActive.acceptAfter
      setup codec checks created.seed p.challenge value ephemeral consumed logged)).run
        (PqxdhDeploymentIdealSlots.detach (cutState t created base))) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      ((cutState t created base).backend.2.1, (cutState t created base).backend.1)
    rw [StateT.run'_eq, support_map]
    exact ⟨r, member, rfl⟩
  unfold PqxdhDeploymentIdealActive.selectedStep at produced
  rw [StateT.run, support_map] at produced
  obtain ⟨inner, innerMember, same⟩ := produced
  obtain ⟨_, mark⟩ := acceptAfter_mark setup codec checks created.seed p.challenge value ephemeral consumed logged _
    inner innerMember
  have marks : r.1.2.backend.marks.isSome = r.1.1.isSome := by
    rw [← same]
    exact mark
  have accepts : t.accept < r.1.2.backend.accepts := by
    rw [← same]
    simp [PqxdhDeploymentIdealSlots.detach, cutState, PqxdhDeploymentIdealCut.withAccepts]
  apply PqxdhDeploymentKemTransfer.map_support_congr
  intro outcome outcomeMember
  have settled := PqxdhDeploymentIdealKeymatch.run_settled setup codec route checks t p created (next r.1.1)
    (PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2) accepts outcome outcomeMember
  simp only [PqxdhDeploymentIdealBranch.marked, settled]
  change decision (outcome.1, outcome.2.base, (r.1.2.backend.marks).isSome) = _
  rw [marks]

end Reply

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.tailCE_client_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.tailCE_client_mark

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.tailCE_tail_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.tailCE_tail_mark

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.acceptAfter_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.acceptAfter_mark

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.activeCE_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostMark.activeCE_reply
