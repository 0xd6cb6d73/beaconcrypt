-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer

/-! CE-9b for the LQ-F later game: the two-sided form of theorem T4 for the logged source (`PqxdhDeploymentLaterServerBridge.actual_le_real`) and the two-sided per-target KEM transfer of the later-quantum confidentiality game. The logged T4 has the proof of `KemRawBridge.actual_le_real` with the logged definitions, so it discards the same runs, and its reverse chain (`real_le_run`, `real_le_commands`, `real_le_actual`) is that of `PqxdhDeploymentKemTwoSided` with the logged command compiler, the logged exposure (`LaterServerBridge.exposeAt_tag`, `scanned_map`), the logged selected-first game (`LaterServerInitialized.actual_source_first`) and the generic KEM hop for scanned programs (`LaterServerKemHop.sourceReal`); the stopped-router facts `PqxdhDeploymentKemTwoSided.stopped_good` and `Completed` are reused unchanged. Hence the logged T4 is an equality for decisions that, on the support of the logged actual execution, imply `KeyMatchFinal` whenever `Decided ∧ GoodKem` holds (`actual_eq_real`, `decided_eq_real`), with the same unconditional defect bound (`real_le_actual_add`, `actual_real_close`). `hop_close` is the two-sided logged KEM hop (`LaterServerKemHop.certified_advantage` with T6 for the logged source, `LaterServerOpaque.branch_opaque`). The per-target decision of the LQ-F game is in the class (`decision_implies_server`, from `LaterServerTransfer.keymatch_server` with `Phase1ReadBack` and `LaterServerTrace.goodKem_later`), so its defect vanishes (`defect_zero_server`), steps 9.1-9.2 are one equality (`eligible_server_real`), and the transfer is two-sided (`kem_transfer_server_two_sided`, `kem_transfer_server_lower`, `kem_transfer_server_sum_two_sided`) with the terms of `kem_transfer_server`. The event may read the post-run adversary's output, which depends on the post-run reveal; the statements are confidentiality statements, as in `LaterServerTransfer`, and no authentication is claimed. Premises: the logged T4's creation cap for the generic statements; `Phase1ReadBack`, `Phase2ReadBack`, `FunctionalDecapsulation` and the run-phase budget for the game statements. No assumption, contract or advantage term is added, and no existing statement changes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointAcceptCutTag (Tag accepted decideTag)
open PqxdhRegistrationJointKemRawBridge (Decided GoodKem KeyMatchFinal)
open PqxdhRegistrationJointKemRawNatural (mapOutcome cutMap)
open PqxdhDeploymentKemTwoSided (Completed stopped_good chance_ext chance_le_add chance_eq_zero toReal_close
  le_add_of_close abs_sum_sub_le)
open PqxdhDeploymentLaterServerSource (Spec)
open PqxdhDeploymentLaterServerCommands (tag commands)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

section Generic

set_option backward.isDefEq.respectTransparency false in
/-- Reverse of `LaterServerBridge.run_le_real`: after the same prephase, the logged raw-ordinal KEM real game returns `true` with probability at most that of the stopped run of the hidden logged command program of the tagged program completing with a session at the selected accept, the decision holding and the monitor clear. -/
theorem real_le_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} ≤
    𝒟[(fun reached => decide (Completed decision reached ∧ PqxdhDynamicKemJointStopping.Good reached.2)) <$>
      ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (simulateQ (actual setup) (commands setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (tag work index) [] [] (PqxdhRegistrationJointInitializedAccept.initial
            created)))).run).run (joint, PqxdhDynamicKemRouter.empty)] {true} := by
  classical
  rw [← PqxdhDeploymentLaterServerBridge.exposeAt_tag, ← PqxdhRegistrationJointKemCut.scan_finish _ _ 0,
    PqxdhRegistrationJointKemRawNatural.router_split, map_bind, PqxdhDeploymentLaterServerBridge.scanned_map,
    PqxdhRegistrationJointKemRawNatural.router_map, bind_map_left, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨_ | cut, after⟩ reachedCut
  · rw [prEvent_eq_zero_of_not_mem_support]
    · exact zero_le
    simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision]
  · have cleared : PqxdhDynamicKemJointStopping.Good after :=
      stopped_good setup.baseImpl setup.joint setup.kem selected.val _ _ (joint, PqxdhDynamicKemRouter.empty) rfl
        (some cut, after) reachedCut rfl
    cases cut with
    | complete outcome =>
      rw [prEvent_eq_zero_of_not_mem_support]
      · exact zero_le
      simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision, cutMap]
    | pending request resume =>
      dsimp only [Option.elim_some, Option.map_some]
      rw [PqxdhRegistrationJointKemRawNatural.finish_stopped, map_bind]
      by_cases active : request.2 = chosen.1
      · rw [active]
        apply prEvent_bind_mono_of_forall_le_of_support
        intro encapsulated _
        conv_lhs => rw [(OracleComp.EvalDistEq.bind_const _ _).prEvent_eq (fun y => y = true)]
        rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
        simp only [PqxdhRegistrationJointKemResume.sourcePost, cutMap, active, ite_true, simulateQ_map,
          OptionT.run_map, StateT.run_map, bind_pure_comp, Functor.map_map]
        rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
        apply prEvent_mono_of_support
        rintro reached member event
        simp only [decide_eq_true_eq] at event ⊢
        refine ⟨?_, stopped_good setup.baseImpl setup.joint setup.kem selected.val _ _ _ cleared reached member ?_⟩
        · rcases reached with ⟨_ | final, state⟩
          · simp [PqxdhRegistrationJointKemGame.decision] at event
          · simp only [Option.map_some, PqxdhRegistrationJointKemGame.decision, mapOutcome, decideTag,
              Bool.and_eq_true] at event
            exact ⟨final, rfl, event.1, event.2⟩
        · rcases reached with ⟨_ | final, state⟩
          · simp [PqxdhRegistrationJointKemGame.decision] at event
          · rfl
      · rw [prEvent_eq_zero_of_not_mem_support]
        · exact zero_le
        simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision, cutMap, active]

set_option backward.isDefEq.respectTransparency false in
/-- Reverse of `LaterServerBridge.commands_le_real`: after the same prephase, the logged raw-ordinal KEM real game returns `true` with probability at most that of `Decided ∧ GoodKem` in the logged monitored commands of the tagged program, through the monitor equality `PqxdhDynamicKemJointStopping.history_event`. -/
theorem real_le_commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} ≤
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final)) <$>
      PqxdhDeploymentLaterServerInitialized.commands setup codec checks created (tag work index) joint runtime
        selected.val (List.ofFn (selected.insertNth chosen others))] {true} := by
  classical
  refine le_trans (real_le_run setup codec checks decision work index count selected created joint runtime chosen
    others) ?_
  simp only [PqxdhDeploymentLaterServerInitialized.commands, Functor.map_map]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  refine le_trans (le_of_eq ?_) (le_trans (le_of_eq (PqxdhDynamicKemJointStopping.history_event setup.baseImpl
    setup.joint setup.kem selected.val (List.ofFn (selected.insertNth chosen others))
    (simulateQ (actual setup) (commands setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (tag work index) [] [] (PqxdhRegistrationJointInitializedAccept.initial created)))
    (joint, PqxdhDynamicKemRouter.empty) rfl (Completed decision)).symm) ?_)
  · apply prEvent_congr_of_support
    intro reached _
    simp only [decide_eq_true_eq]
  · apply prEvent_mono_of_support
    rintro ⟨_ | outcome, state⟩ _ ⟨⟨final, found, decided, session⟩, good⟩
    · cases found
    · cases found
      simp only [decide_eq_true_eq]
      exact ⟨⟨_, rfl, decided, session⟩, good⟩

set_option backward.isDefEq.respectTransparency false in
/-- Reverse of theorem T4 for the logged source (`LaterServerBridge.actual_le_real`), under its own creation cap and no other premise: the logged raw-ordinal KEM real game returns `true` with probability at most that of `Decided ∧ GoodKem` in the logged initialized execution of the tagged program, with the log forgotten. -/
theorem real_le_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    letI := Classical.propDecidable
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected] {true} ≤
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} := by
  classical
  have same := PqxdhDeploymentLaterServerInitialized.actual_source_first setup codec checks ensureInit supplied
    (tag work index) ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) rfl count selected
    (PqxdhDeploymentLaterServerBridge.tag_bound work index _ _ bounded)
  rw [(same.map _).evalDist_eq]
  simp only [PqxdhDeploymentLaterServerInitialized.selectedFirst, PqxdhDeploymentLaterServerKemHop.sourceReal,
    PqxdhDeploymentLaterServerKemHop.sourcePre, map_bind, bind_assoc]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro chosen _
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨_ | created, after⟩ _
  · rw [prEvent_eq_zero_of_not_mem_support]
    · exact zero_le
    simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision]
  · dsimp only
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    simp only [map_bind, bind_assoc, pure_bind]
    rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
    apply prEvent_bind_mono_of_forall_le_of_support
    intro others _
    have core := real_le_commands setup codec checks decision work index count selected created after.1.1 after.2
      chosen others
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    simpa only [map_bind, bind_assoc, pure_bind] using core

set_option backward.isDefEq.respectTransparency false in
/-- Theorem T4 for the logged source as an equality: if, on the support of the logged actual execution with the log forgotten, `Decided ∧ GoodKem` implies `KeyMatchFinal`, then T4's event and the logged raw-ordinal KEM real game have the same probability. -/
theorem actual_eq_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1))
    (implied : ∀ final ∈ support ((fun result => (result.1.map fun outcome =>
        PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)),
      Decided decision final → GoodKem selected final → KeyMatchFinal setup codec checks selected final) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} =
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected]
      {true} := by
  classical
  refine le_antisymm (PqxdhDeploymentLaterServerBridge.actual_le_real setup codec checks ensureInit supplied decision
    work runtime count selected index bounded) ((real_le_actual setup codec checks ensureInit supplied decision work
    runtime count selected index bounded).trans (le_of_eq ?_))
  exact chance_ext _ _ _ fun final member =>
    ⟨fun both => ⟨both.1, both.2, implied final member both.1 both.2⟩, fun all => ⟨all.1, all.2.1⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- T4 for the logged source, for decisions that imply `accepted ∧ GoodKem ∧ KeyMatchFinal`: the probability of `Decided` alone equals that of the logged raw-ordinal KEM real game. -/
theorem decided_eq_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1))
    (implied : ∀ final ∈ support ((fun result => (result.1.map fun outcome =>
        PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)),
      Decided decision final → GoodKem selected final ∧ KeyMatchFinal setup codec checks selected final) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} =
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected]
      {true} := by
  classical
  refine Eq.trans ?_ (actual_eq_real setup codec checks ensureInit supplied decision work runtime count selected index
    bounded fun final member decided _ => (implied final member decided).2)
  exact chance_ext _ _ _ fun final member =>
    ⟨fun decided => ⟨decided, implied final member decided⟩, fun all => all.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The defect of T4 for the logged source, for every decision: the logged raw-ordinal KEM real game returns `true` with probability at most that of T4's event plus that of `Decided ∧ GoodKem ∧ ¬KeyMatchFinal` in the logged actual execution. -/
theorem real_le_actual_add (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    letI := Classical.propDecidable
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected] {true} ≤
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} +
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        ¬KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} := by
  classical
  refine (real_le_actual setup codec checks ensureInit supplied decision work runtime count selected index
    bounded).trans ?_
  exact chance_le_add _ _ _ _ fun final _ both => by
    by_cases keyed : KeyMatchFinal setup codec checks selected final
    · exact Or.inl ⟨both.1, both.2, keyed⟩
    · exact Or.inr ⟨both.1, both.2, keyed⟩

set_option backward.isDefEq.respectTransparency false in
/-- Two-sided T4 for the logged source, for every decision, in real numbers: the logged raw-ordinal KEM real game and T4's event in the logged actual execution differ by at most the probability of `Decided ∧ GoodKem ∧ ¬KeyMatchFinal`. -/
theorem actual_real_close (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    letI := Classical.propDecidable
    |(𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected]
          {true}).toReal -
      (𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
          KeyMatchFinal setup codec checks selected final)) <$>
        ((fun result => (result.1.map fun outcome =>
            PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
          (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
            ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}).toReal| ≤
    (𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        ¬KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}).toReal := by
  classical
  exact toReal_close (UniformTargetSelection.chance_ne_top _ _) (UniformTargetSelection.chance_ne_top _ _)
    (PqxdhDeploymentLaterServerBridge.actual_le_real setup codec checks ensureInit supplied decision work runtime count
      selected index bounded)
    (real_le_actual_add setup codec checks ensureInit supplied decision work runtime count selected index bounded)

/-- The two-sided logged KEM hop: the logged raw-ordinal KEM real game and the logged opaque KEM-ideal branch are within one ordinary one-key ML-KEM IND-CCA advantage of the proof-carrying adversary at the logged exposure plus one ML-KEM correctness error (`LaterServerKemHop.certified_advantage` with T6 for the logged source, `LaterServerOpaque.branch_opaque`). -/
theorem hop_close (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    |(𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected]
          {true}).toReal -
      (𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index false] {true}).toReal| ≤
      setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit supplied
          (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count
          selected).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  have close := PqxdhDeploymentLaterServerKemHop.certified_advantage setup functional ensureInit supplied
    (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected
  rw [PqxdhDeploymentLaterServerOpaque.branch_opaque] at close
  exact close

end Generic

section Deployment
open PqxdhDeploymentInterface (Handle ModeSpec Mode Budget FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentLater (Snap PostSpec)
open PqxdhDeploymentLaterServerGame (Reveal)
open PqxdhDeploymentLaterServerCompile (compileServer)
open PqxdhDeploymentLaterServerTrace (traceFrom)
open PqxdhDeploymentKemTransfer (Observed selectedKem)
open PqxdhDeploymentLaterServerTransfer (happens designated decision)

set_option backward.isDefEq.respectTransparency false in
/-- The per-target decision of the LQ-F game is in the class of `actual_eq_real` and `decided_eq_real`: on the support of the logged actual initialized execution of the tagged compiled LQ-F program at raw-accept ordinal `i`, with the log forgotten, `Decided (decision … g)` implies `GoodKem (selectedKem budget g)` (`LaterServerTrace.goodKem_later` with `compile_server_no_kem`) and `KeyMatchFinal (selectedKem budget g)` (`LaterServerTransfer.keymatch_server`, with the approved `Phase1ReadBack`). -/
theorem decision_implies_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A (Out × (Ledger × (Snap × Local))))
    (reached : final ∈ support ((fun result => (result.1.map fun outcome =>
        PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
      (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
        (tag (compileServer setup codec route bounds mode first second) g.1.val)).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (decided : Decided (decision setup.source.crypto codec setup.serverKeyId budget event claim g) final) :
    GoodKem (selectedKem budget g) final ∧ KeyMatchFinal setup codec checks (selectedKem budget g) final := by
  have good := PqxdhDeploymentLaterServerTrace.goodKem_later setup codec checks ensureInit none
    (compileServer setup codec route bounds mode first second)
    (PqxdhDeploymentLaterServerCompileBudget.compile_server_no_kem setup codec route bounds mode first second)
    g.1.val runtime (selectedKem budget g) final reached
  set work := compileServer setup codec route bounds mode first second with workEq
  set tagged := tag (traceFrom work []) g.1.val with taggedEq
  set start : PqxdhRegistrationJointServerPrefix.State KemSK A :=
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) with startEq
  have retagged : tag work g.1.val = (fun outcome => (outcome.1.1, outcome.2)) <$> tagged := by
    have mapped := PqxdhDeploymentLaterServerTrace.tag_map Prod.fst (traceFrom work []) g.1.val
    rw [PqxdhDeploymentLaterServerTrace.traceFrom_erase] at mapped
    exact mapped
  have rightRun : (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
      (tag work g.1.val)).run start =
      (fun result => (result.1.map fun outcome => ((outcome.1.1, (outcome.1.2.1.1.1, outcome.1.2.1.2),
        outcome.1.2.2), outcome.2), result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none tagged).run start := by
    rw [retagged]
    exact PqxdhDeploymentLaterServerTrace.source_map setup codec checks ensureInit none _ tagged start
  rw [rightRun, Functor.map_map, support_map] at reached
  obtain ⟨⟨_ | outcome, after⟩, member, rfl⟩ := reached
  · obtain ⟨_, found, _⟩ := decided
    cases found
  · obtain ⟨_, found, chosen, _⟩ := decided
    simp only [Option.map_some, Option.some.injEq] at found
    subst found
    obtain ⟨raw, value, tagEq, checked, keys⟩ := PqxdhDeploymentLaterServerTransfer.keymatch_server setup codec checks
      route ensureInit phase1 bounds mode first second budget event claim g runtime outcome after member chosen
    exact ⟨good, _, raw, some g.1.val, value, rfl, tagEq, checked, keys⟩

set_option backward.isDefEq.respectTransparency false in
/-- T4's defect vanishes for the per-target decision of the LQ-F game: in the logged actual execution, `Decided ∧ GoodKem ∧ ¬KeyMatchFinal` has probability zero. -/
theorem defect_zero_server (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided (decision setup.source.crypto codec setup.serverKeyId budget event claim g) final ∧
        GoodKem (selectedKem budget g) final ∧ ¬KeyMatchFinal setup codec checks (selectedKem budget g) final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit none
          (tag (compileServer setup codec route bounds mode first second) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} = 0 := by
  classical
  exact chance_eq_zero _ _ fun final member both => both.2.2 (decision_implies_server setup codec checks route
    ensureInit phase1 bounds mode first second budget event claim g runtime final member both.1).2

set_option backward.isDefEq.respectTransparency false in
/-- Steps 9.1-9.2 for the LQ-F game as one equality: for a run-phase budget-respecting `A₁`, every post-run adversary and a target `g = (i, k)`, the probability that the LQ-F game ends with the event and the claim designating `g` equals the probability that the logged raw-ordinal KEM real game of the per-target decision returns `true`. The chain is `LaterServerTransfer.eligible_server` and `actual_eq_real` with the creation cap of the compiled program, with `decision_implies_server`. -/
theorem eligible_server_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} =
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit none
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) g.1.val)
      runtime budget.create (selectedKem budget g)] {true} := by
  rw [PqxdhDeploymentLaterServerTransfer.eligible_server setup codec checks route ensureInit phase1 phase2 bounds mode
    first second budget event claim g runtime]
  exact actual_eq_real setup codec checks ensureInit none _ (compileServer setup codec route bounds mode first second)
    runtime budget.create (selectedKem budget g) g.1.val
    (IsQueryBoundP.mono (PqxdhDeploymentLaterServerCompileBudget.compile_server_creates setup codec route bounds mode
      first second budget respects) (Nat.le_succ _))
    fun final member decided _ => (decision_implies_server setup codec checks route ensureInit phase1 bounds mode first
      second budget event claim g runtime final member decided).2

/-- Two-sided per-target KEM transfer for the LQ-F game: the probability that the LQ-F game ends with the event and the claim designating `g`, and the probability that the logged opaque KEM-ideal branch of `g`'s decision returns `true`, differ by at most one IND-CCA advantage of the proof-carrying adversary at the logged exposure plus one correctness error: the terms of `kem_transfer_server`. A confidentiality statement: the event may read the post-run adversary's output. -/
theorem kem_transfer_server_two_sided (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      (𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        false] {true}).toReal| ≤
      setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
          (PqxdhDeploymentLaterServerCut.scanned setup codec checks
            (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileServer setup codec route bounds mode first second) g.1.val)
          runtime budget.create (selectedKem budget g)).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  rw [eligible_server_real setup codec checks route ensureInit phase1 phase2 bounds mode first second budget respects
    event claim g runtime]
  exact hop_close setup functional codec checks ensureInit none _ _ runtime budget.create (selectedKem budget g) g.1.val

/-- The reverse of `kem_transfer_server` at one target: the logged opaque KEM-ideal branch of `g`'s decision returns `true` with probability at most that of the LQ-F game ending with the event and the claim designating `g`, plus the same IND-CCA advantage and correctness error. -/
theorem kem_transfer_server_lower (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g) g.1.val
        false] {true} ≤
      𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true} +
      ENNReal.ofReal (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
          (PqxdhDeploymentLaterServerCut.scanned setup codec checks
            (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileServer setup codec route bounds mode first second) g.1.val)
          runtime budget.create (selectedKem budget g)).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  refine le_add_of_close (UniformTargetSelection.chance_ne_top _ _) ?_ (kem_transfer_server_two_sided setup functional
    codec checks route ensureInit phase1 phase2 bounds mode first second budget respects event claim g runtime)
  rw [← prEvent_eq_evalDist_singleton _ true]
  exact prEvent_ne_top _

/-- Two-sided exact-sum headline of the key transfer for the LQ-F game: the probability that the LQ-F game ends with the event and a designated claim, and the sum over all targets `g` in `Fin qAccept × Fin (qCreate + 1)` of the logged opaque KEM-ideal branch of `g`'s decision, differ by at most the sum over `g` of one IND-CCA advantage plus one correctness error. -/
theorem kem_transfer_server_sum_two_sided (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool) (claim : Observed Out → Option Handle)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome)) <$>
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second).run
        runtime] {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (𝒟[PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileServer setup codec route bounds mode first second) runtime budget.create (selectedKem budget g)
          g.1.val false] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit none
            (PqxdhDeploymentLaterServerCut.scanned setup codec checks
              (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
              (compileServer setup codec route bounds mode first second) g.1.val)
            runtime budget.create (selectedKem budget g)).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  rw [UniformTargetSelection.split]
  exact abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    kem_transfer_server_two_sided setup functional codec checks route ensureInit phase1 phase2 bounds mode first second
      budget respects event claim g runtime

end Deployment

end BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_commands

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.actual_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.actual_eq_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.decided_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.decided_eq_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_actual_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.real_le_actual_add

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.actual_real_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.actual_real_close

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.hop_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.hop_close

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.decision_implies_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.decision_implies_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.defect_zero_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.defect_zero_server

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.eligible_server_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.eligible_server_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_sum_two_sided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_sum_two_sided
