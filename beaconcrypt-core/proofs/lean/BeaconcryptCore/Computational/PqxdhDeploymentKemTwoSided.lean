-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentTargetRange

/-! CE-9b: the two-sided form of theorem T4 and the two-sided per-target KEM transfer of the common deployment experiment (plan section 9, step 9.7 and the two-sided chain). T4 `KemRawBridge.actual_le_real` bounds `Pr_actual[Decided ∧ GoodKem ∧ KeyMatchFinal]` in the actual initialized execution of the tagged program by `Pr[KemRawGame.sourceReal]`. Its proof rewrites the actual execution into the selected-first game (an equality), moves the event to the stopped router (an equality, `PqxdhDynamicKemJointStopping.history_event`), splits the stopped run at the KEM cut of the selected accept and then discards: runs that stop or complete before the cut and runs whose cut encapsulates to another key (on these the real game also returns `false`), the clear-monitor conjunct of a completed stopped run (which always holds, `stopped_good`), and, in the active branch, every completed run whose decision and session hold but whose recorded PQ key is not the final pool key at the selected creation index, that is, whose selected key was never created during the run. This module proves the reverse chain (`real_le_run`, `real_le_commands`, `real_le_actual`): the real game is at most `Pr_actual[Decided ∧ GoodKem]`, under T4's own premises and no other. Hence the discarded runs are contained in `Decided ∧ GoodKem ∧ ¬KeyMatchFinal` (`real_le_actual_add`, and its real-valued form `actual_real_close`), and T4 is an equality for every decision that, on the support of the actual execution, implies `KeyMatchFinal` whenever `Decided ∧ GoodKem` holds (`actual_eq_real`); for decisions that imply `accepted ∧ GoodKem ∧ KeyMatchFinal` the left side is `Pr_actual[Decided]` (`decided_eq_real`). Without such a hypothesis the equality can fail: the selected accept may encapsulate to the reserved key of the selected creation index while that index is never created, which the real game counts and `KeyMatchFinal` excludes. The deployment decision of CE-9 is such a decision (`decision_implies`, from `keymatch_point` with `Phase1ReadBack` and `PqxdhDeploymentQuiet.approved_goodkem_unbudgeted`), so T4's defect vanishes for it (`defect_zero`) and steps 9.1-9.2 are one equality (`eligible_real`). With the two-sided KEM hop `kem_hop_close` (the certified hop and T6) this gives the two-sided per-target transfer `kem_transfer_two_sided`, `|Pr_CE[E ∧ designated = some g] − Pr[opaqueBranch false]| ≤ Adv^{IND-CCA} + correctnessError`, its reverse inequality `kem_transfer_lower`, and the two-sided exact-sum headlines `kem_transfer_sum_two_sided` (budgeted designation, `Fin qAccept × Fin (qCreate + 1)`) and `kem_transfer_create_two_sided` (plain eligibility, `Fin qAccept × Fin qCreate`), usable for left-or-right events such as `b' = b`. The terms are those of the one-sided CE-9 theorems, each with coefficient one. Premises: T4's own (the query budget of the program and `room`) for the generic statements; for the deployment statements the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`, `FunctionalDecapsulation` (the premise of the KEM hop) and the adversary budget, as in CE-9. No assumption, contract or advantage term is added, and no existing statement changes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag tag accepted decideTag)
open PqxdhRegistrationJointKemRawBridge (Decided GoodKem KeyMatchFinal)
open PqxdhRegistrationJointKemRawNatural (mapOutcome cutMap)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

section Generic

/-- Two events that agree on the support of a run have the same probability, for any decidability instances. -/
theorem chance_ext {α : Type} (run : ProbComp α) (p q : α → Prop) {_ : DecidablePred p} {_ : DecidablePred q}
    (same : ∀ x ∈ support run, p x ↔ q x) :
    𝒟[(fun x => decide (p x)) <$> run] {true} = 𝒟[(fun x => decide (q x)) <$> run] {true} := by
  rw [UniformTargetSelection.chance_eq_vcvioLegacy, UniformTargetSelection.chance_eq_vcvioLegacy]
  exact probEvent_ext same

/-- An event that, on the support of a run, implies one of two events has at most the sum of their probabilities, for any decidability instances. -/
theorem chance_le_add {α : Type} (run : ProbComp α) (p q r : α → Prop) {_ : DecidablePred p} {_ : DecidablePred q}
    {_ : DecidablePred r} (split : ∀ x ∈ support run, p x → q x ∨ r x) :
    𝒟[(fun x => decide (p x)) <$> run] {true} ≤
      𝒟[(fun x => decide (q x)) <$> run] {true} + 𝒟[(fun x => decide (r x)) <$> run] {true} := by
  rw [UniformTargetSelection.chance_eq_vcvioLegacy, UniformTargetSelection.chance_eq_vcvioLegacy, UniformTargetSelection.chance_eq_vcvioLegacy]
  exact probEvent_le_add_of_imp_or split

/-- An event that fails on the support of a run has probability zero, for any decidability instance. -/
theorem chance_eq_zero {α : Type} (run : ProbComp α) (p : α → Prop) {_ : DecidablePred p}
    (never : ∀ x ∈ support run, ¬p x) : 𝒟[(fun x => decide (p x)) <$> run] {true} = 0 := by
  rw [UniformTargetSelection.chance_eq_vcvioLegacy, probEvent_eq_zero_iff]
  exact never

/-- If `a ≤ b ≤ a + c` for finite `a` and `c`, then the real numbers of `b` and `a` differ by at most that of `c`. -/
theorem toReal_close {a b c : ENNReal} (finiteA : a ≠ ⊤) (finiteC : c ≠ ⊤) (lower : a ≤ b) (upper : b ≤ a + c) :
    |b.toReal - a.toReal| ≤ c.toReal := by
  have finiteB := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨finiteA, finiteC⟩) upper
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add', ← ENNReal.toReal_add finiteA finiteC]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finiteA, finiteC⟩) upper
  · exact (sub_nonpos.mpr (ENNReal.toReal_mono finiteB lower)).trans ENNReal.toReal_nonneg

/-- If the real numbers of finite `a` and `b` differ by at most `c`, then `b ≤ a + ofReal c`. -/
theorem le_add_of_close {a b : ENNReal} {c : ℝ} (finiteA : a ≠ ⊤) (finiteB : b ≠ ⊤)
    (close : |a.toReal - b.toReal| ≤ c) : b ≤ a + ENNReal.ofReal c := by
  rw [abs_sub_comm, abs_sub_le_iff] at close
  rw [← ENNReal.ofReal_toReal finiteB, ← ENNReal.ofReal_toReal finiteA]
  refine (ENNReal.ofReal_le_ofReal (sub_le_iff_le_add'.mp close.1)).trans (ENNReal.ofReal_add_le.trans ?_)
  rw [ENNReal.ofReal_toReal finiteA]

set_option backward.isDefEq.respectTransparency false in
/-- A step of the stopped KEM source that returns an answer keeps the selected-disclosure monitor clear: only the selected reveal sets the monitor, and the stopped source answers it with a stop. -/
theorem source_step_good (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : PqxdhLiveKemBirth.Query)
    (state : PqxdhDynamicKemRouter.State KemSK) (good : PqxdhDynamicKemStopping.Good state)
    (result : Option ((PqxdhLiveKemBirth.PoolSpec KemSK).Range query) × PqxdhDynamicKemRouter.State KemSK)
    (supported : result ∈ support (((PqxdhDynamicKemRouter.source baseImpl kem selected pairs query).run).run state))
    (complete : result.1.isSome = true) : PqxdhDynamicKemStopping.Good result.2 := by
  cases query with
  | create =>
      simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run] at supported
      split at supported <;> simp only [mem_support_pure_iff] at supported
      all_goals subst result
      · simp at complete
      · exact good
  | decapsulate index ciphertext =>
      simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run, bind_pure_comp] at supported
      split at supported <;> simp only [support_map, Set.mem_image] at supported
      all_goals obtain ⟨reply, _, rfl⟩ := supported
      all_goals exact good
  | reveal index =>
      simp only [PqxdhDynamicKemRouter.source, OptionT.run_mk, StateT.run] at supported
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        exact good
      · split at supported <;> simp only [mem_support_pure_iff] at supported
        all_goals subst result
        · simp at complete
        · exact good

set_option backward.isDefEq.respectTransparency false in
/-- A step of the stopped joint router that returns an answer keeps the selected-disclosure monitor clear; identity operations and local coins do not touch the KEM state. -/
theorem stopped_step_good (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (state : PqxdhDynamicKemJointSource.State KemSK) (good : PqxdhDynamicKemJointStopping.Good state)
    (answer : (PqxdhLiveKemBirth.Spec KemSK).Range query) (after : PqxdhDynamicKemJointSource.State KemSK)
    (supported : (some answer, after) ∈ support (((PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected
      pairs query).run).run state)) : PqxdhDynamicKemJointStopping.Good after := by
  rcases query with joint | (coin | query)
  all_goals simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk,
    StateT.run, support_map, Set.mem_image] at supported
  all_goals obtain ⟨reply, actual, same⟩ := supported
  · cases same
    exact good
  · cases same
    exact good
  · simp only [Prod.mk.injEq] at same
    obtain ⟨first, rfl⟩ := same
    exact source_step_good baseImpl kem selected pairs query state.2 good reply actual (by rw [first]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Every completed run of the stopped joint router from a state with a clear selected-disclosure monitor ends with a clear monitor. This is the step that `KemRawBridge.commands_le_real` discards with `event.1`; it loses nothing. -/
theorem stopped_good (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result)
    (state : PqxdhDynamicKemJointSource.State KemSK) (good : PqxdhDynamicKemJointStopping.Good state)
    (result : Option Result × PqxdhDynamicKemJointSource.State KemSK)
    (supported : result ∈ support (((simulateQ
      (PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected pairs) client).run).run state))
    (complete : result.1.isSome = true) : PqxdhDynamicKemJointStopping.Good result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, tail⟩ := supported
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
        subst result
        simp at complete
      · exact ih answer after (stopped_step_good baseImpl primitives kem selected pairs query state good answer after
          actual) result tail complete

/-- A completed router run of the tagged program in which the selected raw accept returned a session and the decision on the program's result holds; the final-state form of the real game's decision. -/
def Completed (decision : X → Bool)
    (reached : Option (Outcome KemSK (X × Tag)) × PqxdhDynamicKemJointSource.State KemSK) : Prop :=
  ∃ outcome, reached.1 = some outcome ∧ decision outcome.1.1.1 = true ∧ accepted outcome.1.1.2 = true

set_option backward.isDefEq.respectTransparency false in
/-- Reverse of `KemRawBridge.run_le_real`: after the same prephase, the raw-ordinal KEM real game returns `true` with probability at most that of the stopped run of the tagged program completing with a session at the selected accept, the decision holding and the monitor clear. A stop, a completion before the cut and an encapsulation to another key give `false` in the real game; an active cut is finished in the real game by the challenger's encapsulation to the selected key and the saved continuation, which is the stopped run's own finish (`finish_stopped`), and the challenger's extra uniform draw is lossless. -/
theorem real_le_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} ≤
    𝒟[(fun reached => decide (Completed decision reached ∧ PqxdhDynamicKemJointStopping.Good reached.2)) <$>
      ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhRegistrationJointKemCommands.program setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (tag work index) [] (PqxdhRegistrationJointInitializedAccept.initial
            created))).run).run (joint, PqxdhDynamicKemRouter.empty)] {true} := by
  classical
  rw [← PqxdhRegistrationJointKemRawNatural.exposeAt_tag, ← PqxdhRegistrationJointKemCut.scan_finish _ _ 0,
    PqxdhRegistrationJointKemRawNatural.router_split, map_bind, PqxdhRegistrationJointKemRawNatural.rawScan_map,
    PqxdhRegistrationJointKemRawNatural.router_map, bind_map_left, evalDist_apply_singleton, evalDist_apply_singleton]
  apply probOutput_bind_mono
  rintro ⟨_ | cut, after⟩ reachedCut
  · rw [probOutput_eq_zero_of_not_mem_support]
    · exact zero_le
    simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision]
  · have cleared : PqxdhDynamicKemJointStopping.Good after :=
      stopped_good setup.baseImpl setup.joint setup.kem selected.val _ _ (joint, PqxdhDynamicKemRouter.empty) rfl
        (some cut, after) reachedCut rfl
    cases cut with
    | complete outcome =>
      rw [probOutput_eq_zero_of_not_mem_support]
      · exact zero_le
      simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision, cutMap]
    | pending request resume =>
      dsimp only [Option.elim_some, Option.map_some]
      rw [PqxdhRegistrationJointKemRawNatural.finish_stopped, map_bind]
      by_cases active : request.2 = chosen.1
      · rw [active]
        apply probOutput_bind_mono
        intro encapsulated _
        rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
        simp only [PqxdhRegistrationJointKemResume.sourcePost, cutMap, active, ite_true, simulateQ_map,
          OptionT.run_map, StateT.run_map, bind_pure_comp, Functor.map_map]
        rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
        apply probEvent_mono
        rintro reached member event
        simp only [Function.comp_apply, decide_eq_true_eq] at event ⊢
        refine ⟨?_, stopped_good setup.baseImpl setup.joint setup.kem selected.val _ _ _ cleared reached member ?_⟩
        · rcases reached with ⟨_ | final, state⟩
          · simp [PqxdhRegistrationJointKemGame.decision] at event
          · simp only [Option.map_some, PqxdhRegistrationJointKemGame.decision, mapOutcome, decideTag,
              Bool.and_eq_true] at event
            exact ⟨final, rfl, event.1, event.2⟩
        · rcases reached with ⟨_ | final, state⟩
          · simp [PqxdhRegistrationJointKemGame.decision] at event
          · rfl
      · rw [probOutput_eq_zero_of_not_mem_support]
        · exact zero_le
        simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision, cutMap, active]

set_option backward.isDefEq.respectTransparency false in
/-- Reverse of `KemRawBridge.commands_le_real`: after the same prephase, the raw-ordinal KEM real game returns `true` with probability at most that of `Decided ∧ GoodKem` in the monitored actual source commands of the tagged program, with no key-match conjunct. The completed stopped run is moved back to the ordinary router by the existing monitor equality `PqxdhDynamicKemJointStopping.history_event`. -/
theorem real_le_commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} ≤
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final)) <$>
      PqxdhRegistrationJointKemInitialization.commands setup codec checks created (tag work index) joint runtime
        selected.val (List.ofFn (selected.insertNth chosen others))] {true} := by
  classical
  refine le_trans (real_le_run setup codec checks decision work index count selected created joint runtime chosen
    others) ?_
  simp only [PqxdhRegistrationJointKemInitialization.commands, Functor.map_map]
  rw [evalDist_apply_singleton, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  refine le_trans (le_of_eq ?_) (le_trans (le_of_eq (PqxdhDynamicKemJointStopping.history_event setup.baseImpl
    setup.joint setup.kem selected.val (List.ofFn (selected.insertNth chosen others))
    (PqxdhRegistrationJointKemCommands.program setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (tag work index) [] (PqxdhRegistrationJointInitializedAccept.initial created))
    (joint, PqxdhDynamicKemRouter.empty) rfl (Completed decision)).symm) ?_)
  · apply probEvent_ext
    intro reached _
    simp only [Function.comp_apply, decide_eq_true_eq]
  · apply probEvent_mono
    rintro ⟨_ | outcome, state⟩ _ ⟨⟨final, found, decided, session⟩, good⟩
    · cases found
    · cases found
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact ⟨⟨_, rfl, decided, session⟩, good⟩

set_option backward.isDefEq.respectTransparency false in
/-- Reverse of theorem T4 (`KemRawBridge.actual_le_real`), under T4's own premises and no other: the raw-ordinal KEM real game returns `true` with probability at most that of `Decided ∧ GoodKem` in the actual initialized source execution of the tagged program. The first step is the existing source-order equality `KemInitialization.actual_source_first`; a failed Server construction gives `false` in the real game. -/
theorem real_le_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (room : budget (.inl 1) ≤ count + 1) :
    letI := Classical.propDecidable
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index] {true} ≤
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} := by
  classical
  have same := PqxdhRegistrationJointKemInitialization.actual_source_first setup codec checks ensureInit supplied
    (tag work index) ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) rfl budget
    (fun source => PqxdhRegistrationJointAcceptCutTag.tag_bound work index _ _ (certified source)) count selected room
  conv_rhs => rw [evalDist_apply_singleton, probOutput_def, evalSPMF_map, same, ← evalSPMF_map, ← probOutput_def]
  rw [evalDist_apply_singleton]
  simp only [PqxdhRegistrationJointKemInitialization.selectedFirst, PqxdhRegistrationJointKemRawGame.sourceReal,
    PqxdhRegistrationJointKemRawChallenge.sourcePreRaw, map_bind, bind_assoc]
  apply probOutput_bind_mono
  intro chosen _
  apply probOutput_bind_mono
  rintro ⟨_ | created, after⟩ _
  · rw [probOutput_eq_zero_of_not_mem_support]
    · exact zero_le
    simp [PqxdhRegistrationJointKemResume.sourcePost, PqxdhRegistrationJointKemGame.decision]
  · dsimp only
    simp only [map_bind, bind_assoc, pure_bind]
    apply probOutput_bind_mono
    intro others _
    have core := real_le_commands setup codec checks decision work index count selected created after.1.1 after.2
      chosen others
    rw [evalDist_apply_singleton, evalDist_apply_singleton] at core
    simpa only [map_bind, bind_assoc, pure_bind] using core

set_option backward.isDefEq.respectTransparency false in
/-- Theorem T4 as an equality (CE-9b). If, on the support of the actual initialized source execution of the tagged program, `Decided ∧ GoodKem` implies `KeyMatchFinal`, then the probability of T4's event `Decided ∧ GoodKem ∧ KeyMatchFinal` equals the probability that the raw-ordinal KEM real game returns `true`. The premises are T4's own and the implication; `≤` is T4, `≥` is `real_le_actual` with the implication. -/
theorem actual_eq_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (room : budget (.inl 1) ≤ count + 1)
    (implied : ∀ final ∈ support ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome
        setup), result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied
          (tag work index)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)),
      Decided decision final → GoodKem selected final → KeyMatchFinal setup codec checks selected final) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} =
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index] {true} := by
  classical
  refine le_antisymm (PqxdhRegistrationJointKemRawBridge.actual_le_real setup codec checks ensureInit supplied decision
    work runtime budget certified count selected index room) ((real_le_actual setup codec checks ensureInit supplied
    decision work runtime budget certified count selected index room).trans (le_of_eq ?_))
  exact chance_ext _ _ _ fun final member =>
    ⟨fun both => ⟨both.1, both.2, implied final member both.1 both.2⟩, fun all => ⟨all.1, all.2.1⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- T4 for decisions that imply `accepted ∧ GoodKem ∧ KeyMatchFinal` (the class of plan section 9): if, on the support of the actual execution, `Decided` implies `GoodKem ∧ KeyMatchFinal`, then the probability of `Decided` alone equals the probability that the raw-ordinal KEM real game returns `true`. -/
theorem decided_eq_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (room : budget (.inl 1) ≤ count + 1)
    (implied : ∀ final ∈ support ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome
        setup), result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied
          (tag work index)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)),
      Decided decision final → GoodKem selected final ∧ KeyMatchFinal setup codec checks selected final) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} =
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index] {true} := by
  classical
  refine Eq.trans ?_ (actual_eq_real setup codec checks ensureInit supplied decision work runtime budget certified count
    selected index room fun final member decided _ => (implied final member decided).2)
  exact chance_ext _ _ _ fun final member =>
    ⟨fun decided => ⟨decided, implied final member decided⟩, fun all => all.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The defect of T4, for every decision and under T4's own premises: the raw-ordinal KEM real game returns `true` with probability at most that of T4's event plus that of `Decided ∧ GoodKem ∧ ¬KeyMatchFinal` in the actual execution. Every run that the proof of T4 discards is therefore a run of the second event; a decision that excludes it makes T4 an equality (`actual_eq_real`). -/
theorem real_le_actual_add (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (room : budget (.inl 1) ≤ count + 1) :
    letI := Classical.propDecidable
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index] {true} ≤
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} +
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        ¬KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} := by
  classical
  refine (real_le_actual setup codec checks ensureInit supplied decision work runtime budget certified count selected
    index room).trans ?_
  exact chance_le_add _ _ _ _ fun final _ both => by
    by_cases keyed : KeyMatchFinal setup codec checks selected final
    · exact Or.inl ⟨both.1, both.2, keyed⟩
    · exact Or.inr ⟨both.1, both.2, keyed⟩

set_option backward.isDefEq.respectTransparency false in
/-- Two-sided T4 for every decision, in real numbers: the raw-ordinal KEM real game and T4's event in the actual execution differ by at most the probability of `Decided ∧ GoodKem ∧ ¬KeyMatchFinal` in the actual execution. -/
theorem actual_real_close (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (room : budget (.inl 1) ≤ count + 1) :
    letI := Classical.propDecidable
    |(𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
        selected index] {true}).toReal -
      (𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
          KeyMatchFinal setup codec checks selected final)) <$>
        ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
          (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
            ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}).toReal| ≤
    (𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        ¬KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}).toReal := by
  classical
  have lower := PqxdhRegistrationJointKemRawBridge.actual_le_real setup codec checks ensureInit supplied decision work
    runtime budget certified count selected index room
  have upper := real_le_actual_add setup codec checks ensureInit supplied decision work runtime budget certified count
    selected index room
  exact toReal_close (UniformTargetSelection.chance_ne_top _ _) (UniformTargetSelection.chance_ne_top _ _) lower upper

end Generic

section Deployment
open PqxdhDeploymentInterface (Handle ModeSpec Mode Budget FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentRegistrationTrace (traceFrom)
open PqxdhDeploymentKemTransfer (Observed happens designated decision selectedKem)

set_option backward.isDefEq.respectTransparency false in
/-- The per-target decision of the deployment experiment is in the class of `actual_eq_real` and `decided_eq_real`: on the support of the actual initialized source execution of the tagged compiled program at raw-accept ordinal `i`, from empty pools with a generated Server seed, `Decided (decision … g)` implies `GoodKem (selectedKem budget g)` (`PqxdhDeploymentQuiet.approved_goodkem_unbudgeted`) and `KeyMatchFinal (selectedKem budget g)` (`PqxdhDeploymentKemTransfer.keymatch_point`, with the approved `Phase1ReadBack`). `Decided` includes the `accepted` conjunct. -/
theorem decision_implies (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A ((X × Ledger) × Local))
    (reached : final ∈ support ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome
      setup), result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
        (tag (compileFull setup codec route bounds mode adversary) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (decided : Decided (decision setup.source.crypto codec setup.serverKeyId budget event claim g) final) :
    GoodKem (selectedKem budget g) final ∧ KeyMatchFinal setup codec checks (selectedKem budget g) final := by
  have good := PqxdhDeploymentQuiet.approved_goodkem_unbudgeted setup codec checks route ensureInit none bounds mode
    adversary g.1.val runtime (selectedKem budget g) final reached
  set work := compileFull setup codec route bounds mode adversary with workEq
  set tagged := tag (traceFrom work []) g.1.val with taggedEq
  set start : PqxdhRegistrationJointServerPrefix.State KemSK A :=
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) with startEq
  have retagged : tag work g.1.val = (fun outcome => (outcome.1.1, outcome.2)) <$> tagged := by
    have mapped := PqxdhDeploymentRegistrationTrace.tag_map Prod.fst (traceFrom work []) g.1.val
    rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at mapped
    exact mapped
  have rightRun : (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
      (tag work g.1.val)).run start =
      (fun result => (result.1.map fun outcome => (outcome.1, (outcome.2.1.1.1, outcome.2.1.2), outcome.2.2),
        result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none tagged).run
          start := by
    rw [retagged]
    exact PqxdhDeploymentRegistrationTrace.source_map setup codec checks ensureInit none _ tagged start
  rw [rightRun, Functor.map_map, support_map] at reached
  obtain ⟨⟨_ | outcome, after⟩, member, rfl⟩ := reached
  · obtain ⟨_, found, _⟩ := decided
    cases found
  · obtain ⟨_, found, chosen, _⟩ := decided
    simp only [Option.map_some, Option.some.injEq] at found
    subst found
    obtain ⟨raw, value, tagEq, checked, keys⟩ := PqxdhDeploymentKemTransfer.keymatch_point setup codec checks route
      ensureInit phase1 bounds mode adversary budget event claim g runtime outcome after member chosen
    exact ⟨good, _, raw, some g.1.val, value, rfl, tagEq, checked, keys⟩

set_option backward.isDefEq.respectTransparency false in
/-- T4's defect vanishes for the per-target decision of the deployment experiment: in the actual execution, `Decided ∧ GoodKem ∧ ¬KeyMatchFinal` has probability zero, so no run that the proof of T4 discards occurs with positive probability. -/
theorem defect_zero (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided (decision setup.source.crypto codec setup.serverKeyId budget event claim g) final ∧
        GoodKem (selectedKem budget g) final ∧ ¬KeyMatchFinal setup codec checks (selectedKem budget g) final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
          (tag (compileFull setup codec route bounds mode adversary) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} = 0 := by
  classical
  exact chance_eq_zero _ _ fun final member both => both.2.2 (decision_implies setup codec checks route ensureInit
    phase1 bounds mode adversary budget event claim g runtime final member both.1).2

set_option backward.isDefEq.respectTransparency false in
/-- Steps 9.1-9.2 of plan section 9 as one equality (CE-9b): for a budget-respecting adversary and a target `g = (i, k)`, the probability that the deployment experiment ends with the event and the claim designating `g` equals the probability that the raw-ordinal KEM real game of the per-target decision returns `true`. The chain is step 9.1 (`eligible_actual`) and `actual_eq_real` at the transported caps, with `decision_implies`. Premises: the approved `Phase1ReadBack` and `Phase2ReadBack` and the budget. -/
theorem eligible_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} =
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit none
      (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val]
      {true} := by
  rw [PqxdhDeploymentKemTransfer.eligible_actual setup codec checks route ensureInit phase1 phase2 bounds mode adversary
    budget event claim g runtime]
  exact actual_eq_real setup codec checks ensureInit none _ (compileFull setup codec route bounds mode adversary)
    runtime (PqxdhDeploymentCompileCaps.transported bounds budget)
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
    budget.create (selectedKem budget g) g.1.val (PqxdhDeploymentCompileCaps.transported_room bounds budget)
    fun final member decided _ => (decision_implies setup codec checks route ensureInit phase1 bounds mode adversary
      budget event claim g runtime final member decided).2

/-- Two-sided per-target KEM transfer (CE-9b, steps 9.1-9.4 in two-sided form): for a budget-respecting adversary and a target `g = (i, k)`, the probability that the deployment experiment ends with the event and the claim designating `g` and the probability that the opaque KEM-ideal branch of `g`'s decision returns `true` differ, in absolute value, by at most one ordinary one-key ML-KEM IND-CCA advantage of the exact proof-carrying raw-ordinal adversary plus one ML-KEM correctness error: the terms of `kem_transfer`. The event is arbitrary, for example `b' = b` for a left-or-right claim. The chain is `eligible_real` and the two-sided KEM hop `kem_hop_close`. Premises: `FunctionalDecapsulation`, `Phase1ReadBack`, `Phase2ReadBack` and the budget. -/
theorem kem_transfer_two_sided (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
        false] {true}).toReal| ≤
      setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
          g.1.val).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup := by
  rw [eligible_real setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects event claim
    g runtime]
  exact PqxdhDeploymentKemTransfer.kem_hop_close setup functional codec checks route ensureInit bounds mode adversary
    budget event claim g runtime

/-- The reverse of `kem_transfer` at one target: the opaque KEM-ideal branch of `g`'s decision returns `true` with probability at most that of the deployment experiment ending with the event and the claim designating `g`, plus the same IND-CCA advantage and correctness error. -/
theorem kem_transfer_lower (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
        (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
        false] {true} ≤
      𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} +
      ENNReal.ofReal (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
          (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
        (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
          g.1.val).toINDCCA +
        PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  refine le_add_of_close (UniformTargetSelection.chance_ne_top _ _) ?_ (kem_transfer_two_sided setup functional codec
    checks route ensureInit phase1 phase2 bounds mode adversary budget respects event claim g runtime)
  rw [evalDist_apply_singleton]
  exact probOutput_ne_top

/-- A sum over finitely many targets of finite differences of probabilities: the difference of the summed probabilities is at most the sum of the per-target bounds. -/
theorem abs_sum_sub_le {G : Type} [Fintype G] (first second : G → ENNReal) (bound : G → ℝ)
    (finite : ∀ target, first target ≠ ⊤)
    (each : ∀ target, |(first target).toReal - (second target).toReal| ≤ bound target) :
    |(∑ target, first target).toReal - ∑ target, (second target).toReal| ≤ ∑ target, bound target := by
  rw [ENNReal.toReal_sum fun target _ => finite target, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun target _ => each target)

/-- Two-sided exact-sum headline of the key transfer, with the budgeted designation: the probability that the deployment experiment ends with the event and the claim designating some target in `Fin qAccept × Fin (qCreate + 1)`, and the sum over all such targets `g` of the probability that the opaque KEM-ideal branch of `g`'s decision returns `true`, differ by at most the sum over `g` of one IND-CCA advantage of `g`'s proof-carrying adversary plus one correctness error. The first step is the exact split `UniformTargetSelection.split`; no selection factor and no EUF term is charged. -/
theorem kem_transfer_sum_two_sided (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g) g.1.val
          false] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.capacity,
        (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
            (decision setup.source.crypto codec setup.serverKeyId budget event claim g)
            (compileFull setup codec route bounds mode adversary) runtime budget.create (selectedKem budget g)
            g.1.val).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  rw [UniformTargetSelection.split]
  exact abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    kem_transfer_two_sided setup functional codec checks route ensureInit phase1 phase2 bounds mode adversary budget
      respects event claim g runtime

/-- A sum over `Fin (n + 1)` whose last term vanishes is the sum of the other terms over `Fin n`. -/
theorem sum_last_eq (n : Nat) (terms : Fin (n + 1) → ENNReal) (last : terms (Fin.last n) = 0) :
    ∑ k, terms k = ∑ k : Fin n, terms k.castSucc := by
  rw [Fin.sum_univ_castSucc, last, add_zero]

/-- The exact split over the tight target domain: for a budget-respecting adversary, the probability that the deployment experiment ends with the event and the claim designated at all (plain eligibility) is the sum over `g` in `Fin qAccept × Fin qCreate`, with `k` read in `Fin (qCreate + 1)`, of the probability that it ends with the event and the claim designating `g`. The column `k = qCreate` is never designated (`designated_create`). -/
theorem split_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} =
      ∑ g : Fin budget.accept × Fin budget.create,
        𝒟[(fun outcome => decide (happens event outcome = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim outcome =
            some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
        (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
          {true} := by
  rw [PqxdhDeploymentKemTransfer.map_support_congr _ _
    (fun outcome => decide (happens event outcome = true ∧
      (designated setup.source.crypto codec setup.serverKeyId budget claim outcome).isSome))
    (fun outcome reached => by
      rw [PqxdhDeploymentTargetRange.eligible_designated setup codec checks route ensureInit phase1 phase2 bounds mode
        adversary budget respects runtime claim outcome reached]),
    UniformTargetSelection.split, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun session _ => sum_last_eq budget.create _ ?_
  rw [UniformTargetSelection.chance_eq_vcvioLegacy, probEvent_eq_zero_iff]
  rintro outcome reached ⟨_, chosen⟩
  exact lt_irrefl _ (PqxdhDeploymentTargetRange.designated_create setup codec checks route ensureInit phase1 phase2
    bounds mode adversary budget respects runtime claim outcome reached _ chosen)

/-- Two-sided exact-sum headline over the tight target domain, with plain eligibility: the probability that the deployment experiment ends with the event and the claim designated at all, and the sum over `g` in `Fin qAccept × Fin qCreate`, with `k` read in `Fin (qCreate + 1)` through `Fin.castSucc`, of the probability that the opaque KEM-ideal branch of `g`'s decision returns `true`, differ by at most the sum over the same targets of one IND-CCA advantage plus one correctness error. This is the two-sided form of `kem_transfer_create`. -/
theorem kem_transfer_create_two_sided (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT A ProbComp Bool) (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A) :
    |(𝒟[(fun outcome => decide (happens event outcome = true ∧
        (PqxdhDeploymentTargetRange.eligible setup.source.crypto codec setup.serverKeyId claim outcome).isSome)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime]
        {true}).toReal -
      ∑ g : Fin budget.accept × Fin budget.create,
        (𝒟[PqxdhRegistrationJointKemRawOpaque.opaqueBranch setup codec checks ensureInit none
          (decision setup.source.crypto codec setup.serverKeyId budget event claim (g.1, g.2.castSucc))
          (compileFull setup codec route bounds mode adversary) runtime budget.create
          (selectedKem budget (g.1, g.2.castSucc)) g.1.val false] {true}).toReal| ≤
      ∑ g : Fin budget.accept × Fin budget.create,
        (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl
            (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhRegistrationJointKemRawCertified.adversary setup codec checks ensureInit none
            (decision setup.source.crypto codec setup.serverKeyId budget event claim (g.1, g.2.castSucc))
            (compileFull setup codec route bounds mode adversary) runtime budget.create
            (selectedKem budget (g.1, g.2.castSucc)) g.1.val).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  rw [split_create setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects event claim
    runtime]
  exact abs_sum_sub_le _ _ _ (fun _ => UniformTargetSelection.chance_ne_top _ _) fun g =>
    kem_transfer_two_sided setup functional codec checks route ensureInit phase1 phase2 bounds mode adversary budget
      respects event claim (g.1, g.2.castSucc) runtime

end Deployment

end BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.chance_ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.chance_ext

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.chance_le_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.chance_le_add

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.chance_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.chance_eq_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.toReal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.toReal_close

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.le_add_of_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.le_add_of_close

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.source_step_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.source_step_good

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.stopped_step_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.stopped_step_good

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.stopped_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.stopped_good

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_commands

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.actual_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.actual_eq_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.decided_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.decided_eq_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_actual_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.real_le_actual_add

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.actual_real_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.actual_real_close

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.decision_implies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.decision_implies

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.defect_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.defect_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.eligible_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.eligible_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_two_sided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_two_sided

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.abs_sum_sub_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.abs_sum_sub_le

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_sum_two_sided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_sum_two_sided

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.sum_last_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.sum_last_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.split_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.split_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_create_two_sided' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided.kem_transfer_create_two_sided
