-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCompile
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBeacon
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-!
# The hand-off of CE-11b to CE-12 (unit U7)

CE-11b's hand-off theorems (design-v2 section 9.1, as amended: `envGD` without `bindStart`, C1 through `PqxdhDeploymentIdealEnv.c1_idealGame`):

- The record lift's slot provenance (`run_origins`, generic in the environment and the slot count): one command of the all-real record compiler projected to the World state and the computed installation origins is the provenance-annotated World command (`handler_project`, from `PqxdhRecordLiftWorldCompiler.handler_erasure` and `PqxdhRecordLiftWorldProvenance.handler_origins`), so every schedule (`schedule_project`) and the compiler's run of the frozen open program projects to the provenance-annotated record world `PqxdhDeploymentIdealOrigins.annotatedRun` (`run_origins`). The record lift's view (`PqxdhRecordLiftIdeal.chainView`: output, ledger, environment state, produced frames, raw-attempt counters and the handle-to-slot map `PqxdhRecordLiftIdeal.handleSlot`) of the record protocol under the all-real lookup policy and of the all-real chain world has the law of the annotated view (`annotatedView`) of the annotated world (`protocol_view`, `realChains_view`, `realChains_analysis_slots`, the support form `realChains_support`).
- The per-target decision `decisionOn` (the event holds and the claim's budgeted designation is `g`): item 2's decision is `decisionOn` on the compiled program's observation (`decision_observe`), and the decision of the second compile lemma is `decisionOn` on the observed projection of CE's ideal game (`ceDecide_observed`).
- `ideal_world`: under `Phase1ReadBack` and `Phase2ReadBack`, for every adversary within its budget, item 2's two-slot world of the compiled program (`PqxdhRegistrationJointKemSecondEntry.slotGame … 2`) and the record world with the ideal environment of the target of `g` (`PqxdhDeploymentIdealEnv.envGD` at `Target.ofCE budget g`) give the per-target decision the same probability (`PqxdhDeploymentIdealCompile.ideal_compile`, `PqxdhDeploymentIdealEnv.c1_idealGame`).
- With C5 restated (`PqxdhDeploymentIdealBeacon.ideal_slots`): `ideal_world_slots` (the equality with `IdealSlots ∨ Anomaly` conjoined on the annotated world), `ideal_world_slots_le` (at most the decision with `IdealSlots` plus the probability of the Beacon-side anomaly on the record world) and `ideal_world_slots_ct` (the anomaly bounded by `ctGuess`, `PqxdhDeploymentIdealAnomalyBound.anomaly_le`).
- On the record lift's view of the all-real chain world: `ideal_view_slots` (C5 restated for the view's handle-to-slot map on every outcome), `ideal_world_view` (`ideal_world` on the view) and `ideal_world_view_slots`, `ideal_world_view_ct` (the bound forms that CE-12 composes with the record lifts).

These are equalities in law, support facts and bounds by the probability of a public event; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment WorldSpec Slot)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhRecordLiftWorldCompiler (project)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (IdealSlots Anomaly originSlots)

/-! ### The record lift's handle-to-slot map and the provenance annotation -/

section Origins
variable {n : ℕ} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The handle-to-slot map of a provenance annotation, for every slot count; at two slots it is `PqxdhDeploymentIdealTrace.originSlots` (`originMap_two`). -/
def originMap (o : PqxdhRecordLiftOrigins.Origins n) : Handle → Option (Slot n)
  | .peer keyId => o.peers keyId
  | .owner index => o.owners index

/-- At two slots the handle-to-slot map of an annotation is `PqxdhDeploymentIdealTrace.originSlots`. -/
theorem originMap_two : originMap (n := 2) = originSlots := by
  funext o handle
  cases handle <;> rfl

/-- The record lift's permitted view (`PqxdhRecordLiftIdeal.View`) read off an outcome of the provenance-annotated record world: the adversary's output, the ledger and the environment state, the produced frames and raw-attempt counters of the World, and the annotation's handle-to-slot map. -/
def annotatedView {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftOrigins.State n) : PqxdhRecordLiftIdeal.View n E X :=
  ⟨result.1.map fun value => (value.2.1.1, value.2.1.2, value.2.2), result.2.1.produced,
    PqxdhRecordLiftWorld.rawCounters result.2.1, originMap result.2.2⟩

/-- The CE-12 analysis projection of the annotated view is the World's analysis projection of the erased outcome. -/
theorem annotatedView_analysis {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftOrigins.State n) :
    (annotatedView result).analysis = PqxdhRecordLiftWorld.analysis (result.1, result.2.1) := by
  rcases result with ⟨_ | value, state⟩ <;> rfl

/-- One command of the all-real record compiler, projected to the World state and the computed installation origins (`PqxdhRecordLiftWorldCompiler.project`), is the provenance-annotated World command at the projected state, from every compiler state with the operational invariant `Good`: the World part is `PqxdhRecordLiftWorldCompiler.handler_erasure`, and the computed origins after the command are the annotation of its reply (`PqxdhRecordLiftWorldProvenance.handler_origins`). -/
theorem handler_project (query : (WorldSpec n).Domain) (state : PqxdhRecordLiftWorldCompiler.State n)
    (good : PqxdhRecordLiftWorldCompiler.Good setup.source state) :
    Prod.map id project <$> (PqxdhRecordLiftWorldCompiler.handler (PqxdhRecordLiftWorldCompiler.realPolicy setup codec)
        setup codec route query).run state =
      (PqxdhRecordLiftOrigins.handler setup codec route query).run (project state) := by
  have erased := PqxdhRecordLiftWorldCompiler.handler_erasure setup codec route query state good
  change _ = (PqxdhRecordLiftWorld.handler setup codec route query).run (PqxdhRecordLiftWorldCompiler.world state) >>=
    fun result => pure (result.1, (result.2, PqxdhRecordLiftOrigins.annotate query result.1
      (PqxdhRecordLiftWorldCompiler.origins state)))
  rw [← erased, bind_map_left, map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun result member => ?_
  have tagged := PqxdhRecordLiftWorldProvenance.handler_origins (PqxdhRecordLiftWorldCompiler.realPolicy setup codec)
    setup codec route query state result member
  change pure (result.1, (PqxdhRecordLiftWorldCompiler.world result.2, PqxdhRecordLiftWorldCompiler.origins result.2)) = _
  rw [tagged]
  rfl

/-- Every adaptive schedule of the all-real record compiler, projected to the World state and the computed installation origins, is the provenance-annotated World schedule at the projected state, from every compiler state with `Good` (kept by every command, `PqxdhRecordLiftWorldCompiler.handler_good`). -/
theorem schedule_project {Result : Type} (client : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftWorldCompiler.State n) (good : PqxdhRecordLiftWorldCompiler.Good setup.source state) :
    Prod.map id project <$> (simulateQ (PqxdhRecordLiftWorldCompiler.handler
        (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup codec route) client).run state =
      (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route) client).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (PqxdhRecordLiftWorldCompiler.Good setup.source) project
    (fun query current holds => PqxdhRecordLiftWorldCompiler.handler_good setup codec route query current holds)
    (fun query current holds => handler_project setup codec route query current holds) client state good

/-- `run_origins` (design-v2 section 9.1): the all-real record compiler's run of the frozen open program, projected to the World state and the computed installation origins, is the provenance-annotated record world (`PqxdhDeploymentIdealOrigins.annotatedRun`), for every environment. It extends `PqxdhRecordLiftWorldCompiler.run_erasure` by the annotation. -/
theorem run_origins {E X : Type} (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    Prod.map id project <$> PqxdhRecordLiftWorldCompiler.run (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup
        codec route env serverKid bounds mode adversary =
      PqxdhDeploymentIdealOrigins.annotatedRun setup codec route env serverKid bounds mode adversary :=
  schedule_project setup codec route _ PqxdhRecordLiftWorldCompiler.initial
    (PqxdhRecordLiftWorldCompiler.initial_good setup.source)

/-- The record lift's view of a split compiler result is the annotated view of its projection: the handle-to-slot map `PqxdhRecordLiftIdeal.handleSlot` of the record control is the handle-to-slot map of the computed installation origins. -/
theorem chainView_split {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftWorldCompiler.State n) :
    PqxdhRecordLiftIdeal.chainView (PqxdhRecordLiftProtocol.splitResult result) =
      annotatedView (Prod.map id project result) := by
  have raw := PqxdhRecordLiftWorldCompiler.rawCounters_erasure result.2
  have slots : PqxdhRecordLiftIdeal.handleSlot (PqxdhRecordLiftProtocol.control result.2) =
      originMap (PqxdhRecordLiftWorldCompiler.origins result.2) := by
    funext handle
    cases handle <;> rfl
  change (⟨_, _, PqxdhRecordLiftWorldCompiler.rawCounters result.2,
    PqxdhRecordLiftIdeal.handleSlot (PqxdhRecordLiftProtocol.control result.2)⟩ : PqxdhRecordLiftIdeal.View n E X) = _
  rw [raw, slots]
  rfl

/-- The record lift's view (`PqxdhRecordLiftIdeal.chainView`) of the key-free record protocol under the all-real lookup policy (`PqxdhRecordLiftProtocol.run` with `PqxdhRecordLiftWorldCompiler.realPolicy`) has the law of the annotated view of the provenance-annotated record world, for every environment: the adversary's output, the ledger, the environment state, the produced frames, the raw-attempt counters and the handle-to-slot map together. From `run_origins` and `PqxdhRecordLiftProtocol.run_factor`. -/
theorem protocol_view {E X : Type} (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftProtocol.run (PqxdhRecordLiftWorldCompiler.realPolicy setup codec)
        setup codec route env serverKid bounds mode adversary =
      annotatedView <$> PqxdhDeploymentIdealOrigins.annotatedRun setup codec route env serverKid bounds mode adversary := by
  rw [← run_origins setup codec route env serverKid bounds mode adversary, PqxdhRecordLiftProtocol.run_factor,
    Functor.map_map, Functor.map_map]
  congr 1
  funext result
  exact chainView_split result

/-- `protocol_view` for the all-real chain world (`PqxdhRecordLiftIdeal.realChains`, the chain hybrid with every coordinate real, whose lookup policy is the all-real one by `PqxdhRecordLiftMixedWorld.policy_real`). -/
theorem realChains_view {E X : Type} (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftIdeal.chainView <$>
        PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary =
      annotatedView <$> PqxdhDeploymentIdealOrigins.annotatedRun setup codec route env serverKid bounds mode adversary := by
  rw [PqxdhRecordLiftIdeal.realChains, PqxdhRecordLiftIdeal.chains, PqxdhRecordLiftMixedWorld.policy_real]
  exact protocol_view setup codec route env serverKid bounds mode adversary

/-- Design-v2 section 9.1's form of `run_origins`: on the all-real chain world, the CE-12 analysis projection of the view and the view's handle-to-slot map (`PqxdhRecordLiftIdeal.handleSlot` of the record control) have the joint law of the World's analysis projection (`PqxdhRecordLiftWorld.analysis`) and the annotation's handle-to-slot map on the provenance-annotated record world. -/
theorem realChains_analysis_slots {E X : Type} (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    (fun result => ((PqxdhRecordLiftIdeal.chainView result).analysis, (PqxdhRecordLiftIdeal.chainView result).slots)) <$>
        PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary =
      (fun result => (PqxdhRecordLiftWorld.analysis (result.1, result.2.1), originMap result.2.2)) <$>
        PqxdhDeploymentIdealOrigins.annotatedRun setup codec route env serverKid bounds mode adversary := by
  have viewed := congrArg (fun computation => (fun view : PqxdhRecordLiftIdeal.View n E X => (view.analysis, view.slots))
    <$> computation) (realChains_view setup codec route env serverKid bounds mode adversary)
  simp only [Functor.map_map] at viewed
  rw [viewed]
  congr 1
  funext result
  exact congrArg (fun analysis => (analysis, originMap result.2.2)) (annotatedView_analysis result)

/-- Every outcome of the all-real chain world has the view of an outcome of the provenance-annotated record world (the support form of `realChains_view`). -/
theorem realChains_support {E X : Type} (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : PqxdhRecordLiftProtocol.RunResult n E X)
    (member : result ∈ support (PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary)) :
    ∃ annotated ∈ support (PqxdhDeploymentIdealOrigins.annotatedRun setup codec route env serverKid bounds mode adversary),
      PqxdhRecordLiftIdeal.chainView result = annotatedView annotated := by
  have viewed : PqxdhRecordLiftIdeal.chainView result ∈ support (PqxdhRecordLiftIdeal.chainView <$>
      PqxdhRecordLiftIdeal.realChains setup codec route env serverKid bounds mode adversary) := by
    rw [support_map]
    exact ⟨result, member, rfl⟩
  rw [realChains_view, support_map] at viewed
  obtain ⟨annotated, annotatedMember, same⟩ := viewed
  exact ⟨annotated, annotatedMember, same.symm⟩

end Origins

/-! ### The per-target decision -/

section Decision
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- The per-target decision on an observation (design-v2 Appendix A, `decisionOn`): the event holds and the budgeted designation of the claim's handle is `g`. -/
noncomputable def decisionOn (budget : Budget) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (observed : Observed X) : Bool :=
  event observed && decide (PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim
    observed = some g)

/-- Item 2's decision on a result of the compiled program is `decisionOn` on the result's observation. -/
theorem decision_observe (budget : Budget) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) :
    PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g =
      fun result => decisionOn setup codec budget event claim g (PqxdhDeploymentKemTransfer.observeCompiled result) :=
  rfl

/-- The decision of the second compile lemma on an outcome of CE's ideal game (the event happens and the claim designates `g`, `PqxdhDeploymentIdealCompile.ideal_compile`) is `decisionOn` on the outcome's observed projection (the adversary's output, the ledger and the produced frames), false when no Server was constructed. -/
theorem ceDecide_observed {A Bk : Type} {n : ℕ} (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      PqxdhDeploymentBackend.XState KemSK Bk n) × A) :
    decide (PqxdhDeploymentKemTransfer.happens event (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
        PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
          (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g) =
      (outcome.1.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)).any
        (decisionOn setup codec budget event claim g) := by
  rcases outcome with ⟨_ | value, after⟩
  · simp [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentIdealBranch.classicalOf,
      PqxdhDeploymentKemTransfer.observeGame]
  · simp only [PqxdhDeploymentKemTransfer.happens, PqxdhDeploymentKemTransfer.designated,
      PqxdhDeploymentIdealBranch.classicalOf, PqxdhDeploymentKemTransfer.observeGame, Option.map_some, Option.any_some,
      Option.bind_some, decisionOn]
    rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff]
    exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- A Boolean observation that implies the disjunction of two others on the support is true with at most the sum of their probabilities. -/
theorem evalDist_le_add {α : Type} (mx : ProbComp α) (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (implies : ∀ a ∈ support mx, P a → Q a ∨ R a) :
    𝒟[(fun a => decide (P a)) <$> mx] {true} ≤
      𝒟[(fun a => decide (Q a)) <$> mx] {true} + 𝒟[(fun a => decide (R a)) <$> mx] {true} := by
  rw [evalDist_apply_singleton, evalDist_apply_singleton, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map, probEvent_map]
  exact probEvent_le_add_of_imp_or fun a member held => by
    simpa using implies a member (by simpa using held)

/-- The observation of a record-lift view (`PqxdhRecordLiftIdeal.View`): the adversary's output, the ledger and the produced frames. -/
def viewObserved {n : ℕ} {E : Type} (view : PqxdhRecordLiftIdeal.View n E X) : Option (Observed X) :=
  view.result.map fun value => (value.1, value.2.1, view.produced)

/-- The observation of the view of a chain-world run is the record lift's observation of the run. -/
theorem viewObserved_chainView {n : ℕ} {E : Type} (result : PqxdhRecordLiftProtocol.RunResult n E X) :
    viewObserved (PqxdhRecordLiftIdeal.chainView result) = PqxdhRecordLiftProtocol.observed result := by
  rcases result with ⟨⟨_ | value, control⟩, secret⟩ <;> rfl

/-- The observation of the annotated view is the World's observation of the erased outcome. -/
theorem viewObserved_annotated {n : ℕ} {E : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftOrigins.State n) :
    viewObserved (annotatedView result) = PqxdhRecordLiftWorld.observed (result.1, result.2.1) := by
  rcases result with ⟨_ | value, state⟩ <;> rfl

end Decision

/-! ### The hand-off theorems -/

section Handoff
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- `ideal_world` (design-v2 section 9.1): under the approved `Phase1ReadBack` and `Phase2ReadBack` and for every adversary within its budget, item 2's two-slot world of the compiled program (`PqxdhRegistrationJointKemSecondEntry.slotGame … 2` with item 2's decision) and the record world with the ideal environment of the target of `g` (`PqxdhDeploymentIdealEnv.envGD` at `Target.ofCE budget g`, identity index 0) give the per-target decision the same probability. From `PqxdhDeploymentIdealCompile.ideal_compile` and `PqxdhDeploymentIdealEnv.c1_idealGame` (C1 for CE's ideal game at the observed projection, which is all the decision reads, `ceDecide_observed`). -/
theorem ideal_world (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} := by
  rw [PqxdhDeploymentIdealCompile.ideal_compile setup codec route checks phase1 phase2 ensureInit bounds mode adversary
    budget respects event claim g runtime]
  have left : (fun outcome => decide (PqxdhDeploymentKemTransfer.happens event
        (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
        PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
          (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
      (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
        runtime =
      (fun observed => observed.any (decisionOn setup codec budget event claim g)) <$>
        ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
          (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run'
            runtime) := by
    rw [StateT.run'_eq, Functor.map_map, Functor.map_map]
    congr 1
    funext outcome
    exact ceDecide_observed setup codec budget event claim g outcome
  have right : (fun observed => observed.any (decisionOn setup codec budget event claim g)) <$>
      ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (PqxdhDeploymentEnvironmentJoin.joined <$> PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)) =
      (fun result => (PqxdhRecordLiftWorld.observed result).any (decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary := by
    simp only [Functor.map_map]
    congr 1
    funext result
    rcases result with ⟨_ | value, state⟩ <;> rfl
  rw [left, ← right]
  exact congrArg (fun measure => measure {true})
    ((PqxdhDeploymentIdealEnv.c1_idealGame setup codec route checks budget g ensureInit runtime bounds mode
      adversary).map _).evalDist_eq

open Classical in
/-- `ideal_world_slots` (design-v2 section 9.1), the equality form: `ideal_world` on the provenance-annotated record world with the ideal environment of the target of `g`, with C5 restated conjoined (`IdealSlots` for the annotation's handle-to-slot map, or the Beacon-side `Anomaly`; `PqxdhDeploymentIdealBeacon.ideal_slots`, which holds on every outcome, so the conjunct changes no probability). The annotated world erases to the record world (`PqxdhDeploymentIdealOrigins.annotatedRun_erase`). -/
theorem ideal_world_slots (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun result => decide ((PqxdhRecordLiftWorld.observed (result.1, result.2.1)).any
          (decisionOn setup codec budget event claim g) = true ∧
          ∀ value, result.1 = some value →
            IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) (originSlots result.2.2)
                value.2.1.2.transcript ∨
              Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} := by
  rw [ideal_world setup codec route checks phase1 phase2 ensureInit bounds mode adversary budget respects event claim g
    runtime, ← PqxdhDeploymentIdealOrigins.annotatedRun_erase, Functor.map_map]
  have same : (fun result => (PqxdhRecordLiftWorld.observed (Prod.map id Prod.fst result)).any
      (decisionOn setup codec budget event claim g)) <$> PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary =
      (fun result => decide ((PqxdhRecordLiftWorld.observed (result.1, result.2.1)).any
          (decisionOn setup codec budget event claim g) = true ∧
          ∀ value, result.1 = some value →
            IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) (originSlots result.2.2)
                value.2.1.2.transcript ∨
              Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    refine bind_congr_of_forall_mem_support _ fun result member => ?_
    have slots := PqxdhDeploymentIdealBeacon.ideal_slots setup codec route checks phase1 phase2 (Target.ofCE budget g)
      ensureInit 0 runtime bounds mode adversary result member
    refine congrArg pure ((Bool.eq_iff_iff).2 ?_)
    rw [decide_eq_true_iff]
    exact ⟨fun held => ⟨held, slots⟩, And.left⟩
  rw [same]

open Classical in
/-- `ideal_world_slots` (design-v2 section 9.1), the bound form on the provenance-annotated record world: the probability of item 2's two-slot world is at most the probability that the per-target decision holds with `IdealSlots` for the annotation's handle-to-slot map, plus the probability of the Beacon-side `Anomaly` on the record world with the same environment (which `PqxdhDeploymentIdealAnomalyBound.anomaly_le` bounds by `ctGuess`; `ideal_world_slots_ct`). -/
theorem ideal_world_slots_le (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} ≤
      𝒟[(fun result => decide ((PqxdhRecordLiftWorld.observed (result.1, result.2.1)).any
          (decisionOn setup codec budget event claim g) = true ∧
          ∀ value, result.1 = some value →
            IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) (originSlots result.2.2)
              value.2.1.2.transcript)) <$>
        PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} +
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} := by
  rw [ideal_world_slots setup codec route checks phase1 phase2 ensureInit bounds mode adversary budget respects event
    claim g runtime, ← PqxdhDeploymentIdealOrigins.annotatedRun_erase, Functor.map_map]
  refine evalDist_le_add _ _ _ _ fun result _ held => ?_
  by_cases slotted : ∀ value, result.1 = some value →
      IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) (originSlots result.2.2)
        value.2.1.2.transcript
  · exact Or.inl ⟨held.1, slotted⟩
  · obtain ⟨value, unslotted⟩ := Classical.not_forall.mp slotted
    obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
    exact Or.inr ⟨value, found, (held.2 value found).resolve_left failed⟩

open Classical in
/-- `ideal_world_slots_le` with the anomaly bounded by `ctGuess` (`PqxdhDeploymentIdealAnomalyBound.anomaly_le`): design-v2 section 9.1's `𝒟[D_g ∧ ¬IdealSlots] ≤ ctGuess setup` in the form CE-12 composes. -/
theorem ideal_world_slots_ct (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} ≤
      𝒟[(fun result => decide ((PqxdhRecordLiftWorld.observed (result.1, result.2.1)).any
          (decisionOn setup codec budget event claim g) = true ∧
          ∀ value, result.1 = some value →
            IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) (originSlots result.2.2)
              value.2.1.2.transcript)) <$>
        PqxdhDeploymentIdealOrigins.annotatedRun setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} + PqxdhDeploymentIdealTrace.ctGuess setup :=
  (ideal_world_slots_le setup codec route checks phase1 phase2 ensureInit bounds mode adversary budget respects event
    claim g runtime).trans (add_le_add le_rfl (PqxdhDeploymentIdealAnomalyBound.anomaly_le setup codec route checks phase1
      phase2 (Target.ofCE budget g) ensureInit 0 runtime setup.serverKeyId bounds mode adversary))

/-- C5 restated on the record lift's own view (design-v2 section 7.4: C5 is needed on the real world only): under `Phase1ReadBack` and `Phase2ReadBack`, on every outcome of the all-real chain world (`PqxdhRecordLiftIdeal.realChains`) with the ideal environment of a target, the view's handle-to-slot map (`PqxdhRecordLiftIdeal.handleSlot` of the record control) satisfies `IdealSlots`, or the transcript has the Beacon-side `Anomaly`. From `realChains_support` (`run_origins`) and `PqxdhDeploymentIdealBeacon.ideal_slots`. -/
theorem ideal_view_slots (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) {count : ℕ} (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (PqxdhRecordLiftIdeal.realChains setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary),
      ∀ value, (PqxdhRecordLiftIdeal.chainView result).result = some value →
        IdealSlots setup.source.crypto codec setup.serverKeyId t (PqxdhRecordLiftIdeal.chainView result).slots
            value.2.1.transcript ∨
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.transcript := by
  intro result member value found
  obtain ⟨annotated, annotatedMember, same⟩ := realChains_support setup codec route _ setup.serverKeyId bounds mode
    adversary result member
  rw [same] at found ⊢
  rcases annotated with ⟨_ | inner, state⟩
  · exact absurd found (by simp [annotatedView])
  · simp only [annotatedView, Option.map_some, Option.some.injEq] at found
    subst found
    have slots := PqxdhDeploymentIdealBeacon.ideal_slots setup codec route checks phase1 phase2 t ensureInit
      identityIndex runtime bounds mode adversary _ annotatedMember inner rfl
    rw [← originMap_two] at slots
    exact slots

/-- `ideal_world_view` (design-v2 section 9.1, the View form): `ideal_world` on the record lift's view of the all-real chain world (`PqxdhRecordLiftIdeal.realChains`, the frozen record world, `PqxdhRecordLiftIdeal.realChains_game`) with the ideal environment of the target of `g`. -/
theorem ideal_world_view (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun view => (viewObserved view).any (decisionOn setup codec budget event claim g)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftIdeal.realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} := by
  rw [ideal_world setup codec route checks phase1 phase2 ensureInit bounds mode adversary budget respects event claim g
    runtime, Functor.map_map]
  have viewed := congrArg (fun computation => (fun observed => observed.any (decisionOn setup codec budget event claim g))
    <$> computation) (PqxdhRecordLiftIdeal.realChains_game setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId
      bounds mode adversary)
  simp only [PqxdhRecordLiftWorld.game, Functor.map_map] at viewed
  rw [← viewed]
  simp only [viewObserved_chainView]

open Classical in
/-- `ideal_world_slots` on the record lift's view (design-v2 section 9.2, the step CE-12 takes before the record lift): under `Phase1ReadBack` and `Phase2ReadBack`, for every adversary within its budget, the probability of item 2's two-slot world is at most the probability that the per-target decision holds with `IdealSlots` for the view's handle-to-slot map on the all-real chain world with the ideal environment of the target of `g`, plus the probability of the Beacon-side `Anomaly` on the record world with that environment. Every bound on that anomaly applies (`PqxdhDeploymentIdealAnomalyBound.anomaly_le` gives `ctGuess`, `ideal_world_view_ct`). -/
theorem ideal_world_view_slots (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} ≤
      𝒟[(fun view => decide ((viewObserved view).any (decisionOn setup codec budget event claim g) = true ∧
          ∀ value, view.result = some value →
            IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) view.slots
              value.2.1.transcript)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftIdeal.realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} +
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} := by
  have anomalies : 𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary] {true} =
      𝒟[(fun view => decide (∃ value, view.result = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.transcript)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftIdeal.realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} := by
    rw [realChains_view, ← PqxdhDeploymentIdealOrigins.annotatedRun_erase, Functor.map_map, Functor.map_map]
    congr 3
    funext annotated
    rcases annotated with ⟨_ | inner, state⟩
    · simp [annotatedView]
    · simp [annotatedView]
  rw [anomalies, ideal_world_view setup codec route checks phase1 phase2 ensureInit bounds mode adversary budget respects
    event claim g runtime]
  refine Eq.trans_le ?_ (evalDist_le_add _ (fun view => (viewObserved view).any
    (decisionOn setup codec budget event claim g) = true) _ _ fun view member held => ?_)
  · simp only [Bool.decide_eq_true]
  rw [support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  by_cases slotted : ∀ value, (PqxdhRecordLiftIdeal.chainView result).result = some value →
      IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g)
        (PqxdhRecordLiftIdeal.chainView result).slots value.2.1.transcript
  · exact Or.inl ⟨held, slotted⟩
  · obtain ⟨value, unslotted⟩ := Classical.not_forall.mp slotted
    obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
    exact Or.inr ⟨value, found, (ideal_view_slots setup codec route checks phase1 phase2 (Target.ofCE budget g)
      ensureInit 0 runtime bounds mode adversary result resultMember value found).resolve_left failed⟩

open Classical in
/-- `ideal_world_view_slots` with the anomaly bounded by `ctGuess` (`PqxdhDeploymentIdealAnomalyBound.anomaly_le`): design-v2 section 9.2's step `Pr[D_g on realChains (envGD g)] ≤ Pr[(D_g ∧ IdealSlots) on realChains (envGD g)] + ctGuess`, with item 2's two-slot world in place of its equal left side. -/
theorem ideal_world_view_ct (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} ≤
      𝒟[(fun view => decide ((viewObserved view).any (decisionOn setup codec budget event claim g) = true ∧
          ∀ value, view.result = some value →
            IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) view.slots
              value.2.1.transcript)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftIdeal.realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} + PqxdhDeploymentIdealTrace.ctGuess setup :=
  (ideal_world_view_slots setup codec route checks phase1 phase2 ensureInit bounds mode adversary budget respects event
    claim g runtime).trans (add_le_add le_rfl (PqxdhDeploymentIdealAnomalyBound.anomaly_le setup codec route checks phase1
      phase2 (Target.ofCE budget g) ensureInit 0 runtime setup.serverKeyId bounds mode adversary))

end Handoff

end BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.originMap_two' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.originMap_two

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.annotatedView_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.annotatedView_analysis

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.handler_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.handler_project

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.schedule_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.schedule_project

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.run_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.run_origins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.chainView_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.chainView_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.protocol_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.protocol_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.realChains_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.realChains_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.realChains_analysis_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.realChains_analysis_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.realChains_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.realChains_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.decision_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.decision_observe

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ceDecide_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ceDecide_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.evalDist_le_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.evalDist_le_add

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.viewObserved_chainView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.viewObserved_chainView

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.viewObserved_annotated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.viewObserved_annotated

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_slots_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_slots_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_slots_ct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_slots_ct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_view_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_view_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_view_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_view_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_view_ct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff.ideal_world_view_ct
