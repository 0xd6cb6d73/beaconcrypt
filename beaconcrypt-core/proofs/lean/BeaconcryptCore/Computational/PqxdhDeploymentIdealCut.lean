-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource

/-!
# The prefix of the second compile lemma, cut at the selected accept (CE-11b, unit U5)

The second compile lemma of CE-11b (design-v2 section 8) compares `CE.idealGame g` with item 2's two-slot ideal world, pointwise in the challenger's draws `p` (route P-a). This module cuts both sides at the selected raw accept (ordinal `t.accept`) and shows that, up to that cut, both are images of one computation: the Server construction (item 2's annotated birth `PqxdhRegistrationJointServerBirth.source`) followed by the annotated pool source execution of the compiled CE scan (`commonPrefix`).

- The CE-side scan (`scanCE`, `finishCE`, `scanCE_finish`, `run_scanCE`): a deployment program run up to its raw accept at a position, which is returned unissued with its continuation; resuming gives the program back. Item 2's source accept scan of CE-3's compiled program is the compiled CE scan (`compile_scan`, `compileCut`), because the compiler forwards each raw accept as exactly one source14 raw accept and no other command issues one (`compile_noAccept`, from CE-3's per-kind budget).
- Before the cut the ideal registration is the real one with the pool create: every request other than the selected accept, from a state in which the selected accept has not run, projects to the native deployment handler with the pool create (`preStep`), and so does the scan up to the selected accept (`preScan`), with the backend changed only in its accept counter. The LQ-F ghosts (the Server ephemeral log and the finish snapshot) are written but never read, so no run of the ideal handler depends on them (`idealRun_unghost`). Hence the ideal game is the pool scan followed by the ideal game resumed from a canonical state at the cut (`cutState`, `resumeAt`, `ideal_cut`).
- The pool scan is the erasure of the annotated pool source execution of the compiled scan (`pool_scan_source`, from `PqxdhDeploymentIdealPool.compile_native_pool` and `PqxdhDeploymentIdealPoolSource.programPool_native`), and the source prefix of item 2's opaque scan under the stopped selected-first router at the pool is its encoding (`stopped_scan_source`, from `compile_scan` and `PqxdhDeploymentIdealPoolSource.kemCommands_stopped`).
- `ideal_prefix`: the common deployment experiment with the ideal registration at `p` is the Server construction, then `commonPrefix`, then `resumeAt` on the merged deployment state. `item2_prefix`: item 2's prephase at the drawn family (`PqxdhDeploymentIdealParams.preOpaquePool`) for the compiled program is the same construction, then `commonPrefix`, then the rest of item 2's opaque scan (`opaqueRest`, `opaqueScan_split`) under the stopped router from the compiled cut and the encoded state.
- `CutRel` and `cut_rel`: on every outcome of the common prefix, the source-side invariant at the pool holds (`cut_owned`), the compiled program's local copies and the erased source state satisfy CE-3's merge invariant (`cut_good`), and the KEM pool holds the first entries of the challenger's pool, at most as many as the budget's creations (`cut_prefix`). This is where the post-challenge phase (unit U6) starts: the selected accept's verification and the steps before its encapsulation are in `opaqueRest` on item 2's side and in `acceptExposed` on the CE side.

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` (through CE-3's compile lemma and invariant) and, on item 2's side, a source budget for item 2's scan of the compiled program that reads no identity or KEM field and creates no more KEM keys than the pool holds (the CE budget gives one; CE-11b's `ideal_compile` instantiates it). These are program equalities and support facts. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealCut
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl logReply)
open PqxdhRegistrationJointAcceptCut (Cut scan)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-! ### The CE-side scan -/

/-- A deployment program cut at a raw accept: either it completed before it, or the raw bytes of that accept and its continuation. -/
inductive CutCE (X : Type) where
  | complete (result : X)
  | pending (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec X)

/-- The CE-side scan (`PqxdhRegistrationJointAcceptCut.scan` for deployment programs): run the program, forwarding every request, up to its raw accept at zero-based position `index`, and return that accept's raw bytes and continuation without issuing it. -/
noncomputable def scanCE (work : OracleComp Spec X) : ℕ → OracleComp Spec (CutCE X) :=
  OracleComp.recOn work
    (fun result _ => pure (.complete result))
    (fun query next recurse index => match query with
      | .inr (.accept raw) => match index with
        | 0 => pure (.pending raw next)
        | index + 1 => do
          let answer ← (Spec.query (.inr (.accept raw)) : OracleComp Spec _)
          recurse answer index
      | query => do
        let answer ← (Spec.query query : OracleComp Spec _)
        recurse answer index)

/-- Resume a cut: issue the suspended raw accept and run its continuation. -/
noncomputable def finishCE : CutCE X → OracleComp Spec X
  | .complete result => pure result
  | .pending raw next => (Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= next

/-- Scanning and resuming give the program back. -/
theorem scanCE_finish (work : OracleComp Spec X) (index : ℕ) : (scanCE work index >>= finishCE) = work := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure result => rfl
  | query_bind query next ih =>
    rcases query with coin | command
    · change (((Spec.query (.inl coin) : OracleComp Spec _) >>= fun answer => scanCE (next answer) index) >>=
        finishCE) = _
      simp only [bind_assoc, ih]
    · cases command
      all_goals first
        | change (((Spec.query _ : OracleComp Spec _) >>= fun answer => scanCE (next answer) index) >>= finishCE) = _
          simp only [bind_assoc, ih]
        | skip
      cases index with
      | zero => rfl
      | succ index =>
        change (((Spec.query _ : OracleComp Spec _) >>= fun answer => scanCE (next answer) index) >>= finishCE) = _
        simp only [bind_assoc, ih]

/-- Under any handler, the program's run is the run of its scan followed by the run of the resumption from the reached state. -/
theorem run_scanCE {σ : Type} (impl : QueryImpl Spec (StateT σ ProbComp)) (work : OracleComp Spec X) (index : ℕ)
    (state : σ) :
    (simulateQ impl work).run state =
      (simulateQ impl (scanCE work index)).run state >>= fun reached =>
        (simulateQ impl (finishCE reached.1)).run reached.2 := by
  conv_lhs => rw [← scanCE_finish work index]
  rw [simulateQ_bind, StateT.run_bind]


/-- The scan of a completed program completes. -/
theorem scanCE_pure (value : X) (index : ℕ) : scanCE (pure value : OracleComp Spec X) index = pure (.complete value) :=
  rfl

/-- The scan stops at the raw accept of position zero. -/
theorem scanCE_accept_zero (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec X) :
    scanCE ((Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= next) 0 = pure (.pending raw next) := rfl

/-- The scan issues a raw accept before the cut position and continues with the next position. -/
theorem scanCE_accept_succ (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec X) (index : ℕ) :
    scanCE ((Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= next) (index + 1) =
      (Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= fun answer => scanCE (next answer) index := rfl

/-- The scan issues every request other than a raw accept and continues at the same position. -/
theorem scanCE_other (query : Spec.Domain) (other : PqxdhDeploymentCompileBudget.commandKind query ≠ 3)
    (next : Spec.Range query → OracleComp Spec X) (index : ℕ) :
    scanCE ((Spec.query query : OracleComp Spec _) >>= next) index =
      (Spec.query query : OracleComp Spec _) >>= fun answer => scanCE (next answer) index := by
  rcases query with coin | command
  · rfl
  · cases command with
    | accept raw => exact absurd rfl other
    | _ => rfl

/-! ### The compiled program of a scan -/

/-- The source14 accept scan passes a request other than a raw accept. -/
theorem scan_query_other (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 3) {β : Type}
    (next : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query →
      OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) β) (index : ℕ) :
    scan (((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query :
        OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= next) index =
      ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query :
        OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= fun answer => scan (next answer) index := by
  rcases query with (coin | request) | read
  · rfl
  · cases request with
    | accept raw => exact absurd rfl other
    | _ => rfl
  · rfl

/-- The source14 accept scan passes a program without raw accept. -/
theorem scan_bind_noAccept {α β : Type} (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α)
    (none : work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 3) 0)
    (next : α → OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) β) (index : ℕ) :
    scan (work >>= next) index = work >>= fun answer => scan (next answer) index := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [pure_bind]
  | query_bind query rest ih =>
      rw [isQueryBoundP_query_bind_iff] at none
      have other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 3 := by
        intro accept
        rcases none.1 with absent | impossible
        · exact absent accept
        · exact absurd impossible (Nat.lt_irrefl 0)
      rw [bind_assoc, scan_query_other query other, bind_assoc]
      refine bind_congr fun answer => ih answer ?_
      simpa only [other, ↓reduceIte] using none.2 answer

section Compile
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Every deployment command other than a raw accept compiles to a source14 program without raw accept (CE-3's per-kind budget at the accept class). -/
theorem compile_noAccept (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local)
    (other : PqxdhDeploymentCompileBudget.commandKind query ≠ 3) :
    ((compileImpl setup codec route query).run copies).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
  have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) query copies
  have zero : PqxdhDeploymentCompileBudget.cost (.inl 3) (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
    rcases query with coin | command
    · rfl
    · cases command <;> first | rfl | exact absurd rfl other
  rwa [zero] at bound

/-- The compiled form of a CE cut: a completed program with its local copies, or the raw bytes of the suspended accept with the compiled continuation, which logs the accept's reply first (as `compileImpl` does). -/
noncomputable def compileCut : CutCE X × Local → Cut KemSK (X × Local)
  | (.complete result, copies) => .complete (result, copies)
  | (.pending raw next, copies) => .pending raw fun answer =>
      (simulateQ (compileImpl setup codec route) (next answer)).run
        { copies with log := logReply copies.log (.accept raw) answer }

/-- The source14 accept scan of a compiled program at position `index` is the compiled CE scan at the same position (`compileImpl` forwards each raw accept as exactly one source14 raw accept and issues no other). -/
theorem compile_scan (work : OracleComp Spec X) (index : ℕ) (copies : Local) :
    scan ((simulateQ (compileImpl setup codec route) work).run copies) index =
      compileCut setup codec route <$> (simulateQ (compileImpl setup codec route) (scanCE work index)).run copies := by
  induction work using OracleComp.inductionOn generalizing index copies with
  | pure result => rfl
  | query_bind query next ih =>
    by_cases accept : PqxdhDeploymentCompileBudget.commandKind query = 3
    · rcases query with coin | command
      · exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
      · cases command with
        | accept raw =>
            cases index with
            | zero => rfl
            | succ index =>
                have scanned : scanCE ((Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= next) (index + 1) =
                    (Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= fun answer => scanCE (next answer) index :=
                  rfl
                rw [scanned, simulateQ_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_bind,
                  map_bind]
                simp only [compileImpl, PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward,
                  StateT.run, bind_assoc, pure_bind, id]
                change ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) >>= fun answer =>
                  scan ((simulateQ (compileImpl setup codec route) (next answer)).run
                    { copies with log := logReply copies.log (.accept raw) answer }) index :
                  OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) = _
                exact bind_congr fun answer => ih answer index _
        | _ => exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
    · have shape : (simulateQ (compileImpl setup codec route) ((Spec.query query : OracleComp Spec _) >>= next)).run
          copies = (compileImpl setup codec route query).run copies >>= fun reached =>
            (simulateQ (compileImpl setup codec route) (next reached.1)).run reached.2 := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have scanned : scanCE ((Spec.query query : OracleComp Spec _) >>= next) index =
          (Spec.query query : OracleComp Spec _) >>= fun answer => scanCE (next answer) index := by
        rcases query with coin | command
        · rfl
        · cases command with
          | accept raw => exact absurd rfl accept
          | _ => rfl
      rw [shape, scan_bind_noAccept _ (compile_noAccept setup codec route query copies accept), scanned,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      exact bind_congr fun reached => ih reached.1 index reached.2

end Compile


/-! ### The ideal registration before the cut -/

section Pre
open PqxdhDeploymentBackend (XState RegImpl handlerWith)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore detach attach)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS IdealCore IdealBk TableState idealReg idealProg createPool)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPool (deploymentPool)

/-- The allocator passes coins through: a lifted probabilistic computation keeps the allocator and the service state. -/
theorem slotImpl_lift {S α : Type} {n : ℕ} (svc : PqxdhDeploymentSeedSplit.SlotService S n) (work : ProbComp α)
    (state : PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × S) :
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl svc) (liftS work)).run state =
      (fun a => (a, state)) <$> work := by
  rw [liftS, QueryImpl.simulateQ_liftComp_left_eq_of_apply (PqxdhRegistrationJointKemSecondEntry.slotImpl svc)
    (fun query => StateT.mk fun current => (fun reply => (reply, current)) <$> (unifSpec.query query : ProbComp _))
    (fun query => by funext current; exact PqxdhRegistrationJointKemSecondEntry.slot_coin svc query current)]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, StateT.run_mk, bind_map_left, map_bind]
      refine bind_congr fun reply => ?_
      exact ih reply state

/-- A slot-core command whose slot program runs a coins-only computation on the detached state is that computation with the allocator and the service state reattached. -/
theorem slotCore_lift {Γ : Type} {n : ℕ} (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery)
    (x : XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × Γ)) n)
    (work : ProbComp (PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK Γ n))
    (shape : (prog created query).run (detach x) = liftS work) :
    (slotCore prog svc created query).run x = (fun r => (r.1, attach r.2 x.backend.2.1 x.backend.1)) <$> work := by
  rw [PqxdhDeploymentIdealSlots.slotCore_run, shape, slotImpl_lift, Functor.map_map]

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- `realRegAt` projects to the native deployment handler on the deployment state (`PqxdhDeploymentLaterServerGame.handler_erase`). -/
theorem realRegAt_base {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK Bk n) :
    Prod.map id XState.base <$> (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x =
      (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val)).run x.base := by
  rw [← PqxdhDeploymentLaterServerGame.handler_erase setup codec checks route created.seed (.inr query.val) x.base x.log]
  simp only [realRegAt, StateT.run, Functor.map_map]
  rfl

/-- `realRegAt` keeps the backend and the seed table. -/
theorem realRegAt_keeps {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK Bk n)
    (result : PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK Bk n)
    (supported : result ∈ support ((realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x)) :
    result.2.backend = x.backend ∧ result.2.seeds = x.seeds := by
  simp only [realRegAt, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact ⟨rfl, rfl⟩


variable {count : ℕ} (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- The ideal backend before the cut: the selected accept has not been active and no session is marked. -/
def PreCut (x : XState KemSK (IdealBk TableState) 2) : Prop :=
  x.backend.2.2.active = false ∧ x.backend.2.2.marks = none

/-- The ideal backend after one request before the cut: a raw accept advances the accept counter, every other request keeps the backend. -/
def bump : Spec.Domain → IdealBk TableState → IdealBk TableState
  | .inr (.accept _), backend => (backend.1, (backend.2.1, { backend.2.2 with accepts := backend.2.2.accepts + 1 }))
  | _, backend => backend

/-- A base step of the extended state projects to the step on the deployment state and keeps the backend and the seed table. -/
theorem onBase_base {Bk : Type} {n : ℕ} {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (x : XState KemSK Bk n) :
    Prod.map id XState.base <$> (PqxdhDeploymentBackend.onBase step).run x = step.run x.base ∧
      ∀ result ∈ support ((PqxdhDeploymentBackend.onBase step).run x), result.2.backend = x.backend ∧
        result.2.seeds = x.seeds := by
  refine ⟨?_, ?_⟩
  · simp only [PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift, StateT.run, Functor.map_map]
    exact id_map _
  · intro result member
    simp only [PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact ⟨rfl, rfl⟩

/-- A slot-core command of the ideal registration whose slot program runs a coins-only step projects to that step's target on the deployment state and keeps the allocator, the service state and the seed table. -/
theorem idealReg_lift (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK (IdealBk TableState) 2)
    (y : XState KemSK IdealCore 2) (step : StateT (XState KemSK IdealCore 2) ProbComp
      (PqxdhRecordLiftInterface.EnvSpec.Range query))
    (target : StateT (PqxdhDeploymentNative.State KemSK) ProbComp (PqxdhRecordLiftInterface.EnvSpec.Range query))
    (shape : (idealProg setup codec route checks t p (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
      created query).run (detach x) = liftS (step.run y))
    (seeds : y.seeds = x.seeds)
    (stepBase : Prod.map id XState.base <$> step.run y = target.run x.base)
    (stepKeeps : ∀ result ∈ support (step.run y), result.2.backend = y.backend ∧ result.2.seeds = y.seeds) :
    Prod.map id XState.base <$> (idealReg setup codec route checks t p created query).run x = target.run x.base ∧
      ∀ result ∈ support ((idealReg setup codec route checks t p created query).run x),
        result.2.backend = (x.backend.1, (x.backend.2.1, y.backend)) ∧ result.2.seeds = x.seeds := by
  have run := slotCore_lift (idealProg setup codec route checks t p
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)) PqxdhDeploymentSeedSplit.tableService
    created query x (step.run y) shape
  change (slotCore _ PqxdhDeploymentSeedSplit.tableService created query).run x = _ at run
  refine ⟨?_, ?_⟩
  · change Prod.map id XState.base <$> (slotCore _ PqxdhDeploymentSeedSplit.tableService created query).run x = _
    rw [run, Functor.map_map, ← stepBase]
    rfl
  · intro result member
    change result ∈ support ((slotCore _ PqxdhDeploymentSeedSplit.tableService created query).run x) at member
    rw [run, support_map] at member
    obtain ⟨reached, reachedMember, rfl⟩ := member
    obtain ⟨keeps, seedsKept⟩ := stepKeeps reached reachedMember
    exact ⟨by simp only [attach, keeps], by simp only [attach, seedsKept, seeds]⟩

/-- A real registration command of the ideal registration (`realRegAt`, as a coins-only slot step) projects to the native handler and keeps the backend and the seed table. -/
theorem idealReg_real (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK (IdealBk TableState) 2)
    (y : XState KemSK IdealCore 2)
    (shape : (idealProg setup codec route checks t p (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)
      created query).run (detach x) = liftS ((realRegAt setup codec route checks created query).run y))
    (base : y.base = x.base) (seeds : y.seeds = x.seeds) :
    Prod.map id XState.base <$> (idealReg setup codec route checks t p created query).run x =
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val)).run x.base ∧
      ∀ result ∈ support ((idealReg setup codec route checks t p created query).run x),
        result.2.backend = (x.backend.1, (x.backend.2.1, y.backend)) ∧ result.2.seeds = x.seeds :=
  idealReg_lift setup codec route checks t p created query x y _ _ shape seeds
    (by rw [realRegAt_base, base]) (realRegAt_keeps setup codec route checks created query y)

/-- One request of the handler with the ideal registration before the cut (the selected accept has not run: inactive, no marked session, and the request is not the selected accept) projects to the native deployment handler with the pool create and keeps the allocator, the service state and the seed table; only a raw accept advances the accept counter. -/
theorem preStep (query : Spec.Domain) (x : XState KemSK (IdealBk TableState) 2) (pre : PreCut x)
    (notSelected : ∀ raw, query = .inr (.accept raw) → x.backend.2.2.accepts ≠ t.accept) :
    Prod.map id XState.base <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x =
      (deploymentPool setup codec checks route created.seed (p.pool t) query).run x.base ∧
      ∀ result ∈ support ((handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x),
        result.2.backend = bump query x.backend ∧ result.2.seeds = x.seeds := by
  rcases query with coin | command
  · refine ⟨?_, ?_⟩
    · simp only [handlerWith, deploymentPool, PqxdhDeploymentNative.handler, StateT.run_lift]
      rfl
    · intro result member
      simp only [handlerWith, StateT.run_lift, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at member
      obtain ⟨_, _, rfl⟩ := member
      exact ⟨rfl, rfl⟩
  · cases command with
    | create pin keyId =>
        have base := onBase_base (Bk := IdealCore) (n := 2) (match PqxdhDeploymentInterface.parsePin pin with
          | none => pure none
          | some word => some <$> PqxdhDeploymentNative.onNative (createPool setup (p.pool t) word keyId)) (detach x)
        exact idealReg_lift setup codec route checks t p created ⟨.create pin keyId, trivial⟩ x (detach x)
          (PqxdhDeploymentIdealSteps.createReg setup (p.pool t) pin keyId) _ rfl rfl base.1 base.2
    | bundle owner =>
        exact idealReg_real setup codec route checks t p created ⟨.bundle owner, trivial⟩ x (detach x) rfl rfl rfl
    | accept raw =>
        have other := notSelected raw rfl
        exact idealReg_real setup codec route checks t p created ⟨.accept raw, trivial⟩ x
          { detach x with backend := { (detach x).backend with accepts := (detach x).backend.accepts + 1 } }
          (PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw (detach x) other) rfl rfl
    | build session payload =>
        exact idealReg_real setup codec route checks t p created ⟨.build session payload, trivial⟩ x (detach x)
          (PqxdhDeploymentIdealSteps.buildStep_unmarked setup codec route checks _ created session payload (detach x)
            pre.2) rfl rfl
    | finish owner raw =>
        exact idealReg_real setup codec route checks t p created ⟨.finish owner raw, trivial⟩ x (detach x)
          (PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p _ created owner raw (detach x)
            (by simp [detach, pre.1])) rfl rfl
    | hmac key message =>
        exact idealReg_real setup codec route checks t p created ⟨.hmac key message, trivial⟩ x (detach x) rfl rfl rfl
    | hash bytes => exact onBase_base _ x
    | serverSend keyId plaintext => exact onBase_base _ x
    | serverRaw raw => exact onBase_base _ x
    | beaconSend owner plaintext => exact onBase_base _ x
    | beaconRaw owner raw => exact onBase_base _ x

/-- An ideal backend with its accept counter replaced. -/
def withAccepts (backend : IdealBk TableState) (accepts : ℕ) : IdealBk TableState :=
  (backend.1, (backend.2.1, { backend.2.2 with accepts := accepts }))

/-- The ideal registration before the cut (route P-a, the CE side of the prefix): the scan of a deployment program up to its raw accept at position `index`, run by the handler with the ideal registration from a state before the cut whose accept counter plus `index` is at most the selected ordinal, projects to the scan's run by the native deployment handler with the pool create; on every outcome the backend differs from the starting one only in the accept counter, which a suspended accept has advanced by exactly `index`, and the seed table is unchanged. -/
theorem preScan (work : OracleComp Spec X) (index : ℕ) (x : XState KemSK (IdealBk TableState) 2) (pre : PreCut x)
    (room : x.backend.2.2.accepts + index ≤ t.accept) :
    Prod.map id XState.base <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
          (scanCE work index)).run x =
      (simulateQ (deploymentPool setup codec checks route created.seed (p.pool t)) (scanCE work index)).run x.base ∧
      ∀ result ∈ support ((simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
          (scanCE work index)).run x),
        ∃ accepts, result.2.backend = withAccepts x.backend accepts ∧ result.2.seeds = x.seeds ∧
          ∀ raw next, result.1 = .pending raw next → accepts = x.backend.2.2.accepts + index := by
  induction work using OracleComp.inductionOn generalizing index x with
  | pure value =>
      rw [scanCE_pure]
      refine ⟨by simp, ?_⟩
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨x.backend.2.2.accepts, rfl, rfl, fun _ _ impossible => by cases impossible⟩
  | query_bind query next ih =>
      by_cases accept : PqxdhDeploymentCompileBudget.commandKind query = 3
      · rcases query with coin | command
        · exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
        · cases command with
          | accept raw =>
              cases index with
              | zero =>
                  rw [scanCE_accept_zero]
                  refine ⟨by simp, ?_⟩
                  intro result member
                  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
                  subst member
                  exact ⟨x.backend.2.2.accepts, rfl, rfl, fun _ _ _ => rfl⟩
              | succ index =>
                  have other : x.backend.2.2.accepts ≠ t.accept := by omega
                  have step := preStep setup codec route checks t p created (.inr (.accept raw)) x pre
                    (fun _ same => by cases same; exact other)
                  rw [scanCE_accept_succ]
                  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
                  refine ⟨?_, ?_⟩
                  · rw [map_bind, ← step.1, bind_map_left]
                    refine bind_congr_of_forall_mem_support _ fun reached member => ?_
                    obtain ⟨backend, seeds⟩ := step.2 reached member
                    have reachedPre : PreCut reached.2 := by
                      simp only [PreCut, backend, bump]
                      exact pre
                    have reachedRoom : reached.2.backend.2.2.accepts + index ≤ t.accept := by
                      simp only [backend, bump]
                      omega
                    exact (ih reached.1 index reached.2 reachedPre reachedRoom).1
                  · intro result member
                    rw [mem_support_bind_iff] at member
                    obtain ⟨reached, reachedMember, member⟩ := member
                    obtain ⟨backend, seeds⟩ := step.2 reached reachedMember
                    have reachedPre : PreCut reached.2 := by
                      simp only [PreCut, backend, bump]
                      exact pre
                    have reachedRoom : reached.2.backend.2.2.accepts + index ≤ t.accept := by
                      simp only [backend, bump]
                      omega
                    obtain ⟨accepts, resultBackend, resultSeeds, pending⟩ :=
                      (ih reached.1 index reached.2 reachedPre reachedRoom).2 result member
                    refine ⟨accepts, ?_, resultSeeds.trans seeds, fun raw' next' cut => ?_⟩
                    · rw [resultBackend, backend]
                      rfl
                    · rw [pending raw' next' cut, backend]
                      simp only [bump]
                      omega
          | _ => exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
      · have step := preStep setup codec route checks t p created query x pre
          (fun raw same => by subst same; exact absurd rfl accept)
        have kept : bump query x.backend = x.backend := by
          rcases query with coin | command
          · rfl
          · cases command with
            | accept raw => exact absurd rfl accept
            | _ => rfl
        rw [scanCE_other query accept]
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        refine ⟨?_, ?_⟩
        · rw [map_bind, ← step.1, bind_map_left]
          refine bind_congr_of_forall_mem_support _ fun reached member => ?_
          obtain ⟨backend, seeds⟩ := step.2 reached member
          rw [kept] at backend
          have reachedPre : PreCut reached.2 := by
            simp only [PreCut, backend]
            exact pre
          exact (ih reached.1 index reached.2 reachedPre (by rw [backend]; exact room)).1
        · intro result member
          rw [mem_support_bind_iff] at member
          obtain ⟨reached, reachedMember, member⟩ := member
          obtain ⟨backend, seeds⟩ := step.2 reached reachedMember
          rw [kept] at backend
          have reachedPre : PreCut reached.2 := by
            simp only [PreCut, backend]
            exact pre
          obtain ⟨accepts, resultBackend, resultSeeds, pending⟩ :=
            (ih reached.1 index reached.2 reachedPre (by rw [backend]; exact room)).2 result member
          exact ⟨accepts, by rw [resultBackend, backend], resultSeeds.trans seeds,
            fun raw next cut => by rw [pending raw next cut, backend]⟩

end Pre


/-! ### The LQ-F ghosts do not steer the ideal registration -/

section Ghost
open PqxdhDeploymentBackend (XState RegImpl handlerWith)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore detach attach)
open PqxdhDeploymentIdealSteps (realRegAt onSlots liftS IdealCore IdealBk TableState idealReg idealProg)
open PqxdhDeploymentIdealParams (Target Params)

/-- An extended state with the LQ-F ghosts (the finish snapshot and the Server ephemeral log) reset. -/
def unghost {Bk : Type} {n : ℕ} (x : XState KemSK Bk n) : XState KemSK Bk n :=
  { x with snap := PqxdhDeploymentLater.Snap.empty, log := [] }

/-- If one step of a handler, after resetting a state component with an idempotent map, does not depend on that component of its input, then neither does the run of any program. -/
theorem run_reset {ι' σ α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (StateT σ ProbComp)) (reset : σ → σ)
    (idem : ∀ s, reset (reset s) = reset s)
    (step : ∀ query s, Prod.map id reset <$> (impl query).run s = Prod.map id reset <$> (impl query).run (reset s))
    (work : OracleComp spec' α) (s : σ) :
    Prod.map id reset <$> (simulateQ impl work).run s = Prod.map id reset <$> (simulateQ impl work).run (reset s) := by
  induction work using OracleComp.inductionOn generalizing s with
  | pure value => simp [idem]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      have left : ((impl query).run s >>= fun r => Prod.map id reset <$> (simulateQ impl (next r.1)).run r.2) =
          (Prod.map id reset <$> (impl query).run s) >>= fun r =>
            Prod.map id reset <$> (simulateQ impl (next r.1)).run r.2 := by
        rw [bind_map_left]
        exact bind_congr fun r => ih r.1 r.2
      have right : ((impl query).run (reset s) >>= fun r => Prod.map id reset <$> (simulateQ impl (next r.1)).run r.2) =
          (Prod.map id reset <$> (impl query).run (reset s)) >>= fun r =>
            Prod.map id reset <$> (simulateQ impl (next r.1)).run r.2 := by
        rw [bind_map_left]
        exact bind_congr fun r => ih r.1 r.2
      rw [left, right, step]

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- `realRegAt` with the ghosts reset is the native handler on the deployment state. -/
theorem realRegAt_clean {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK Bk n) :
    Prod.map id unghost <$> (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x =
      (fun r => (r.1, unghost { x with base := r.2 })) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr query.val)).run x.base := by
  rw [← PqxdhDeploymentLaterServerGame.handler_erase setup codec checks route created.seed (.inr query.val) x.base x.log]
  simp only [realRegAt, StateT.run, Functor.map_map]
  rfl

/-- `realRegAt` does not read the ghosts. -/
theorem realRegAt_unghost {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (x : XState KemSK Bk n) :
    Prod.map id unghost <$> (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run x =
      Prod.map id unghost <$> (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run (unghost x) := by
  rw [realRegAt_clean, realRegAt_clean]
  rfl

/-- A base step does not read the ghosts. -/
theorem onBase_unghost {Bk : Type} {n : ℕ} {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (x : XState KemSK Bk n) :
    Prod.map id unghost <$> (PqxdhDeploymentBackend.onBase step).run x =
      Prod.map id unghost <$> (PqxdhDeploymentBackend.onBase step).run (unghost x) := by
  simp only [PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift, StateT.run, Functor.map_map]
  rfl

/-- A coins-only slot step inherits the ghost independence of its probabilistic step. -/
theorem onSlots_unghost {Γ : Type} {n : ℕ} {α : Type} (step : StateT (XState KemSK Γ n) ProbComp α)
    (independent : ∀ y, Prod.map id unghost <$> step.run y = Prod.map id unghost <$> step.run (unghost y))
    (y : XState KemSK Γ n) :
    Prod.map id unghost <$> (onSlots step).run y = Prod.map id unghost <$> (onSlots step).run (unghost y) := by
  change Prod.map id unghost <$> liftS (step.run y) = Prod.map id unghost <$> liftS (step.run (unghost y))
  rw [liftS, liftS, ← OracleComp.liftComp_map, ← OracleComp.liftComp_map, independent]

/-- A slot core whose slot program does not read the ghosts does not read them either. -/
theorem slotCore_unghost {Γ : Type} {n : ℕ} (prog : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery)
    (independent : ∀ y, Prod.map id unghost <$> (prog created query).run y =
      Prod.map id unghost <$> (prog created query).run (unghost y))
    (x : XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × Γ)) n) :
    Prod.map id unghost <$> (slotCore prog svc created query).run x =
      Prod.map id unghost <$> (slotCore prog svc created query).run (unghost x) := by
  have shift : ∀ (y : XState KemSK Γ n) (a : PqxdhRegistrationJointKemSecondEntry.Alloc Coord n) (v : S),
      unghost (attach y a v) = attach (unghost y) a v := fun _ _ _ => rfl
  have lift : ∀ (z : XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc Coord n × Γ)) n),
      Prod.map id unghost <$> (slotCore prog svc created query).run z =
        (fun r => (r.1.1, attach r.1.2 r.2.1 r.2.2)) <$>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl svc)
            (Prod.map id unghost <$> (prog created query).run (detach z))).run (z.backend.2.1, z.backend.1) := by
    intro z
    rw [PqxdhDeploymentIdealSlots.slotCore_run, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
    rfl
  rw [lift, lift, independent]
  rfl


variable {count : ℕ} (t : Target count) (p : Params KemSK count)
  (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- No command of the ideal registration reads the ghosts: they are only written (the accept's log entry, the finish snapshot). -/
theorem idealProg_unghost (query : PqxdhRecordLiftInterface.EnvQuery) (y : XState KemSK IdealCore 2) :
    Prod.map id unghost <$> (idealProg setup codec route checks t p hidden created query).run y =
      Prod.map id unghost <$> (idealProg setup codec route checks t p hidden created query).run (unghost y) := by
  rcases query with ⟨command, env⟩
  cases command with
  | create pin keyId =>
      exact onSlots_unghost _ (fun z => onBase_unghost _ z) y
  | bundle owner =>
      exact onSlots_unghost _ (fun z => realRegAt_unghost setup codec route checks created _ z) y
  | hmac key message =>
      exact onSlots_unghost _ (fun z => realRegAt_unghost setup codec route checks created _ z) y
  | accept raw =>
      change Prod.map id unghost <$> (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run y =
        Prod.map id unghost <$> (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
          (unghost y)
      by_cases selected : y.backend.accepts = t.accept
      · have selected' : (unghost y).backend.accepts = t.accept := selected
        change Prod.map id unghost <$> (if y.backend.accepts = t.accept then _ else _) =
          Prod.map id unghost <$> (if (unghost y).backend.accepts = t.accept then _ else _)
        rw [ite_eq_left selected, ite_eq_left selected', Functor.map_map, Functor.map_map]
        rfl
      · have selected' : ¬ (unghost y).backend.accepts = t.accept := selected
        rw [PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw y selected,
          PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw (unghost y) selected']
        exact onSlots_unghost (Γ := IdealCore) (n := 2)
          (realRegAt (Bk := IdealCore) (n := 2) setup codec route checks created ⟨.accept raw, trivial⟩)
          (fun z => realRegAt_unghost (Bk := IdealCore) (n := 2) setup codec route checks created ⟨.accept raw, trivial⟩ z)
          { y with backend := { y.backend with accepts := y.backend.accepts + 1 } }
  | build session payload =>
      change Prod.map id unghost <$>
          (PqxdhDeploymentIdealSteps.buildStep setup codec route checks hidden created session payload).run y =
        Prod.map id unghost <$>
          (PqxdhDeploymentIdealSteps.buildStep setup codec route checks hidden created session payload).run (unghost y)
      rcases marked : y.backend.marks with _ | ⟨index, coords⟩
      · rw [PqxdhDeploymentIdealSteps.buildStep_unmarked setup codec route checks hidden created session payload y marked,
          PqxdhDeploymentIdealSteps.buildStep_unmarked setup codec route checks hidden created session payload (unghost y)
            marked]
        exact onSlots_unghost (Γ := IdealCore) (n := 2)
          (realRegAt (Bk := IdealCore) (n := 2) setup codec route checks created ⟨.build session payload, trivial⟩)
          (fun z => realRegAt_unghost (Bk := IdealCore) (n := 2) setup codec route checks created
            ⟨.build session payload, trivial⟩ z) y
      · by_cases hit : index = session ∧ (y.base.native.shared.2.pending session).isSome
        · change Prod.map id unghost <$> (match y.backend.marks with
              | some (index, coords) => _
              | none => _) =
            Prod.map id unghost <$> (match (unghost y).backend.marks with
              | some (index, coords) => _
              | none => _)
          have marked' : (unghost y).backend.marks = some (index, coords) := marked
          have hit' : index = session ∧ ((unghost y).base.native.shared.2.pending session).isSome = true := hit
          rw [marked, marked']
          dsimp only
          rw [ite_eq_left hit, ite_eq_left hit']
          simp only [map_bind, map_pure]
          rfl
        · rw [PqxdhDeploymentIdealSteps.buildStep_other setup codec route checks hidden created session payload y index
              coords marked hit,
            PqxdhDeploymentIdealSteps.buildStep_other setup codec route checks hidden created session payload (unghost y)
              index coords marked hit]
          exact onSlots_unghost (Γ := IdealCore) (n := 2)
            (realRegAt (Bk := IdealCore) (n := 2) setup codec route checks created ⟨.build session payload, trivial⟩)
            (fun z => realRegAt_unghost (Bk := IdealCore) (n := 2) setup codec route checks created
              ⟨.build session payload, trivial⟩ z) y
  | finish owner raw =>
      change Prod.map id unghost <$>
          (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p hidden created owner raw).run y =
        Prod.map id unghost <$>
          (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p hidden created owner raw).run (unghost y)
      by_cases challenge : y.backend.active = true ∧ owner = t.kem.val ∧ PqxdhDeploymentIdealSteps.initSentAt
          y.base.native.owners owner = true
      · change Prod.map id unghost <$> (if y.backend.active = true ∧ owner = t.kem.val ∧
              PqxdhDeploymentIdealSteps.initSentAt y.base.native.owners owner = true then _ else _) =
          Prod.map id unghost <$> (if (unghost y).backend.active = true ∧ owner = t.kem.val ∧
              PqxdhDeploymentIdealSteps.initSentAt (unghost y).base.native.owners owner = true then _ else _)
        have challenge' : (unghost y).backend.active = true ∧ owner = t.kem.val ∧
            PqxdhDeploymentIdealSteps.initSentAt (unghost y).base.native.owners owner = true := challenge
        rw [ite_eq_left challenge, ite_eq_left challenge']
        simp only [map_bind, map_pure]
        rfl
      · rw [PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p hidden created owner raw y challenge,
          PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p hidden created owner raw (unghost y)
            challenge]
        exact onSlots_unghost (Γ := IdealCore) (n := 2)
          (realRegAt (Bk := IdealCore) (n := 2) setup codec route checks created ⟨.finish owner raw, trivial⟩)
          (fun z => realRegAt_unghost (Bk := IdealCore) (n := 2) setup codec route checks created
            ⟨.finish owner raw, trivial⟩ z) y
  | hash bytes => exact absurd env id
  | serverSend keyId plaintext => exact absurd env id
  | serverRaw raw => exact absurd env id
  | beaconSend owner plaintext => exact absurd env id
  | beaconRaw owner raw => exact absurd env id

/-- No request of the handler with the ideal registration reads the ghosts. -/
theorem idealStep_unghost (query : Spec.Domain) (x : XState KemSK (IdealBk TableState) 2) :
    Prod.map id unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x =
      Prod.map id unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run (unghost x) := by
  have core : ∀ env : PqxdhRecordLiftInterface.EnvQuery,
      Prod.map id unghost <$> (idealReg setup codec route checks t p created env).run x =
        Prod.map id unghost <$> (idealReg setup codec route checks t p created env).run (unghost x) := fun env =>
    slotCore_unghost _ PqxdhDeploymentSeedSplit.tableService created env
      (fun y => idealProg_unghost setup codec route checks t p _ created env y) x
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift]
    rfl
  · cases command with
    | create pin keyId => exact core ⟨.create pin keyId, trivial⟩
    | bundle owner => exact core ⟨.bundle owner, trivial⟩
    | accept raw => exact core ⟨.accept raw, trivial⟩
    | build session payload => exact core ⟨.build session payload, trivial⟩
    | finish owner raw => exact core ⟨.finish owner raw, trivial⟩
    | hmac key message => exact core ⟨.hmac key message, trivial⟩
    | hash bytes => exact onBase_unghost _ x
    | serverSend keyId plaintext => exact onBase_unghost _ x
    | serverRaw raw => exact onBase_unghost _ x
    | beaconSend owner plaintext => exact onBase_unghost _ x
    | beaconRaw owner raw => exact onBase_unghost _ x

/-- No run of the handler with the ideal registration reads the ghosts: with the ghosts reset on the outcome, the run from a state is the run from that state with its ghosts reset. -/
theorem idealRun_unghost {α : Type} (work : OracleComp Spec α) (x : XState KemSK (IdealBk TableState) 2) :
    Prod.map id unghost <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) work).run x =
      Prod.map id unghost <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) work).run
          (unghost x) :=
  run_reset _ unghost (fun _ => rfl) (fun query state => idealStep_unghost setup codec route checks t p created query state)
    work x

end Ghost


/-! ### The ideal game at the cut -/

section Cut
open PqxdhDeploymentBackend (XState RegImpl handlerWith xinitial)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPool (deploymentPool)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The canonical extended state at the cut for a deployment state: the ideal backend right before the selected accept (the accept counter at the selected ordinal, inactive, no mark, no install ghost, empty allocator and table), no seed and no LQ-F ghost. -/
def cutState (base : PqxdhDeploymentNative.State KemSK) : XState KemSK (IdealBk TableState) 2 :=
  ⟨base, withAccepts (idealInit created) t.accept, ∅, PqxdhDeploymentLater.Snap.empty, []⟩

/-- The ideal game after the cut, as a distribution of a decision that reads the result and the deployment state: from the canonical state at the cut, resume the cut (issue the suspended raw accept, if any, and run the rest) with the ideal registration. -/
noncomputable def resumeAt {Y : Type} (decision : Y × PqxdhDeploymentNative.State KemSK → Bool) (cut : CutCE Y)
    (base : PqxdhDeploymentNative.State KemSK) : ProbComp Bool :=
  (fun outcome => decision (outcome.1, outcome.2.base)) <$>
    (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) (finishCE cut)).run
      (cutState t created base)

/-- The ideal game cut at the selected accept (CE side of the prefix, route P-a): for every decision that reads only the result and the deployment state, the run of a deployment program by the handler with the ideal registration from its initial state is the run of the program's scan up to the selected accept by the native deployment handler with the pool create, followed by the ideal game resumed from the canonical state at the cut (`resumeAt`). The ghosts written before the cut (the LQ-F log and snapshot) do not matter (`idealRun_unghost`), and the backend at a suspended accept is the canonical one (`preScan`). -/
theorem ideal_cut {Y : Type} (decision : Y × PqxdhDeploymentNative.State KemSK → Bool) (work : OracleComp Spec Y) :
    (fun outcome => decision (outcome.1, outcome.2.base)) <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) work).run
          (xinitial created (idealInit created)) =
      (simulateQ (deploymentPool setup codec checks route created.seed (p.pool t)) (scanCE work t.accept)).run
          (PqxdhDeploymentNative.initial created) >>= fun reached =>
        resumeAt setup codec route checks t p created decision reached.1 reached.2 := by
  have pre : PreCut (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)) := ⟨rfl, rfl⟩
  have scanned := preScan setup codec route checks t p created work t.accept _ pre (by simp [xinitial, idealInit,
    PqxdhDeploymentIdealSteps.IdealCore.initial])
  rw [run_scanCE _ work t.accept, map_bind]
  rw [show PqxdhDeploymentNative.initial created =
    (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)).base from rfl, ← scanned.1, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun reached member => ?_
  obtain ⟨accepts, backend, seeds, pending⟩ := scanned.2 reached member
  have reads : ∀ (state : XState KemSK (IdealBk TableState) 2),
      (fun outcome : Y × XState KemSK (IdealBk TableState) 2 => decision (outcome.1, outcome.2.base)) <$>
          (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
            (finishCE reached.1)).run state =
        (fun outcome => decision (outcome.1, outcome.2.base)) <$>
          (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
            (finishCE reached.1)).run (unghost state) := by
    intro state
    have ghost := congrArg (fun work => (fun outcome : Y × XState KemSK (IdealBk TableState) 2 =>
      decision (outcome.1, outcome.2.base)) <$> work)
      (idealRun_unghost setup codec route checks t p created (finishCE reached.1) state)
    rw [Functor.map_map, Functor.map_map] at ghost
    exact ghost
  change _ = resumeAt setup codec route checks t p created decision reached.1 reached.2.base
  rw [reads]
  unfold resumeAt
  rcases cut : reached.1 with result | ⟨raw, next⟩
  · simp only [finishCE, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · have counted := pending raw next cut
    have same : unghost reached.2 = cutState t created reached.2.base := by
      have : reached.2 = ⟨reached.2.base, reached.2.backend, reached.2.seeds, reached.2.snap, reached.2.log⟩ := rfl
      rw [this]
      simp only [unghost, cutState, backend, seeds, counted]
      simp [xinitial, idealInit, PqxdhDeploymentIdealSteps.IdealCore.initial]
    rw [same]


/-- The initial annotated source state of a constructed Server, with the private pools after its construction. -/
def sourceInit (pool : PqxdhRegistrationJointPreparation.Pool KemSK) : PqxdhRegistrationJointSchedule.State KemSK :=
  PqxdhRegistrationJointSchedule.initial pool (PqxdhRegistrationSchedule.initial created).shared

/-- The pool scan on the deployment side is an image of the annotated pool source execution of the compiled scan (CE-3's compile lemma at the pool, `PqxdhDeploymentIdealPool.compile_native_pool`, then the erasure `PqxdhDeploymentIdealPoolSource.programPool_native`), under the approved codec contracts and for a Server constructed with the experiment's key ID and no peer. -/
theorem pool_scan_source {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (identityIndex : ℕ)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (work : OracleComp Spec Y) (index : ℕ) :
    (simulateQ (deploymentPool setup codec checks route created.seed (p.pool t)) (scanCE work index)).run
        (PqxdhDeploymentNative.initial created) =
      (fun result => (result.1.1, merge result.1.2 (PqxdhRegistrationJointSchedule.source result.2))) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed identityIndex (p.pool t))
          (PqxdhDeploymentCompile.compile setup codec route (scanCE work index))).run (sourceInit created pool) := by
  rw [show PqxdhDeploymentNative.initial created =
      (⟨PqxdhRegistrationSchedule.initial created, 0, fun _ => 0, []⟩ : PqxdhDeploymentNative.State KemSK) from rfl,
    ← PqxdhDeploymentIdealPool.compile_native_pool setup codec checks route created.seed (p.pool t) phase1 phase2
      (scanCE work index) (PqxdhRegistrationSchedule.initial created) sender peers rfl (fun _ => rfl),
    show PqxdhRegistrationSchedule.initial created =
      PqxdhRegistrationJointSchedule.source (sourceInit created pool) from rfl,
    ← PqxdhDeploymentIdealPoolSource.programPool_native, Functor.map_map]

/-- The prefix of item 2's opaque scan at the pool (its source commands up to the selected raw accept, compiled to the open private-service interface and run by the stopped selected-first router at the pool) is an image of the same annotated pool source execution of the compiled CE scan: the router's reply is the compiled cut (`compileCut`) with the encoded owners and the native state, and the router's state is the joint identity state with the router state of the KEM pool (`compile_scan`, `PqxdhDeploymentIdealPoolSource.kemCommands_stopped`). The premises are a source budget for item 2's scan of the compiled program that reads no identity or KEM field and creates no more KEM keys than the pool holds, the Server's identity slot in the joint pool, and an empty KEM pool. -/
theorem stopped_scan_source {Y : Type} (selected : ℕ) (identityIndex : ℕ)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[identityIndex]? = some created.seed) (work : OracleComp Spec Y) (index : ℕ)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (scan (PqxdhDeploymentCompile.compile setup codec route work) index).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected (p.pool t))
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex
            (setup.joint.publicKeys created.seed) (scan (PqxdhDeploymentCompile.compile setup codec route work) index) []
            (PqxdhRegistrationSchedule.initial created).shared))).run).run (pool.1, PqxdhDynamicKemRouter.empty) =
      (fun result => (some (((compileCut setup codec route result.1,
          (PqxdhRegistrationJointGeneratedFinish.encodeState setup result.2).owners), result.2.shared)),
          (result.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.pool.2))) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed identityIndex (p.pool t))
          (PqxdhDeploymentCompile.compile setup codec route (scanCE work index))).run (sourceInit created pool) := by
  have owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed identityIndex (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  have prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) (sourceInit created pool).pool.2 := by
    simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty,
      PqxdhDeploymentIdealPoolSource.PoolPrefix]
  have routerEmpty :
      PqxdhDynamicKemRouter.empty = PqxdhDeploymentIdealPoolSource.routerOf (sourceInit created pool).pool.2 := by
    simp only [sourceInit, PqxdhRegistrationJointSchedule.initial, empty]
    rfl
  rw [PqxdhRegistrationJointKemEncapsulation.commands_actual, routerEmpty]
  have stopped := PqxdhDeploymentIdealPoolSource.kemCommands_stopped setup codec checks selected created.seed
    identityIndex (p.pool t) _ budget certified unreadIdentity unreadKem (sourceInit created pool) owned prefixed
    (by simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using room)
  refine stopped.trans ?_
  rw [show PqxdhDeploymentCompile.compile setup codec route work =
      (simulateQ (compileImpl setup codec route) work).run PqxdhDeploymentCompile.Local.empty from rfl,
    compile_scan, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The common prefix of the CE side and item 2's side at the pool (route P-a): the annotated pool source execution of the compiled CE scan up to the selected raw accept, from the constructed Server's initial annotated source state with the private pools after its construction. -/
noncomputable def commonPrefix {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (work : OracleComp Spec Y) :
    ProbComp ((CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK) :=
  (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
      created.server.server.metadata.identityIndex (p.pool t))
    (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept))).run (sourceInit created pool)

end Cut

section Prefix
open PqxdhDeploymentBackend (XState RegImpl handlerWith xinitial gameWith)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count) {A : Type}

/-- The prefix of `CE.idealGame g` at the challenger's draws (U5, CE side): for every decision that reads the constructed Server's public data, the adversary's output, the ledger and the deployment state, the common deployment experiment with the ideal registration at the draws is the Server construction (as item 2's annotated birth, which also installs the Server's seed in the joint identity pool), then the common prefix (`commonPrefix`), then the ideal game resumed from the canonical state at the cut on the merged deployment state. Premises: the approved codec contracts. -/
theorem ideal_prefix (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) ×
      PqxdhDeploymentNative.State KemSK) → Bool) :
    (fun outcome => decision (outcome.1.map fun result => (result.1, (result.2.1, result.2.2.1), result.2.2.2.base))) <$>
        (gameWith setup codec route idealInit (idealReg setup codec route checks t p) ensureInit 0 bounds mode
          adversary).run runtime =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => pure (decision none)
        | some created =>
            commonPrefix setup codec route checks t p created born.2.1
                (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
              >>= fun reached =>
              resumeAt setup codec route checks t p created
                (fun outcome => decision (some (PqxdhRegistrationJointServerBirth.encode created, outcome.1, outcome.2)))
                reached.1.1 (merge reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)) := by
  simp only [gameWith, PqxdhRegistrationJointServerBirth.source, StateT.run, map_bind, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun born member => ?_
  rcases born with ⟨_ | created, after⟩
  · simp
  · obtain ⟨sender, peers⟩ := PqxdhDeploymentCompileGame.construct_fields setup.joint ensureInit 0 setup.serverKeyId
      runtime created after member
    dsimp only
    have cut := ideal_cut setup codec route checks t p created
      (fun outcome => decision (some (PqxdhRegistrationJointServerBirth.encode created, outcome.1, outcome.2)))
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))
    rw [pool_scan_source setup codec route checks t p created phase1 phase2 sender peers
      created.server.server.metadata.identityIndex
      (PqxdhRegistrationJointServerBirth.install created (PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty)),
      bind_map_left] at cut
    rw [Functor.map_map]
    exact cut


/-- The rest of item 2's opaque scan after its source prefix (`PqxdhRegistrationJointKemRawOpaque.opaqueScan` after the scanned source commands): a completed prefix completes; at the selected raw accept, a rejected attached verification or a rejection before encapsulation completes the run, and otherwise the source parameters of the active cut are saved. -/
noncomputable def opaqueRest {Z R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : Z × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (reached : PqxdhRegistrationJointKemCommands.Outcome KemSK (Cut KemSK Z)) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (PqxdhRegistrationJointKemRawOpaque.OpaqueCut Reader KemSK Z R) :=
  match reached.1.1 with
  | .complete result => pure (.complete ((observe (result, none), reached.1.2), reached.2))
  | .pending raw next =>
    match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
    | none =>
      PqxdhRegistrationJointKemRawOpaque.rejectRun setup codec checks identityIndex publicIdentity observe raw next
        reached.1.2 reached.2 (none, reached.2.2.server.consumed)
    | some value => do
      let prepared ← simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
          (PqxdhRegistrationJointKemCollected.beforeEncapsulation value)).run reached.2.2.server.consumed)
      match prepared.1 with
      | none =>
        PqxdhRegistrationJointKemRawOpaque.rejectRun setup codec checks identityIndex publicIdentity observe raw next
          reached.1.2 reached.2 (none, prepared.2)
      | some ephemeral => pure (.pending raw value ephemeral prepared.2 reached.2 reached.1.2 next)

/-- Item 2's opaque scan is its source prefix followed by `opaqueRest`. -/
theorem opaqueScan_split {Z R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : Z × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Z) (index : ℕ)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhRegistrationJointKemRawOpaque.opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity
        observe work index owners state =
      simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex publicIdentity
            (scan work index) owners state) >>=
        opaqueRest setup codec checks identityIndex publicIdentity observe := rfl

/-- The prefix of item 2's ideal world at the challenger's draws (U5, item 2's side): item 2's prephase at the drawn family (`PqxdhDeploymentIdealParams.preOpaquePool`) for the compiled program of a deployment program, at the target's raw-accept ordinal and KEM index, is the same Server construction as `ideal_prefix`, then the same common prefix (`commonPrefix`), then the rest of item 2's opaque scan (`opaqueRest`) under the stopped selected-first router at the pool, started from the compiled cut with the encoded owners and the native state and from the joint identity state with the router state of the KEM pool. Premises: a source budget for item 2's scan of the compiled program that reads no identity or KEM field and creates no more KEM keys than the pool holds. -/
theorem item2_prefix {Y : Type} (ensureInit : StateT A ProbComp Bool) (decision : Y × Local → Bool)
    (work : OracleComp Spec Y) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (scan (PqxdhDeploymentCompile.compile setup codec route work) t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    PqxdhDeploymentIdealParams.preOpaquePool (Reader := Reader) setup codec checks ensureInit none decision
        (PqxdhDeploymentCompile.compile setup codec route work) runtime count t.kem t.accept p.chosen p.others =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        (match born.1 with
        | none => pure (.failed born.2)
        | some created =>
            (commonPrefix setup codec route checks t p created born.2.1 work >>= fun reached =>
              ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
                (opaqueRest setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
                  (PqxdhRegistrationJointAcceptCutTag.decideTag decision)
                  ((compileCut setup codec route reached.1,
                    (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners), reached.2.shared))).run).run
                  (reached.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.pool.2)) >>= fun result =>
              pure (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others result.1 result.2 born.2.2)) := by
  unfold PqxdhDeploymentIdealParams.preOpaquePool
  rw [PqxdhRegistrationJointServerBirth.client_source, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun born member => ?_
  rcases born with ⟨_ | created, after⟩
  · rfl
  · dsimp only [Option.map_some]
    have publicSame := PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId none
      _ after created member
    have slot := PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId none _ after
      created member
    have installed := (PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId
      none _ after created member).1
    have empty : after.1.2 = PqxdhLiveKemBirth.empty := by rw [installed]; rfl
    refine congrArg (fun work => work >>= _) ?_
    change ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
      (PqxdhRegistrationJointKemRawOpaque.opaqueScan (Reader := Reader) setup codec checks
        created.server.server.metadata.identityIndex created.publicIdentity
        (PqxdhRegistrationJointAcceptCutTag.decideTag decision) (PqxdhDeploymentCompile.compile setup codec route work)
        t.accept [] (PqxdhRegistrationSchedule.initial created).shared)).run).run
          (after.1.1, PqxdhDynamicKemRouter.empty) = _
    rw [opaqueScan_split, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, publicSame,
      stopped_scan_source setup codec route checks t p created t.kem.val created.server.server.metadata.identityIndex
        after.1 empty slot work t.accept budget certified unreadIdentity unreadKem room, bind_map_left, ← publicSame]
    rfl

end Prefix

/-! ### Facts at the cut -/

section Facts
open PqxdhDeploymentIdealParams (Target Params)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- On every outcome of the common prefix, the annotated source state keeps the source-side invariant at the pool (CE-3's source ownership facts, the Server's identity slot, one KEM key pair per owner). -/
theorem cut_owned {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup codec route checks t p created pool work)) :
    PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex reached.2 := by
  have start : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex
      (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  exact (PqxdhServerAuthExperiment.run_rel (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
      created.server.server.metadata.identityIndex (p.pool t))
    (fun before after => PqxdhDeploymentIdealPoolSource.PoolOwned created.seed
      created.server.server.metadata.identityIndex before → PqxdhDeploymentIdealPoolSource.PoolOwned created.seed
        created.server.server.metadata.identityIndex after)
    (fun _ owned => owned) (fun _ _ _ left right owned => right (left owned))
    (fun query before after supported owned => PqxdhDeploymentIdealPoolSource.query_poolOwned setup codec checks
      created.seed created.server.server.metadata.identityIndex (p.pool t) query before after owned supported)
    _ _ reached member) start

/-- On every outcome of the common prefix, the compiled program's local copies and the erased source state satisfy CE-3's merge invariant (`PqxdhDeploymentCompileInvariant.Good`), under the approved codec contracts and for a Server constructed with the experiment's key ID and no peer. -/
theorem cut_good {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (work : OracleComp Spec Y) (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup codec route checks t p created pool work)) :
    PqxdhDeploymentCompileInvariant.Good setup codec reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2) := by
  have image := PqxdhDeploymentIdealPoolSource.programPool_native setup codec checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)
    (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept)) (sourceInit created pool)
  have erased : (reached.1, PqxdhRegistrationJointSchedule.source reached.2) ∈ support
      ((simulateQ (PqxdhDeploymentIdealPool.revealPool setup codec checks created.seed (p.pool t))
        ((simulateQ (compileImpl setup codec route) (scanCE work t.accept)).run Local.empty)).run
          (PqxdhRegistrationSchedule.initial created)) := by
    change _ ∈ support ((simulateQ (PqxdhDeploymentIdealPool.revealPool setup codec checks created.seed (p.pool t))
      (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept))).run
        (PqxdhRegistrationJointSchedule.source (sourceInit created pool)))
    rw [← image, support_map]
    exact ⟨reached, member, rfl⟩
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at erased
  obtain ⟨final, finalMember, same⟩ := erased
  have copies : final.2.1 = reached.1.2 := congrArg (fun value => value.1.2) same
  have native : final.2.2 = PqxdhRegistrationJointSchedule.source reached.2 := congrArg (fun value => value.2) same
  rw [← copies, ← native]
  exact (PqxdhServerAuthExperiment.run_rel (PqxdhDeploymentIdealPool.compiledPool setup codec checks route created.seed
      (p.pool t))
    (fun before after => PqxdhDeploymentCompileInvariant.Good setup codec before.1 before.2 →
      PqxdhDeploymentCompileInvariant.Good setup codec after.1 after.2)
    (fun _ good => good) (fun _ _ _ left right good => right (left good))
    (fun query before after supported good => PqxdhDeploymentIdealPool.good_step_pool setup codec checks route
      created.seed (p.pool t) phase1 phase2 query before.1 before.2 good after supported)
    _ _ final finalMember)
    (PqxdhDeploymentCompileInvariant.good_initial setup codec (PqxdhRegistrationSchedule.initial created) sender peers
      rfl (fun _ => rfl))

/-- On every outcome of the common prefix, the KEM pool holds the first entries of the challenger's pool, at most as many as the source budget's creations (owner `j` holds pool entry `j`), when the budget of item 2's scan of the compiled program creates no more KEM keys than the pool holds. -/
theorem cut_prefix {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (scan (PqxdhDeploymentCompile.compile setup codec route work) t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (room : budget (.inl 1) ≤ (p.pool t).length)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup codec route checks t p created pool work)) :
    PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) reached.2.pool.2 ∧
      reached.2.pool.2.keys.length ≤ budget (.inl 1) := by
  have owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex
      (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  have certified' : ∀ source, (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept)).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source) := by
    intro source
    have bound := certified source
    rw [show PqxdhDeploymentCompile.compile setup codec route work =
        (simulateQ (compileImpl setup codec route) work).run Local.empty from rfl, compile_scan,
      isQueryBoundP_map_iff] at bound
    exact bound
  have creations := PqxdhRegistrationJointKemCommands.creations setup codec checks
    created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed)
    (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept)) budget certified'
    (PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).owners
    (sourceInit created pool).shared
  have image := PqxdhDeploymentIdealPoolSource.kemCommands_reserved setup codec checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)
    (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept)) (sourceInit created pool) owned
  have mapped : (((reached.1, (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners),
      reached.2.shared), reached.2.pool) ∈ support ((simulateQ (PqxdhDeploymentIdealPoolSource.reservedAt setup (p.pool t))
        (PqxdhRegistrationJointKemCommands.program setup codec checks created.server.server.metadata.identityIndex
          (setup.joint.publicKeys created.seed) (PqxdhDeploymentCompile.compile setup codec route (scanCE work t.accept))
          (PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).owners
          (sourceInit created pool).shared)).run (sourceInit created pool).pool) := by
    rw [image, support_map]
    exact ⟨reached, member, rfl⟩
  have prefixed := PqxdhDeploymentIdealPoolSource.reserved_program_prefix setup (p.pool t) _ _ creations
    (sourceInit created pool).pool.1 (sourceInit created pool).pool.2
    (by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty,
      PqxdhDeploymentIdealPoolSource.PoolPrefix])
    (by simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using room) _ mapped
  refine ⟨prefixed.1, ?_⟩
  simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using prefixed.2


/-- The relation at the cut, on an outcome of the common prefix (`commonPrefix`), from which the CE side resumes with `resumeAt` on the merged deployment state (`ideal_prefix`) and item 2's side resumes with `opaqueRest` from the compiled cut, the encoded owners, the native state, the joint identity state and the router state of the KEM pool (`item2_prefix`): the annotated source state keeps the source-side invariant at the pool, the local copies and the erased source state satisfy CE-3's merge invariant, and the KEM pool holds the first entries of the challenger's pool, at most as many as the budget's creations. -/
structure CutRel {Y : Type} (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK) : Prop where
  owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex reached.2
  good : PqxdhDeploymentCompileInvariant.Good setup codec reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)
  prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) reached.2.pool.2
  bounded : reached.2.pool.2.keys.length ≤ budget (.inl 1)

/-- Every outcome of the common prefix satisfies the relation at the cut, under the approved codec contracts, for a Server constructed with the experiment's key ID and no peer whose seed sits at its identity slot of the joint pool, with an empty KEM pool, and for a budget of item 2's scan of the compiled program that creates no more KEM keys than the pool holds. -/
theorem cut_rel {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (scan (PqxdhDeploymentCompile.compile setup codec route work) t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (room : budget (.inl 1) ≤ (p.pool t).length)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup codec route checks t p created pool work)) :
    CutRel setup codec t p created budget reached :=
  ⟨cut_owned setup codec route checks t p created pool empty slot work reached member,
    cut_good setup codec route checks t p created phase1 phase2 sender peers pool work reached member,
    (cut_prefix setup codec route checks t p created pool empty slot work budget certified room reached member).1,
    (cut_prefix setup codec route checks t p created pool empty slot work budget certified room reached member).2⟩

end Facts

end BeaconcryptCore.Computational.PqxdhDeploymentIdealCut

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_finish' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.run_scanCE' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.run_scanCE

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_pure' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_accept_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_accept_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_accept_succ' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_accept_succ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_other' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scanCE_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scan_query_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scan_query_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scan_bind_noAccept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.scan_bind_noAccept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.compile_noAccept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.compile_noAccept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.compile_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.compile_scan

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.slotImpl_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.slotImpl_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.slotCore_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.slotCore_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.onBase_base' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.onBase_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealReg_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealReg_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealReg_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealReg_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.preStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.preStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.preScan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.preScan

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.run_reset' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.run_reset

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_clean

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_unghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.realRegAt_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.onBase_unghost' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.onBase_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.onSlots_unghost' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.onSlots_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.slotCore_unghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.slotCore_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealProg_unghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealProg_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealStep_unghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealStep_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealRun_unghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.idealRun_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.ideal_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.ideal_cut

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.pool_scan_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.pool_scan_source

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.stopped_scan_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.stopped_scan_source

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.ideal_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.ideal_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.opaqueScan_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.opaqueScan_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.item2_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.item2_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_owned

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_good

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealCut.cut_rel
