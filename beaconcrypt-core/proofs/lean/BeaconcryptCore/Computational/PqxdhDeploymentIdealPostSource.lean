-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSim

/-!
# The middle execution of the post-challenge simulation and its CE layer (CE-11b, unit U6, second part)

The active branch of the second compile lemma (`PqxdhDeploymentIdealActive.ActiveBranch`) compares two executions of the same deployment program after the selected accept: the CE side runs it by the handler with the ideal registration on the merged deployment state, item 2 runs its compiled program (CE-3's `compileImpl`, the same on both sides) through its post-challenge stack. Neither state determines the other: the CE state merges the compiled program's local copies into the native state and keeps the analysis observers, while item 2 keeps the source's stale kernels of copied peers and owners and erases the observers. The simulation therefore goes through a middle execution of the compiled program, of which both sides are images. This module defines it and proves the CE side.

- The middle state (`Mid`) is item 2's annotated source state (pools with their histories and the indexed owners; `PqxdhRegistrationJointSchedule.State`), the backend of the ideal registration (accept counter, activity, mark, ghosts, allocator and table) and the seed table. The middle source handler (`sourceMid`) answers the selected raw accept, the build of the marked session with a pending token and owner k's challenge finish after an active selected accept by the ideal registration's step on the middle state without copies (`toX`, rejoined with `fromX` and `rejoin`; `idealMid`), and every other source request by item 2's annotated pool source (`PqxdhDeploymentIdealPoolSource.sourcePool`) with the accept counter advanced on a raw accept (`realMid`).
- The CE view of a middle state with the compiled program's local copies (`mergeX`) is CE-3's merge of the copies into the native state of the annotated source, with no ghosts.
- Real commands (`RealAt`, `step_real`): after the cut the real steps of the ideal registration project to the native deployment handler with the pool create (`postStep`, `postStep_unghost`), every other command's compiled program issues no source request of a hidden kind (`compile_noHidden`) or is a single forwarded real request (`sourceMid_single`), and the step follows from CE-3's pool step `PqxdhDeploymentIdealPool.step_merge_pool` and the erasure `PqxdhDeploymentIdealPoolSource.programPool_native`.
- Hidden commands: the hidden steps never read a copied kernel. On the shared native state (`ShComm`, with closure lemmas) the selected accept (`acceptExposed_comm`, from the native accept tail `shComm_tail`, the LQ-F logged accept `shComm_acceptLogged` and item 2's marker tail under `tailCE`, `tailCE_tail_comm`) and the steps after encapsulation (`acceptAfter_comm`) commute with CE-3's Server override; owner k's challenge finish commutes with merging when owner k has no local copy (`finishChallenge_merge`, through `groupCE_comm`); the marked build commutes when every copied peer is installed (`buildHidden_comm`, through the factored Server build `factored_override`, which follows from the generic builder's commutation with any map of the present peers that leaves unoccupied key IDs alone, `genericBuild_mapPeers`). Lifted to the slot programs (`acceptStep_selected_merge`, `buildStep_hidden_merge`, `finishStep_challenge_merge`, `selectedStep_merge`) and through the slot core (`idealReg_merge`), these give `step_accept_selected`, `step_build_hidden` and `step_finish_hidden`.
- `step_mergeMid`: under CE-3's merge invariant every deployment command commutes with merging. `compile_simulationMid`: for every invariant that implies CE-3's merge invariant and is kept by every compiled step under the middle source handler, merging the final local copies into the final middle state of the compiled program's middle execution gives the run of the deployment program by the handler with the ideal registration from the merged state, without ghosts (the ghosts are erased by item 2's `run_erase` with `PqxdhDeploymentIdealCut.idealStep_unghost`), jointly with the program's output. The invariant's preservation and item 2's side of the simulation are later parts of unit U6.

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState idealReg)
open PqxdhDeploymentIdealParams (Target Params)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The middle state -/

/-- The state of the middle execution of the post-challenge simulation: item 2's annotated source state (pools with their histories and the indexed owners), the backend of the ideal registration and the seed table. -/
structure Mid (KemSK : Type) where
  joint : PqxdhRegistrationJointSchedule.State KemSK
  backend : IdealBk TableState
  seeds : (PqxdhRecordLiftWorld.SeedSpec 2).QueryCache

/-- The extended deployment state of a middle state with no local copies: the native state of the annotated source with zero raw-attempt counters and no produced frame, the backend, the seed table, the empty snapshot and the empty log. -/
def toX (m : Mid KemSK) : XState KemSK (IdealBk TableState) 2 :=
  ⟨⟨PqxdhRegistrationJointSchedule.source m.joint, 0, fun _ => 0, []⟩, m.backend, m.seeds,
    PqxdhDeploymentLater.Snap.empty, []⟩

/-- The extended deployment state of a middle state with local copies: CE-3's merge of the copies into the native state of the annotated source, the backend, the seed table, the empty snapshot and the empty log. -/
def mergeX (copies : Local) (m : Mid KemSK) : XState KemSK (IdealBk TableState) 2 :=
  ⟨merge copies (PqxdhRegistrationJointSchedule.source m.joint), m.backend, m.seeds,
    PqxdhDeploymentLater.Snap.empty, []⟩

/-- An annotated source state with the shared native state and the owners of a native registration state, keeping the pools and the indices of every owner at a position the old state has. -/
def rejoin (old : PqxdhRegistrationJointSchedule.State KemSK) (new : PqxdhRegistrationSchedule.State KemSK) :
    PqxdhRegistrationJointSchedule.State KemSK :=
  ⟨old.pool, new.shared, new.owners.mapIdx fun position owner => match old.owners[position]? with
    | some entry => { entry with owner := owner }
    | none => ⟨0, 0, owner⟩⟩

/-- Erasing the annotations of a rejoined state gives the native registration state back. -/
theorem source_rejoin (old : PqxdhRegistrationJointSchedule.State KemSK) (new : PqxdhRegistrationSchedule.State KemSK) :
    PqxdhRegistrationJointSchedule.source (rejoin old new) = new := by
  have owners : (new.owners.mapIdx fun position owner => match old.owners[position]? with
      | some entry => ({ entry with owner := owner } : PqxdhRegistrationJointOwnership.Entry KemSK)
      | none => ⟨0, 0, owner⟩).map PqxdhRegistrationJointOwnership.Entry.owner = new.owners := by
    apply List.ext_getElem?
    intro index
    rw [List.getElem?_map, List.getElem?_mapIdx]
    rcases new.owners[index]? with _ | owner
    · rfl
    · simp only [Option.map_some]
      rcases old.owners[index]? <;> rfl
  simp only [PqxdhRegistrationJointSchedule.source, rejoin, owners]

/-- The middle state after a step of the ideal registration on `toX m`. -/
def fromX (m : Mid KemSK) (y : XState KemSK (IdealBk TableState) 2) : Mid KemSK :=
  ⟨rejoin m.joint y.base.native, y.backend, y.seeds⟩

/-- The backend after a real source request: a raw accept advances the accept counter. -/
def bumpSource : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain → IdealBk TableState → IdealBk TableState
  | .inl (.inr (.accept _)), backend => (backend.1, (backend.2.1, { backend.2.2 with accepts := backend.2.2.accepts + 1 }))
  | _, backend => backend

/-- Whether a build addresses the marked session while it has a pending token. -/
def buildHiddenAt (m : Mid KemSK) (session : ℕ) : Bool :=
  match m.backend.2.2.marks with
  | some (index, _) => decide (index = session ∧ (m.joint.shared.2.pending session).isSome = true)
  | none => false

/-- Whether a finish is owner k's challenge finish: the selected accept was active, the finish addresses the selected owner, and that owner is in the `initSent` phase. -/
def finishHiddenAt {count : ℕ} (t : Target count) (m : Mid KemSK) (owner : ℕ) : Bool :=
  decide (m.backend.2.2.active = true ∧ owner = t.kem.val ∧
    PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners owner = true)

section Handler
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A real source request on the middle state: item 2's annotated pool source (`PqxdhDeploymentIdealPoolSource.sourcePool`) on the annotated source state, with the accept counter advanced on a raw accept. -/
noncomputable def realMid (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) :
    StateT (Mid KemSK) ProbComp ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query) := fun m =>
  (fun r => (r.1, { m with joint := r.2, backend := bumpSource query m.backend })) <$>
    (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed created.server.server.metadata.identityIndex
      (p.pool t) query).run m.joint

/-- A hidden request on the middle state: the ideal registration's step on `toX m`, rejoined. -/
noncomputable def idealMid (query : PqxdhRecordLiftInterface.EnvQuery) :
    StateT (Mid KemSK) ProbComp (PqxdhRecordLiftInterface.EnvSpec.Range query) := fun m =>
  (fun r => (r.1, fromX m r.2)) <$> (idealReg setup codec route checks t p created query).run (toX m)

/-- The middle source handler: the selected raw accept, the marked build and owner k's challenge finish are the ideal registration's hidden steps; every other request is real. -/
noncomputable def sourceMid :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (Mid KemSK) ProbComp)
  | .inl (.inr (.accept raw)) => fun m =>
      if m.backend.2.2.accepts = t.accept then (idealMid setup codec route checks t p created ⟨.accept raw, trivial⟩).run m
      else (realMid setup codec checks t p created (.inl (.inr (.accept raw)))).run m
  | .inl (.inr (.build session payload)) => fun m =>
      if buildHiddenAt m session then (idealMid setup codec route checks t p created ⟨.build session payload, trivial⟩).run m
      else (realMid setup codec checks t p created (.inl (.inr (.build session payload)))).run m
  | .inl (.inr (.finish owner raw)) => fun m =>
      if finishHiddenAt t m owner then (idealMid setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run m
      else (realMid setup codec checks t p created (.inl (.inr (.finish owner raw)))).run m
  | query => realMid setup codec checks t p created query

/-- The compiled handler over the middle source handler, on the local copies and the middle state. -/
noncomputable def compiledMid :
    QueryImpl PqxdhDeploymentInterface.Spec (StateT (Local × Mid KemSK) ProbComp) :=
  ((sourceMid setup codec route checks t p created).mapStateTBase (compileImpl setup codec route)).flattenStateT

end Handler

/-! ### The real steps of the ideal registration after the cut -/

section Real
open PqxdhDeploymentIdealSlots (detach)
open PqxdhDeploymentIdealPool (deploymentPool)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A deployment command is real at an extended state: it is not the raw accept at the selected ordinal, not a build of the marked session while that session has a pending token, and not owner k's challenge finish after an active selected accept. -/
def RealAt (query : PqxdhDeploymentInterface.Spec.Domain) (x : XState KemSK (IdealBk TableState) 2) : Prop :=
  match query with
  | .inr (.accept _) => x.backend.2.2.accepts ≠ t.accept
  | .inr (.build session _) => ∀ index coords, x.backend.2.2.marks = some (index, coords) →
      ¬ (index = session ∧ (x.base.native.shared.2.pending session).isSome)
  | .inr (.finish owner _) => ¬ (x.backend.2.2.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt x.base.native.owners owner = true)
  | _ => True

/-- A real command of the handler with the ideal registration projects to the native deployment handler with the pool create (`PqxdhDeploymentIdealCut.preStep` after the cut): the backend advances the accept counter on a raw accept and is kept otherwise, and the seed table is kept. -/
theorem postStep (query : PqxdhDeploymentInterface.Spec.Domain) (x : XState KemSK (IdealBk TableState) 2)
    (real : RealAt t query x) :
    Prod.map id XState.base <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x =
      (deploymentPool setup codec checks route created.seed (p.pool t) query).run x.base ∧
      ∀ result ∈ support ((handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x),
        result.2.backend = PqxdhDeploymentIdealCut.bump query x.backend ∧ result.2.seeds = x.seeds := by
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
        have base := PqxdhDeploymentIdealCut.onBase_base (Bk := IdealCore) (n := 2)
          (match PqxdhDeploymentInterface.parsePin pin with
          | none => pure none
          | some word => some <$> PqxdhDeploymentNative.onNative
              (PqxdhDeploymentIdealSteps.createPool setup (p.pool t) word keyId)) (detach x)
        exact PqxdhDeploymentIdealCut.idealReg_lift setup codec route checks t p created ⟨.create pin keyId, trivial⟩ x
          (detach x) (PqxdhDeploymentIdealSteps.createReg setup (p.pool t) pin keyId) _ rfl rfl base.1 base.2
    | bundle owner =>
        exact PqxdhDeploymentIdealCut.idealReg_real setup codec route checks t p created ⟨.bundle owner, trivial⟩ x
          (detach x) rfl rfl rfl
    | accept raw =>
        exact PqxdhDeploymentIdealCut.idealReg_real setup codec route checks t p created ⟨.accept raw, trivial⟩ x
          { detach x with backend := { (detach x).backend with accepts := (detach x).backend.accepts + 1 } }
          (PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw (detach x) real) rfl rfl
    | build session payload =>
        exact PqxdhDeploymentIdealCut.idealReg_real setup codec route checks t p created ⟨.build session payload, trivial⟩ x
          (detach x) (PqxdhDeploymentIdealSteps.buildStep_real setup codec route checks _ created session payload
            (detach x) real) rfl rfl
    | finish owner raw =>
        exact PqxdhDeploymentIdealCut.idealReg_real setup codec route checks t p created ⟨.finish owner raw, trivial⟩ x
          (detach x) (PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p _ created owner raw (detach x)
            real) rfl rfl
    | hmac key message =>
        exact PqxdhDeploymentIdealCut.idealReg_real setup codec route checks t p created ⟨.hmac key message, trivial⟩ x
          (detach x) rfl rfl rfl
    | hash bytes => exact PqxdhDeploymentIdealCut.onBase_base _ x
    | serverSend keyId plaintext => exact PqxdhDeploymentIdealCut.onBase_base _ x
    | serverRaw raw => exact PqxdhDeploymentIdealCut.onBase_base _ x
    | beaconSend owner plaintext => exact PqxdhDeploymentIdealCut.onBase_base _ x
    | beaconRaw owner raw => exact PqxdhDeploymentIdealCut.onBase_base _ x

/-- A step whose base projection and whose backend and seed table on every outcome are known has a known ghost-free projection. -/
theorem unghost_of_base {α : Type} (work : ProbComp (α × XState KemSK (IdealBk TableState) 2))
    (target : ProbComp (α × PqxdhDeploymentNative.State KemSK)) (backend : IdealBk TableState)
    (seeds : (PqxdhRecordLiftWorld.SeedSpec 2).QueryCache)
    (projected : Prod.map id XState.base <$> work = target)
    (kept : ∀ result ∈ support work, result.2.backend = backend ∧ result.2.seeds = seeds) :
    Prod.map id PqxdhDeploymentIdealCut.unghost <$> work =
      (fun result => (result.1, (⟨result.2, backend, seeds, PqxdhDeploymentLater.Snap.empty, []⟩ :
        XState KemSK (IdealBk TableState) 2))) <$> target := by
  rw [← projected, Functor.map_map]
  apply PqxdhDeploymentKemTransfer.map_support_congr
  intro result member
  obtain ⟨sameBackend, sameSeeds⟩ := kept result member
  simp only [Prod.map, id_eq, PqxdhDeploymentIdealCut.unghost, sameBackend, sameSeeds]

/-- A real command of the handler with the ideal registration, without ghosts: the native deployment step with the pool create, with the bumped backend, the kept seed table and no ghosts. -/
theorem postStep_unghost (query : PqxdhDeploymentInterface.Spec.Domain) (x : XState KemSK (IdealBk TableState) 2)
    (real : RealAt t query x) :
    Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x =
      (fun result => (result.1, (⟨result.2, PqxdhDeploymentIdealCut.bump query x.backend, x.seeds,
        PqxdhDeploymentLater.Snap.empty, []⟩ : XState KemSK (IdealBk TableState) 2))) <$>
        (deploymentPool setup codec checks route created.seed (p.pool t) query).run x.base :=
  have step := postStep setup codec route checks t p created query x real
  unghost_of_base _ _ _ _ step.1 step.2

end Real

/-! ### The middle source handler on real requests -/

section Frame
open PqxdhDeploymentIdealPool (deploymentPool compiledPool revealPool)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A source request of a hidden kind: a raw accept, a build or a finish. -/
def HiddenKind (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) : Prop :=
  PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 3 ∨
    PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 4 ∨
    PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 5

instance : DecidablePred (HiddenKind (KemSK := KemSK)) := fun _ => by
  unfold HiddenKind
  infer_instance

/-- Two query bounds of zero give a bound of zero for the disjunction. -/
theorem bound_or_zero {ι' α : Type} {spec' : OracleSpec ι'} (work : OracleComp spec' α) (first second : ι' → Prop)
    [DecidablePred first] [DecidablePred second]
    (noFirst : work.IsQueryBoundP first 0) (noSecond : work.IsQueryBoundP second 0) :
    work.IsQueryBoundP (fun query => first query ∨ second query) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noFirst noSecond ⊢
      obtain ⟨firstAllowed, firstRest⟩ := noFirst
      obtain ⟨secondAllowed, secondRest⟩ := noSecond
      have notFirst : ¬ first query := by
        rcases firstAllowed with free | impossible
        · exact free
        · omega
      have notSecond : ¬ second query := by
        rcases secondAllowed with free | impossible
        · exact free
        · omega
      refine ⟨Or.inl (by simp [notFirst, notSecond]), fun reply => ?_⟩
      have restFirst := firstRest reply
      have restSecond := secondRest reply
      simp only [notFirst, notSecond, ↓reduceIte] at restFirst restSecond
      simpa [notFirst, notSecond] using ih reply restFirst restSecond

/-- The compiled program of a deployment command other than a raw accept, a build or a finish issues no source request of a hidden kind (from CE-3's per-kind budget `PqxdhDeploymentCompileBudget.step_bound`). -/
theorem compile_noHidden (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local)
    (other : PqxdhDeploymentCompileBudget.commandKind query ≠ 3 ∧ PqxdhDeploymentCompileBudget.commandKind query ≠ 4 ∧
      PqxdhDeploymentCompileBudget.commandKind query ≠ 5) :
    ((compileImpl setup codec route query).run copies).IsQueryBoundP (HiddenKind (KemSK := KemSK)) 0 := by
  have zero : ∀ kind : Fin 9, kind = 3 ∨ kind = 4 ∨ kind = 5 →
      PqxdhDeploymentCompileBudget.cost (.inl kind) (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
    intro kind hidden
    obtain ⟨not3, not4, not5⟩ := other
    rcases query with coin | command
    · rcases hidden with rfl | rfl | rfl <;> rfl
    · cases command <;> simp [PqxdhDeploymentCompileBudget.commandKind] at not3 not4 not5 ⊢ <;>
        rcases hidden with rfl | rfl | rfl <;> rfl
  have bound := fun kind hidden => (zero kind hidden) ▸
    PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl kind) query copies
  exact bound_or_zero _ _ _ (bound 3 (Or.inl rfl)) (bound_or_zero _ _ _ (bound 4 (Or.inr (Or.inl rfl)))
    (bound 5 (Or.inr (Or.inr rfl))))

/-- On every source request of another kind, the middle source handler is the real one. -/
theorem sourceMid_other (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ¬ HiddenKind query) :
    sourceMid setup codec route checks t p created query = realMid setup codec checks t p created query := by
  rcases query with (coin | request) | read
  · rfl
  · cases request <;> first | rfl | exact absurd (by simp [HiddenKind, PqxdhRegistrationJointRevealCosts.sourceKind,
      PqxdhRegistrationSchedule.sourceKind]) other
  · rfl

/-- On a program without raw accepts, the real middle handler is item 2's annotated pool source on the annotated source state, with the backend and the seed table kept. -/
theorem realMid_frame {α : Type} (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α)
    (noAccept : work.IsQueryBoundP (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query =
      .inl 3) 0) (m : Mid KemSK) :
    (simulateQ (realMid setup codec checks t p created) work).run m =
      (fun result => (result.1, { m with joint := result.2 })) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
          created.server.server.metadata.identityIndex (p.pool t)) work).run m.joint := by
  induction work using OracleComp.inductionOn generalizing m with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noAccept
      obtain ⟨allowed, rest⟩ := noAccept
      have notAccept : ¬ PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = .inl 3 := by
        rcases allowed with free | impossible
        · exact free
        · omega
      have kept : bumpSource query m.backend = m.backend := by
        rcases query with (coin | request) | read
        · rfl
        · cases request <;> first | rfl | exact absurd rfl notAccept
        · rfl
      have step : (realMid setup codec checks t p created query).run m =
          (fun r => (r.1, { m with joint := r.2 })) <$>
            (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
              created.server.server.metadata.identityIndex (p.pool t) query).run m.joint := by
        unfold realMid
        change (fun (r : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query ×
          PqxdhRegistrationJointSchedule.State KemSK) =>
            (r.1, ({ joint := r.2, backend := bumpSource query m.backend, seeds := m.seeds } : Mid KemSK))) <$> _ = _
        rw [kept]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, step, bind_map_left]
      refine bind_congr fun result => ?_
      have nextBound := rest result.1
      simp only [notAccept, ↓reduceIte] at nextBound
      exact ih result.1 nextBound { m with joint := result.2 }

/-- A forwarded source request whose middle step is the real one runs as item 2's annotated pool source with the bumped backend. -/
theorem sourceMid_single {β : Type} (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (finish : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query → β) (m : Mid KemSK)
    (real : (sourceMid setup codec route checks t p created query).run m =
      (realMid setup codec checks t p created query).run m) :
    (simulateQ (sourceMid setup codec route checks t p created)
        (((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query :
          OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= fun answer => pure (finish answer))).run m =
      (fun result => (result.1, { m with joint := result.2, backend := bumpSource query m.backend })) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.sourcePool setup codec checks created.seed
          created.server.server.metadata.identityIndex (p.pool t))
          (((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query :
            OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= fun answer => pure (finish answer))).run
          m.joint := by
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, real,
    map_bind, map_pure]
  unfold realMid
  exact bind_map_left _ _ _

/-- Merging owners keeps whether an owner is in the `initSent` phase. -/
theorem initSentAt_merge (copies : Local) (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ) :
    PqxdhDeploymentIdealSteps.initSentAt (owners.mapIdx fun position owner =>
        PqxdhDeploymentCompile.mergeOwner (copies.owners position) owner) index =
      PqxdhDeploymentIdealSteps.initSentAt owners index := by
  unfold PqxdhDeploymentIdealSteps.initSentAt
  rw [List.getElem?_mapIdx]
  rcases owners[index]? with _ | owner
  · rfl
  · simp only [Option.map_some]
    unfold PqxdhDeploymentCompile.mergeOwner
    rcases copies.owners index with _ | current <;> rcases phase : owner.beacon.phase <;> simp [phase]

/-- Under CE-3's merge invariant, every deployment command that is real at the merged state commutes with merging: the compiled step under the middle source handler, with the local copies merged into the middle state, is the ghost-free step of the handler with the ideal registration on the merged state. -/
theorem step_real (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local) (m : Mid KemSK)
    (inv : PqxdhDeploymentCompileStep.Inv setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (real : RealAt t query (mergeX copies m)) :
    Prod.map id (fun state : Local × Mid KemSK => mergeX state.1 state.2) <$>
        (compiledMid setup codec route checks t p created query).run (copies, m) =
      Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run (mergeX copies m) := by
  rw [postStep_unghost setup codec route checks t p created query (mergeX copies m) real]
  change _ = (fun result => (result.1, (⟨result.2, PqxdhDeploymentIdealCut.bump query m.backend, m.seeds,
    PqxdhDeploymentLater.Snap.empty, []⟩ : XState KemSK (IdealBk TableState) 2))) <$>
    (deploymentPool setup codec checks route created.seed (p.pool t) query).run
      (merge copies (PqxdhRegistrationJointSchedule.source m.joint))
  rw [← PqxdhDeploymentIdealPool.step_merge_pool setup codec checks route created.seed (p.pool t) query copies _ inv]
  have shape : (simulateQ (sourceMid setup codec route checks t p created)
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
                (realMid setup codec checks t p created (.inl (.inr (.accept raw)))).run m := by
              change (if m.backend.2.2.accepts = t.accept then _ else _) = _
              exact ite_eq_right_of_eq_false _ _ (eq_false real)
            exact sourceMid_single setup codec route checks t p created (.inl (.inr (.accept raw)))
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
                (realMid setup codec checks t p created (.inl (.inr (.build session payload)))).run m := by
              change (if buildHiddenAt m session then _ else _) = _
              rw [notHidden]
              rfl
            exact sourceMid_single setup codec route checks t p created (.inl (.inr (.build session payload)))
              (fun answer => (answer, { copies with
                log := PqxdhDeploymentCompile.logReply copies.log (.build session payload) answer })) m step
        | finish owner raw =>
            have notHidden : finishHiddenAt t m owner = false := by
              unfold finishHiddenAt
              have merged := initSentAt_merge copies (PqxdhRegistrationJointSchedule.source m.joint).owners owner
              have other : ¬ (m.backend.2.2.active = true ∧ owner = t.kem.val ∧
                  PqxdhDeploymentIdealSteps.initSentAt (PqxdhRegistrationJointSchedule.source m.joint).owners owner =
                    true) := by
                rw [← merged]
                exact real
              exact decide_eq_false other
            have step : (sourceMid setup codec route checks t p created (.inl (.inr (.finish owner raw)))).run m =
                (realMid setup codec checks t p created (.inl (.inr (.finish owner raw)))).run m := by
              change (if finishHiddenAt t m owner then _ else _) = _
              rw [notHidden]
              rfl
            exact sourceMid_single setup codec route checks t p created (.inl (.inr (.finish owner raw)))
              (fun answer => (answer, { copies with
                log := PqxdhDeploymentCompile.logReply copies.log (.finish owner raw) answer })) m step
        | _ => simp [PqxdhDeploymentCompileBudget.commandKind] at hidden
    · have other : PqxdhDeploymentCompileBudget.commandKind query ≠ 3 ∧
          PqxdhDeploymentCompileBudget.commandKind query ≠ 4 ∧ PqxdhDeploymentCompileBudget.commandKind query ≠ 5 := by
        omega
      rw [PqxdhDeploymentIdealPool.simulateQ_congr_none (sourceMid setup codec route checks t p created)
        (realMid setup codec checks t p created) HiddenKind
        (sourceMid_other setup codec route checks t p created) _ (compile_noHidden setup codec route query copies other)]
      have noAccept : ((compileImpl setup codec route query).run copies).IsQueryBoundP
          (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
        have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) (.inl 3) query copies
        have zero : PqxdhDeploymentCompileBudget.cost (.inl 3) (PqxdhDeploymentCompileBudget.commandKind query) = 0 := by
          rcases query with coin | command
          · rfl
          · cases command <;> simp [PqxdhDeploymentCompileBudget.commandKind] at other ⊢ <;> rfl
        rwa [zero] at bound
      rw [realMid_frame setup codec checks t p created _ noAccept m]
      have kept : PqxdhDeploymentIdealCut.bump query m.backend = m.backend := by
        rcases query with coin | command
        · rfl
        · cases command <;> first | rfl | simp [PqxdhDeploymentCompileBudget.commandKind] at other
      rw [kept]
  change Prod.map id _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((compileImpl setup codec route query).run copies)).run m) = _
  rw [shape]
  change _ = _ <$> (Prod.map id _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (revealPool setup codec checks created.seed (p.pool t))
      ((compileImpl setup codec route query).run copies)).run (PqxdhRegistrationJointSchedule.source m.joint)))
  rw [← PqxdhDeploymentIdealPoolSource.programPool_native setup codec checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)]
  simp only [Functor.map_map]
  rfl

end Frame

/-! ### Commuting with CE-3's Server override on the shared native state -/

section Commute
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentCompileRegistration (overrideShared overrideGame)
open PqxdhDeploymentIdealSlots (SlotSpec)

/-- A stateful computation on the shared native state commutes with CE-3's Server override (every copied peer kernel replaced by its live local copy). -/
def ShComm {M : Type → Type} [Monad M] {α : Type} (copies : Local) (work : StateT (NativeState KemSK) M α) : Prop :=
  ∀ s, work.run (overrideShared copies s) = Prod.map id (overrideShared copies) <$> work.run s

variable {M : Type → Type} [Monad M] [LawfulMonad M] (copies : Local)

theorem shComm_pure {α : Type} (value : α) : ShComm (M := M) (KemSK := KemSK) copies (pure value) := by
  intro s
  simp only [StateT.run_pure, map_pure, Prod.map, id]

theorem shComm_bind {α β : Type} (work : StateT (NativeState KemSK) M α) (next : α → StateT (NativeState KemSK) M β)
    (first : ShComm copies work) (rest : ∀ value, ShComm copies (next value)) : ShComm copies (work >>= next) := by
  intro s
  simp only [StateT.run_bind, first s, bind_map_left, map_bind]
  exact bind_congr fun result => rest result.1 result.2

/-- A local state step that commutes with the game override commutes with the shared override. -/
theorem shComm_local {α : Type} (step : PqxdhServerAuthExperiment.GameState KemSK → α × PqxdhServerAuthExperiment.GameState KemSK)
    (same : ∀ game, step (overrideGame copies game) = Prod.map id (overrideGame copies) (step game)) :
    ShComm copies (PqxdhServerAuthNative.localState step) := by
  intro s
  have stepped : step (overrideShared copies s).2 = Prod.map id (overrideGame copies) (step s.2) := same s.2
  simp only [PqxdhServerAuthNative.localState, StateT.run, map_pure, stepped]
  rfl

theorem shComm_coins {α : Type} (work : ProbComp α) :
    ShComm (KemSK := KemSK) copies (PqxdhServerAuthNative.nativeCoins work) := by
  intro s
  simp only [PqxdhServerAuthNative.nativeCoins, StateT.run, Functor.map_map]
  rfl

theorem shComm_ctx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    ShComm (KemSK := KemSK) copies (PqxdhServerAuthNative.nativeCtx work) := by
  intro s
  simp only [PqxdhServerAuthNative.nativeCtx, StateT.run, Functor.map_map]
  rfl

theorem shComm_romRootBytes (hmac : PqxdhSecretInputKdf.HmacSha512) (message : PqxdhJointDhExtractFamily.Message)
    (bytes : Pqxdh.Bytes) :
    ShComm (KemSK := KemSK) copies (PqxdhServerAuthNative.romRootBytes hmac message bytes) := by
  intro s
  simp only [PqxdhServerAuthNative.romRootBytes, StateT.run, Functor.map_map]
  rfl

theorem shComm_set (game : PqxdhServerAuthExperiment.GameState KemSK) (s : NativeState KemSK) :
    (PqxdhServerAuthNative.nativeSet (overrideGame copies game)).run (overrideShared copies s) =
      Prod.map id (overrideShared copies) <$> (PqxdhServerAuthNative.nativeSet game).run s := rfl

/-- A probabilistic shared step that commutes lifts to slot clients. -/
theorem shComm_liftS {α : Type} (work : NativeGame KemSK α) (commutes : ShComm copies work) :
    ShComm copies (fun s => PqxdhDeploymentIdealSteps.liftS (work.run s) :
      StateT (NativeState KemSK) (OracleComp SlotSpec) α) := by
  intro s
  change PqxdhDeploymentIdealSteps.liftS (work.run (overrideShared copies s)) = _
  rw [commutes s]
  simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map]
  rfl

end Commute

section Accept
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentCompileRegistration (overrideShared overrideGame)
variable (copies : Local)

/-- The native client of a raw accept (core acceptance, root, consumption) commutes with the override. -/
theorem shComm_nativeClient (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    ShComm (M := ProbComp) (KemSK := KemSK) copies (PqxdhServerAuthNative.nativeClient hmac index control binding input) := by
  unfold PqxdhServerAuthNative.nativeClient
  split
  · exact shComm_pure copies _
  · exact shComm_pure copies _
  · exact shComm_pure copies _
  · refine shComm_bind copies _ _ ?_ fun _ => shComm_bind copies _ _ ?_ fun _ => shComm_pure copies _
    · unfold PqxdhServerAuthNative.loggedRoot PqxdhServerAuthNative.romRoot
      exact shComm_bind copies _ _ (shComm_romRootBytes copies _ _ _) fun _ =>
        shComm_bind copies _ _ (shComm_local copies _ fun _ => rfl) fun _ => shComm_pure copies _
    · exact shComm_local copies _ fun _ => rfl

/-- The native accept tail after the installation of the game state (`PqxdhRegistrationJointServerAccept.tail` without its first step). -/
noncomputable def tailRest (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (input : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32)) : NativeGame KemSK (Option ℕ) :=
  match input with
  | none => pure none
  | some input => do
      let returned ← PqxdhServerAuthNative.nativeClient setup.hmac index control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
      match returned with
      | .ok (some token) => do
          PqxdhServerAuthNative.nativeModify fun current =>
            { current with pending := Function.update current.pending index (some token) }
          pure (some index)
      | _ => pure none

theorem shComm_tailRest (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (input : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32)) :
    ShComm (M := ProbComp) copies (tailRest setup publicIdentity index control input) := by
  unfold tailRest
  rcases input with _ | input
  · exact shComm_pure copies _
  · refine shComm_bind copies _ _ (shComm_nativeClient copies _ _ _ _ _) fun returned => ?_
    rcases returned with (_ | token) | _ | _
    · exact shComm_pure copies _
    · exact shComm_bind copies _ _ (shComm_local copies _ fun _ => rfl) fun _ => shComm_pure copies _
    · exact shComm_pure copies _
    · exact shComm_pure copies _

/-- The native accept tail on the state's own game state commutes with the override. -/
theorem shComm_tail (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    ShComm (M := ProbComp) copies (fun s : NativeState KemSK =>
      (PqxdhRegistrationJointServerAccept.tail setup publicIdentity s.2 collected).run s) := by
  intro s
  have shape : ∀ game : PqxdhServerAuthExperiment.GameState KemSK,
      PqxdhRegistrationJointServerAccept.tail setup publicIdentity game collected =
        (PqxdhServerAuthNative.nativeSet ({ game with
            sessions := game.sessions + 1
            server := { game.server with consumed := collected.2 } } : PqxdhServerAuthExperiment.GameState KemSK) >>=
          fun _ => tailRest setup publicIdentity game.sessions game.server.control collected.1 :
            NativeGame KemSK (Option ℕ)) := fun _ => rfl
  change (PqxdhRegistrationJointServerAccept.tail setup publicIdentity (overrideGame copies s.2) collected).run
    (overrideShared copies s) = Prod.map id (overrideShared copies) <$>
      (PqxdhRegistrationJointServerAccept.tail setup publicIdentity s.2 collected).run s
  rw [shape, shape]
  change ((PqxdhServerAuthNative.nativeSet (overrideGame copies ({ s.2 with
      sessions := s.2.sessions + 1
      server := { s.2.server with consumed := collected.2 } } : PqxdhServerAuthExperiment.GameState KemSK)) >>=
    fun _ => tailRest setup publicIdentity s.2.sessions s.2.server.control collected.1 :
      NativeGame KemSK (Option ℕ))).run (overrideShared copies s) = _
  rw [StateT.run_bind, shComm_set, bind_map_left, StateT.run_bind, map_bind]
  exact bind_congr fun result => shComm_tailRest copies setup publicIdentity _ _ _ result.2

/-- The LQ-F logged accept commutes with the override. -/
theorem shComm_acceptLogged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    ShComm (M := ProbComp) copies (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw) := by
  intro s
  unfold PqxdhDeploymentLaterServerNative.acceptLogged
  have get : ∀ state : NativeState KemSK,
      StateT.run PqxdhServerAuthNative.nativeGet state = pure (state.2, state) := fun _ => rfl
  have coins : ∀ {V : Type} (work : ProbComp V) (state : NativeState KemSK),
      StateT.run (PqxdhServerAuthNative.nativeCoins work) state = (fun value => (value, state)) <$> work :=
    fun _ _ => rfl
  simp only [StateT.run_bind, get, coins, pure_bind, bind_map_left, map_bind]
  refine bind_congr fun collected => ?_
  have tailed := shComm_tail copies setup (setup.joint.publicKeys seed) (collected.1.1, collected.2) s
  change (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) (overrideShared copies s).2
    (collected.1.1, collected.2)).run (overrideShared copies s) = _ at tailed
  rw [tailed, bind_map_left]
  rfl

/-- Every request of item 2's marker client under `tailCE` commutes with the override of the native state. -/
theorem tailCE_clientQuery_comm (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueClient.Spec Reader).Domain) (s : NativeState KemSK)
    (mark : Option (ℕ × PqxdhDeploymentIdealSlots.Coord)) :
    (PqxdhDeploymentIdealSteps.tailCE (KemSK := KemSK) hmac index (.inl query)).run (overrideShared copies s, mark) =
      Prod.map id (Prod.map (overrideShared copies) id) <$>
        (PqxdhDeploymentIdealSteps.tailCE hmac index (.inl query)).run (s, mark) := by
  rcases query with input | query
  · rcases shared : input.shared with _ | secret
    · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared, map_bind, map_pure]
      rfl
    · simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, shared, Functor.map_map]
      have root : ShComm (M := ProbComp) copies (PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index
          (List.Vector.replicate 32 0) input) := by
        unfold PqxdhRegistrationJointKemOpaqueClient.romRoot
        exact shComm_bind copies _ _ (shComm_romRootBytes copies _ _ _) fun _ =>
          shComm_bind copies _ _ (shComm_local copies _ fun _ => rfl) fun _ => shComm_pure copies _
      have rooted := root s
      simp only [StateT.run] at rooted
      rw [rooted]
      simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map, Functor.map_map]
      rfl
  · have aux : ShComm (M := ProbComp) copies (PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK query) := by
      cases query with
      | eraseShared => exact shComm_pure copies _
      | eraseInput => exact shComm_pure copies _
      | consume rid =>
          show ShComm copies (PqxdhServerAuthNative.nativeConsume rid)
          exact shComm_local copies _ fun _ => rfl
    simp only [PqxdhDeploymentIdealSteps.tailCE, StateT.run, Functor.map_map]
    have auxed := aux s
    simp only [StateT.run] at auxed
    rw [auxed]
    simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map, Functor.map_map]
    rfl

/-- Item 2's marker client under `tailCE` commutes with the override of the native state. -/
theorem tailCE_client_comm (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) α) (s : NativeState KemSK)
    (mark : Option (ℕ × PqxdhDeploymentIdealSlots.Coord)) :
    (simulateQ (PqxdhDeploymentIdealSteps.tailCE (KemSK := KemSK) hmac index)
        (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward work)).run (overrideShared copies s, mark) =
      Prod.map id (Prod.map (overrideShared copies) id) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac index)
          (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward work)).run (s, mark) := by
  rw [← QueryImpl.simulateQ_compose]
  exact (OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (PqxdhDeploymentIdealSteps.tailCE (KemSK := KemSK) hmac index ∘ₛ PqxdhRegistrationJointKemOpaqueTail.forward)
    (PqxdhDeploymentIdealSteps.tailCE hmac index ∘ₛ PqxdhRegistrationJointKemOpaqueTail.forward)
    (Prod.map (overrideShared copies) id)
    (fun query state => by
      simp only [QueryImpl.apply_compose, PqxdhRegistrationJointKemOpaqueTail.forward, simulateQ_spec_query]
      exact (tailCE_clientQuery_comm copies hmac index query state.1 state.2).symm) work (s, mark)).symm

/-- Item 2's marker tail after the installation of the game state. -/
noncomputable def opaqueRest (serverKeyId : Std.U64) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (input : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader)) :
    OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) (Option ℕ) :=
  match input with
  | none => pure none
  | some input => do
      let returned ← simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        (PqxdhRegistrationJointKemOpaqueClient.client control
          ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input)
      match returned with
      | .ok (some token) => do
          let _ ← ((PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).query (.inr (.publish index token)) :
            OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) _)
          pure (some index)
      | _ => pure none

/-- The rest of item 2's marker tail under `tailCE` commutes with the override of the native state. -/
theorem opaqueRest_comm (hmac : PqxdhSecretInputKdf.HmacSha512) (sessions : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (index : ℕ) (control : beaconcrypt_core.pqxdh.ServerState)
    (input : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader)) (u : NativeState KemSK)
    (mark : Option (ℕ × PqxdhDeploymentIdealSlots.Coord)) :
    (simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac sessions)
        (opaqueRest serverKeyId publicIdentity index control input)).run (overrideShared copies u, mark) =
      Prod.map id (Prod.map (overrideShared copies) id) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac sessions)
          (opaqueRest serverKeyId publicIdentity index control input)).run (u, mark) := by
  have publish : ∀ (slot : ℕ) (token : PqxdhServerRelatedRootConsumer.Returned)
      (state : NativeState KemSK × Option (ℕ × PqxdhDeploymentIdealSlots.Coord)),
      (PqxdhDeploymentIdealSteps.tailCE (Reader := Reader) hmac sessions (.inr (.publish slot token))).run state =
        pure ((), ((state.1.1, { state.1.2 with pending := Function.update state.1.2.pending slot (some token) }),
          state.2)) := fun _ _ _ => rfl
  unfold opaqueRest
  rcases input with _ | input
  · simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · simp only [simulateQ_bind, StateT.run_bind, map_bind]
    rw [tailCE_client_comm copies hmac sessions, bind_map_left]
    refine bind_congr fun returned => ?_
    rcases returned with ⟨(_ | token) | _ | _, after, afterMark⟩
    · simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, publish, pure_bind, simulateQ_pure,
        StateT.run_pure, map_pure]
      rfl
    · simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl
    · simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rfl

/-- Item 2's marker tail under `tailCE`, on the state's own game state, commutes with the override of the native state. -/
theorem tailCE_tail_comm (hmac : PqxdhSecretInputKdf.HmacSha512) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (s : NativeState KemSK) (mark : Option (ℕ × PqxdhDeploymentIdealSlots.Coord)) :
    (simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac (overrideShared copies s).2.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity (overrideShared copies s).2 collected)).run
        (overrideShared copies s, mark) =
      Prod.map id (Prod.map (overrideShared copies) id) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac s.2.sessions)
          (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity s.2 collected)).run (s, mark) := by
  have shape : ∀ game : PqxdhServerAuthExperiment.GameState KemSK,
      PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity game collected =
        ((PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).query (.inr (.install ({ game with
            sessions := game.sessions + 1
            server := { game.server with consumed := collected.2 } } : PqxdhServerAuthExperiment.GameState KemSK))) :
          OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) _) >>= fun _ =>
          opaqueRest serverKeyId publicIdentity game.sessions game.server.control collected.1 := fun _ => rfl
  have install : ∀ (index : ℕ) (value : PqxdhServerAuthExperiment.GameState KemSK)
      (state : NativeState KemSK × Option (ℕ × PqxdhDeploymentIdealSlots.Coord)),
      (PqxdhDeploymentIdealSteps.tailCE (Reader := Reader) hmac index (.inr (.install value))).run state =
        pure ((), ((state.1.1, value), state.2)) := fun _ _ _ => rfl
  rw [shape, shape]
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, install, pure_bind]
  exact opaqueRest_comm copies hmac s.2.sessions serverKeyId publicIdentity s.2.sessions s.2.server.control
    collected.1 (s.1, { s.2 with
      sessions := s.2.sessions + 1
      server := { s.2.server with consumed := collected.2 } }) mark

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The inactive selected accept (the LQ-F logged accept as a slot client) commutes with the override. -/
theorem acceptInactive_comm (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    ShComm copies (PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw) := by
  intro s
  have logged := shComm_acceptLogged copies setup codec checks seed raw s
  simp only [StateT.run] at logged
  simp only [PqxdhDeploymentIdealSteps.acceptInactive, StateT.run, logged, PqxdhDeploymentIdealSteps.liftS,
    OracleComp.liftComp_map, Functor.map_map]
  rfl

/-- The active selected accept commutes with the override. -/
theorem acceptActive_comm (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) :
    ShComm copies (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified) := by
  intro s
  unfold PqxdhDeploymentIdealSteps.acceptActive
  simp only [StateT.run, map_bind]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · have tailed := shComm_tail (Reader := Reader) copies setup (setup.joint.publicKeys seed) (none, consumed) s
    simp only [StateT.run] at tailed
    simp only
    rw [tailed]
    simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map, bind_map_left, map_bind, map_pure]
    rfl
  · simp only [map_bind]
    refine bind_congr fun prepared => ?_
    have tailed := tailCE_tail_comm copies setup.hmac setup.serverKeyId (setup.joint.publicKeys seed) prepared s none
    simp only [StateT.run] at tailed
    rw [tailed, bind_map_left]
    simp only [map_pure]
    rfl

/-- The selected raw accept with its encapsulation exposed commutes with the override. -/
theorem acceptExposed_comm (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) :
    ShComm copies (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw) := by
  unfold PqxdhDeploymentIdealSteps.acceptExposed
  split
  · rename_i verified _
    split
    · exact acceptActive_comm copies setup codec checks seed challenge verified
    · exact acceptInactive_comm copies setup codec checks seed raw
  · exact acceptInactive_comm copies setup codec checks seed raw

/-- The selected accept from the steps after encapsulation commutes with the override. -/
theorem acceptAfter_comm (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) :
    ShComm copies (PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge value ephemeral consumed
      logged) := by
  intro s
  unfold PqxdhDeploymentIdealActive.acceptAfter
  simp only [StateT.run, map_bind]
  refine bind_congr fun prepared => ?_
  have tailed := tailCE_tail_comm copies setup.hmac setup.serverKeyId (setup.joint.publicKeys seed) prepared s none
  simp only [StateT.run] at tailed
  rw [tailed, bind_map_left]
  simp only [map_pure]
  rfl

end Accept

/-! ### Owner k's challenge finish commutes with merging -/

section Finish
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhDeploymentCompileRegistration (overrideShared overrideGame)
open PqxdhDeploymentIdealSlots (SlotSpec Coord)
open PqxdhRegistrationJointKemEntryFactor (Output)
variable (copies : Local) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

theorem shComm_sourceRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    ShComm (M := ProbComp) (KemSK := KemSK) copies (PqxdhServerAuthNative.sourceRoot hmac input) := by
  intro s
  simp only [PqxdhServerAuthNative.sourceRoot, StateT.run, Functor.map_map]
  rfl

/-- The CE-native grouped finish commutes with the override of the native state. -/
theorem groupCE_comm (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) (s : NativeState KemSK) (mark : Option Coord) :
    (PqxdhDeploymentIdealSteps.groupCE setup codec hidden pending).run (overrideShared copies s, mark) =
      Prod.map id (Prod.map (overrideShared copies) id) <$>
        (PqxdhDeploymentIdealSteps.groupCE setup codec hidden pending).run (s, mark) := by
  unfold PqxdhDeploymentIdealSteps.groupCE
  simp only [StateT.run]
  rcases shared : pending.root.shared with _ | secret
  · simp only
    split
    · simp only [map_bind]
      refine bind_congr fun value => ?_
      have ctx := shComm_ctx (KemSK := KemSK) copies ((hidden value).hiddenAfter
        (PqxdhRegistrationJointKemPostSkeleton.embed pending)) s
      simp only [StateT.run] at ctx
      rw [ctx]
      simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map, bind_map_left, map_pure]
      rfl
    · simp only [map_pure]
      rfl
  · simp only
    have known : ShComm (M := ProbComp) copies (do
        let root ← PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot (KemSK := KemSK) setup.hmac
          (List.Vector.replicate 32 0) pending.root
        match root with
        | none => pure none
        | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative
            setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) :
        NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged)) := by
      refine shComm_bind copies _ _ ?_ fun root => ?_
      · unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot
        split
        · exact shComm_sourceRoot copies _ _
        · exact shComm_pure copies _
      · rcases root with _ | root
        · exact shComm_pure copies _
        · exact shComm_ctx copies _
    have ran := known s
    simp only [StateT.run] at ran
    erw [ran]
    simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map, Functor.map_map]
    rfl

/-- The interpreter of the grouped native owner commutes with the override of the native state, request by request. -/
theorem ownerImplCE_comm (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) {α : Type}
    (work : OracleComp (PqxdhDeploymentIdealSteps.OwnerSpecCE KemSK Response) α) (s : NativeState KemSK)
    (mark : Option Coord) :
    (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge) work).run
        (overrideShared copies s, mark) =
      Prod.map id (Prod.map (overrideShared copies) id) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge) work).run (s, mark) :=
  (OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge)
    (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge) (Prod.map (overrideShared copies) id)
    (fun query state => by
      rcases query with query | pending
      · simp only [PqxdhDeploymentIdealSteps.ownerImplCE, StateT.run, Functor.map_map]
        rfl
      · exact (groupCE_comm copies setup codec hidden pending state.1 state.2).symm) work (s, mark)).symm

/-- Owner k's challenge finish commutes with CE-3's merge when the addressed owner has no local copy. -/
theorem finishChallenge_merge (hidden : Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes)
    (native : PqxdhRegistrationSchedule.State KemSK) (free : copies.owners index = none) (mark : Option Coord) :
    (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge index raw).run
        ((merge copies native).native, mark) =
      Prod.map id (Prod.map (fun next => (merge copies next).native) id) <$>
        (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge index raw).run (native, mark) := by
  unfold PqxdhDeploymentIdealSteps.finishChallenge
  simp only [StateT.run]
  have found : (merge copies native).native.owners[index]? = native.owners[index]? := by
    rw [PqxdhDeploymentCompileRegistration.merge_native]
    simp only [List.getElem?_mapIdx, free]
    cases native.owners[index]? <;> rfl
  rw [found]
  rcases native.owners[index]? with _ | owner
  · simp only [map_pure]
    rfl
  · simp only [map_bind, map_pure]
    have ran := ownerImplCE_comm copies setup codec hidden challenge
      (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner) native.shared mark
    simp only [StateT.run] at ran
    erw [ran, bind_map_left]
    refine bind_congr fun result => ?_
    simp only [Prod.map, id_eq, PqxdhDeploymentCompileRegistration.merge_native, List.mapIdx_set, free,
      PqxdhDeploymentCompileRegistration.mergeOwner_none]

end Finish

/-! ### The factored build commutes with the Server override -/

section GenericBuild
open RustM beaconcrypt_core
variable {K M PM C : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Replace each present peer of a generic Server publication state by a function of its key ID. -/
def mapPeersG (f : Std.U64 → RawCtxGenericRoleStorage.Peer K PM → RawCtxGenericRoleStorage.Peer K PM)
    (state : PqxdhInitialGenericPublication.State K M PM C) : PqxdhInitialGenericPublication.State K M PM C :=
  { state with server := { state.server with peers := fun kid => (state.server.peers kid).map (f kid) } }

/-- Mapping a Rust result of the generic builder by `mapPeersG`. -/
def mapBuiltG (f : Std.U64 → RawCtxGenericRoleStorage.Peer K PM → RawCtxGenericRoleStorage.Peer K PM) :
    RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialGenericPublication.State K M PM C) →
    RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhInitialGenericPublication.State K M PM C) :=
  fun result => (fun value => (value.1, mapPeersG f value.2)) <$> result

theorem publish_mapPeers (f : Std.U64 → RawCtxGenericRoleStorage.Peer K PM → RawCtxGenericRoleStorage.Peer K PM)
    (state : PqxdhInitialGenericPublication.State K M PM C) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : K) (metadata : PM) (unused : f candidate.key_id = id) :
    PqxdhInitialGenericPublication.publish (mapPeersG f state) candidate kernel metadata =
      mapPeersG f (PqxdhInitialGenericPublication.publish state candidate kernel metadata) := by
  simp only [PqxdhInitialGenericPublication.publish, mapPeersG]
  congr 2
  funext kid
  by_cases same : kid = candidate.key_id
  · subst same
    simp only [Function.update_self, Option.map_some, unused, id_eq]
  · simp only [Function.update_of_ne same]

theorem afterInitialization_mapPeers (f : Std.U64 → RawCtxGenericRoleStorage.Peer K PM → RawCtxGenericRoleStorage.Peer K PM)
    (calls : RawCtxChainOwner.Calls K m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : K) (metadata : PM)
    (state : PqxdhInitialGenericPublication.State K M PM C) (unused : f candidate.key_id = id) :
    PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata
        (mapPeersG f state) =
      (fun value => (value.1, mapPeersG f value.2)) <$>
        PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  simp only [map_bind]
  refine bind_congr fun sent => ?_
  refine bind_congr fun _ => ?_
  rcases sent with ⟨advanced, _ | encrypted⟩
  · simp only [map_pure]
  · simp only [map_bind]
    refine bind_congr fun serialized => ?_
    rcases serialized with _ | serialized
    · simp only [map_pure]
    · simp only [map_pure, publish_mapPeers f state candidate advanced metadata unused]

theorem candidate_mapPeers (f : Std.U64 → RawCtxGenericRoleStorage.Peer K PM → RawCtxGenericRoleStorage.Peer K PM)
    (calls : RawCtxChainOwner.Calls K m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (initial : RustM K) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PM)
    (state : PqxdhInitialGenericPublication.State K M PM C) (unused : f candidate.key_id = id) :
    PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata (mapPeersG f state) =
      mapBuiltG f <$> PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state := by
  unfold PqxdhInitialGenericBuilder.candidate
  simp only [map_bind]
  refine bind_congr fun valid => ?_
  split
  · simp only [map_pure]
    rfl
  · simp only [map_bind]
    refine bind_congr fun reserved => ?_
    split
    · simp only [map_pure]
      rfl
    · unfold PqxdhInitialGenericBuilder.continueRust
      split
      · split
        · simp only [map_pure]
          rfl
        · split
          · simp only [map_bind]
            refine bind_congr fun allocated => ?_
            split
            · simp only [map_pure]
              rfl
            · split
              · simp only [afterInitialization_mapPeers f calls aux candidate _ _ metadata state unused,
                  Functor.map_map]
                rfl
              · simp only [map_pure]
                rfl
              · simp only [map_pure]
                rfl
          · simp only [map_pure]
            rfl
      · simp only [map_pure]
        rfl
      · simp only [map_pure]
        rfl

/-- The generic Server builder commutes with any per-key map of the present peers that leaves unoccupied key IDs alone: occupancy is read only through `isSome`, and a new peer is installed only at an unoccupied key ID. -/
theorem genericBuild_mapPeers (f : Std.U64 → RawCtxGenericRoleStorage.Peer K PM → RawCtxGenericRoleStorage.Peer K PM)
    (calls : RawCtxChainOwner.Calls K m) (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PM)
    (state : PqxdhInitialGenericPublication.State K M PM C)
    (untouched : ∀ kid, state.server.peers kid = none → f kid = id) :
    PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata (mapPeersG f state) =
      mapBuiltG f <$> PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state := by
  unfold PqxdhServerAuthSendFactor.genericBuild PqxdhInitialGenericBuilder.continueRust
  have occupancy : ∀ kid, ((mapPeersG f state).server.peers kid).isSome = (state.server.peers kid).isSome := by
    intro kid
    simp only [mapPeersG, Option.isSome_map]
  have control : (mapPeersG f state).control = state.control := rfl
  have identity : (mapPeersG f state).server.identity = state.server.identity := rfl
  have identityKeyId : (mapPeersG f state).identityKeyId = state.identityKeyId := rfl
  simp only [occupancy, control, identity, identityKeyId]
  cases next : pqxdh.server_next_key_id state.control with
  | ok value =>
      rcases value with value | _
      · dsimp only
        cases prepared : pqxdh.server_prepare_commit state.control pending
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers value).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
        | ok result =>
            rcases result with candidate | _
            · dsimp only
              obtain ⟨available, key⟩ := PqxdhDeploymentCompileRegistration.prepare_key _ _ _ _ candidate prepared
              rw [next] at key
              have same : candidate.key_id = value := by
                cases key
                rfl
              have free : state.server.peers value = none := by
                by_contra occupied
                rw [Option.isSome_iff_ne_none.mpr occupied] at available
                simp at available
              exact candidate_mapPeers f calls aux initial candidate data metadata state (by rw [same]; exact untouched value free)
            · simp only [map_pure]
              rfl
        | fail error => simp only [map_pure]; rfl
        | div => simp only [map_pure]; rfl
      · simp only [map_pure]
        rfl
  | fail error => simp only [map_pure]; rfl
  | div => simp only [map_pure]; rfl

end GenericBuild

section FactoredBuild
open PqxdhDeploymentCompileRegistration (overrideServer overrideShared overrideGame mapBuilt)
open PqxdhServerAuthNative (NativeState NativeGame)
variable (copies : Local)

/-- The replacement of a copied peer's kernel by its local copy, in the factored kernel representation. -/
def knownCopy (kid : Std.U64) (peer : RawCtxGenericRoleStorage.Peer PqxdhServerAuthSendFactor.Kernel Unit) :
    RawCtxGenericRoleStorage.Peer PqxdhServerAuthSendFactor.Kernel Unit :=
  match copies.peers kid with
  | some current => { peer with kernel := PqxdhServerAuthSendFactor.known current }
  | none => peer

theorem embed_override (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    PqxdhServerAuthSendFactor.embed (overrideServer copies state) =
      mapPeersG (knownCopy copies) (PqxdhServerAuthSendFactor.embed state) := by
  simp only [PqxdhServerAuthSendFactor.embed, overrideServer, mapPeersG]
  congr 2
  funext kid
  rcases state.server.peers kid with _ | peer
  · rfl
  · simp only [Option.map_some, knownCopy, PqxdhDeploymentCompile.mergePeer]
    rcases copies.peers kid <;> rfl

theorem native_override (state : PqxdhInitialGenericPublication.State PqxdhServerAuthSendFactor.Kernel Unit Unit
    (List Pqxdh.Bytes)) :
    PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve (mapPeersG (knownCopy copies) state) =
      overrideServer copies (PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve state) := by
  simp only [PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.nativeServer, mapPeersG, overrideServer]
  congr 2
  funext kid
  rcases state.server.peers kid with _ | peer
  · rfl
  · simp only [Option.map_some, knownCopy, PqxdhDeploymentCompile.mergePeer]
    rcases copies.peers kid <;> rfl

/-- The factored Server build commutes with the Server override when every copied peer is installed. -/
theorem factored_override {m : Type → Type} [Monad m] [LawfulMonad m]
    (receiveCall : PqxdhServerAuthSendFactor.Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      m (PqxdhServerAuthSendFactor.Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (value : PqxdhServerAuthSendFactor.Factor)
    (pending : beaconcrypt_core.pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (installed : ∀ kid current, copies.peers kid = some current → state.server.peers kid ≠ none) :
    PqxdhServerAuthLoggedSendFactor.factored receiveCall prim source aux value pending data () (overrideServer copies state) =
      mapBuilt copies <$>
        PqxdhServerAuthLoggedSendFactor.factored receiveCall prim source aux value pending data () state := by
  unfold PqxdhServerAuthLoggedSendFactor.factored
  rw [embed_override, genericBuild_mapPeers]
  · simp only [Functor.map_map]
    congr 1
    funext result
    simp only [mapBuiltG, mapBuilt, Functor.map_map]
    congr 1
    funext built
    simp only [Prod.map, id_eq, native_override]
  · intro kid free
    funext peer
    have unoccupied : state.server.peers kid = none := by
      simp only [PqxdhServerAuthSendFactor.embed, Option.map_eq_none_iff] at free
      exact free
    simp only [knownCopy, id_eq]
    rcases copied : copies.peers kid with _ | current
    · rfl
    · exact absurd unoccupied (installed kid current copied)

/-- The marked build with the factored hidden services commutes with the override when every copied peer is installed. -/
theorem buildHidden_comm {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (value : PqxdhRegistrationJointKemEntryFactor.Output) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (s : NativeState KemSK) (installed : PqxdhDeploymentCompileRegistration.Installed copies s.2) :
    (PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload).run
        (overrideShared copies s) =
      Prod.map id (overrideShared copies) <$>
        (PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
          (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload).run s := by
  unfold PqxdhDeploymentIdealSteps.buildHidden
  have get : ∀ state : NativeState KemSK,
      StateT.run PqxdhServerAuthNative.nativeGet state = pure (state.2, state) := fun _ => rfl
  simp only [StateT.run_bind, get, pure_bind]
  have second : (overrideShared copies s).2 = { s.2 with server := overrideServer copies s.2.server } := rfl
  simp only [second]
  rcases s.2.pending session with _ | token
  · simp only [StateT.run_pure, map_pure]
    rfl
  · have coins : ∀ {V : Type} (work : ProbComp V) (state : NativeState KemSK),
        StateT.run (PqxdhServerAuthNative.nativeCoins work) state = (fun value => (value, state)) <$> work :=
      fun _ _ => rfl
    simp only [StateT.run_bind, coins, bind_map_left, map_bind]
    have built := factored_override copies (fun entry _ _ => pure (entry, .None))
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
      (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks) (PqxdhServerAuthCtxMaterial.factor value)
      token.pending payload s.2.server installed
    change (((PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
      (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks) (PqxdhServerAuthCtxMaterial.factor value)
      token.pending payload () (overrideServer copies s.2.server)).run ([], s.2.ctx)) >>= _) = _
    rw [built, StateT.run_map, bind_map_left]
    refine bind_congr fun result => ?_
    simp only [PqxdhDeploymentCompileRegistration.settle_override]
    rfl

end FactoredBuild

/-! ### The hidden steps of the ideal registration commute with merging -/

section Slot
open PqxdhDeploymentIdealSlots (SlotSpec Coord detach attach)
open PqxdhDeploymentCompileRegistration (overrideShared overrideServer)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit) (copies : Local)

/-- An extended state with the local copies merged into its native registration state. -/
def mergeY {Γ : Type} {n : ℕ} (y : XState KemSK Γ n) : XState KemSK Γ n :=
  { y with base := merge copies y.base.native }

/-- The selected raw accept commutes with merging. -/
theorem acceptStep_selected_merge (raw : Pqxdh.Bytes) (y : XState KemSK IdealCore 2)
    (selected : y.backend.accepts = t.accept) :
    (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run (mergeY copies y) =
      Prod.map id (mergeY copies) <$> (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run y := by
  have chosen : (mergeY copies y).backend.accepts = t.accept := selected
  change (if (mergeY copies y).backend.accepts = t.accept then _ else _) =
    Prod.map id (mergeY copies) <$> (if y.backend.accepts = t.accept then _ else _)
  rw [ite_eq_left chosen, ite_eq_left selected]
  have exposed := acceptExposed_comm copies setup codec checks created.seed p.chosen p.challenge raw
    y.base.native.shared
  change _ <$> (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks created.seed p.chosen p.challenge raw).run
    (overrideShared copies y.base.native.shared) = _
  rw [exposed, Functor.map_map, Functor.map_map]
  rfl

/-- Whether an owner is established is kept by merging. -/
theorem establishedAt_set (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ) :
    PqxdhDeploymentIdealSteps.establishedAt (owners.mapIdx fun position owner =>
        PqxdhDeploymentCompile.mergeOwner (copies.owners position) owner) index =
      PqxdhDeploymentIdealSteps.establishedAt owners index := by
  unfold PqxdhDeploymentIdealSteps.establishedAt
  rw [List.getElem?_mapIdx]
  rcases owners[index]? with _ | owner
  · rfl
  · simp only [Option.map_some]
    unfold PqxdhDeploymentCompile.mergeOwner
    rcases copies.owners index with _ | current <;> rcases phase : owner.beacon.phase <;> simp [phase]

/-- Owner k's challenge finish commutes with merging, without ghosts, when the selected owner has no local copy. -/
theorem finishStep_challenge_merge (owner : ℕ) (raw : Pqxdh.Bytes) (y : XState KemSK IdealCore 2)
    (challenge : y.backend.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt y.base.native.owners owner = true)
    (free : copies.owners owner = none) :
    Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p
          (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created owner raw).run (mergeY copies y) =
      Prod.map id (PqxdhDeploymentIdealCut.unghost ∘ mergeY copies) <$>
        (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p
          (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created owner raw).run y := by
  have merged : (mergeY copies y).backend.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt (mergeY copies y).base.native.owners owner = true := by
    refine ⟨challenge.1, challenge.2.1, ?_⟩
    change PqxdhDeploymentIdealSteps.initSentAt (y.base.native.owners.mapIdx fun position owner =>
      PqxdhDeploymentCompile.mergeOwner (copies.owners position) owner) owner = true
    rw [initSentAt_merge]
    exact challenge.2.2
  change Prod.map id _ <$> (if (mergeY copies y).backend.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt (mergeY copies y).base.native.owners owner = true then _ else _) =
    Prod.map id _ <$> (if y.backend.active = true ∧ owner = t.kem.val ∧
      PqxdhDeploymentIdealSteps.initSentAt y.base.native.owners owner = true then _ else _)
  rw [ite_eq_left merged, ite_eq_left challenge]
  have finished := finishChallenge_merge copies setup codec
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge owner raw y.base.native free none
  change Prod.map id _ <$> ((PqxdhDeploymentIdealSteps.finishChallenge setup codec
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) p.challenge owner raw).run
      ((merge copies y.base.native).native, none) >>= _) = _
  rw [finished, bind_map_left, map_bind, map_bind]
  refine bind_congr fun result => ?_
  simp only [map_pure]
  congr 1
  simp only [Prod.map, id_eq, Function.comp, PqxdhDeploymentIdealCut.unghost, mergeY]
  have established : PqxdhDeploymentIdealSteps.establishedAt (merge copies result.2.1).native.owners owner =
      PqxdhDeploymentIdealSteps.establishedAt result.2.1.owners owner := by
    rw [PqxdhDeploymentCompileRegistration.merge_native]
    exact establishedAt_set copies _ owner
  simp only [established]
  rfl

/-- The key ID of a published peer is kept by the Server override. -/
theorem publishedKey_override (response : Option PqxdhServerRegistrationPublication.Response)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) :
    PqxdhDeploymentIdealSteps.publishedKey response (overrideServer copies server) =
      PqxdhDeploymentIdealSteps.publishedKey response server := by
  rcases response with _ | response
  · rfl
  · simp only [PqxdhDeploymentIdealSteps.publishedKey, overrideServer, Option.map_map]
    rfl

/-- The marked build commutes with merging when every copied peer is installed. -/
theorem buildStep_hidden_merge (session : ℕ) (payload : Option Pqxdh.Bytes) (y : XState KemSK IdealCore 2)
    (coords : Coord) (marked : y.backend.marks = some (session, coords))
    (pending : (y.base.native.shared.2.pending session).isSome = true)
    (installed : PqxdhDeploymentCompileRegistration.Installed copies y.base.native.shared.2) :
    (PqxdhDeploymentIdealSteps.buildStep setup codec route checks
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run
        (mergeY copies y) =
      Prod.map id (mergeY copies) <$> (PqxdhDeploymentIdealSteps.buildStep setup codec route checks
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run y := by
  have mergedMarks : (mergeY copies y).backend.marks = some (session, coords) := marked
  have hidden : session = session ∧ ((mergeY copies y).base.native.shared.2.pending session).isSome = true :=
    ⟨rfl, pending⟩
  have hiddenY : session = session ∧ (y.base.native.shared.2.pending session).isSome = true := ⟨rfl, pending⟩
  change (match (mergeY copies y).backend.marks with
    | some (index, coords) => _
    | none => _) = Prod.map id (mergeY copies) <$> (match y.backend.marks with
    | some (index, coords) => _
    | none => _)
  rw [mergedMarks, marked]
  dsimp only
  rw [ite_eq_left hidden, ite_eq_left hiddenY, map_bind]
  refine bind_congr fun value => ?_
  have built := buildHidden_comm copies setup codec checks value session payload y.base.native.shared installed
  change PqxdhDeploymentIdealSteps.liftS ((PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK)
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value) session payload).run
      (overrideShared copies y.base.native.shared)) >>= _ = _
  rw [built]
  simp only [PqxdhDeploymentIdealSteps.liftS, OracleComp.liftComp_map, bind_map_left, map_bind, map_pure]
  refine bind_congr fun result => ?_
  have server : (overrideShared copies result.2).2.server = overrideServer copies result.2.2.server := rfl
  simp only [Prod.map, id_eq, server, publishedKey_override]
  rfl

/-- A slot-program command of the ideal registration that commutes with merging (without ghosts) at the slot program's state of `toX m` gives a slot-core command that commutes with merging at `mergeX copies m`. -/
theorem idealReg_merge (query : PqxdhRecordLiftInterface.EnvQuery) (m : Mid KemSK)
    (commutes : Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
          (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created query).run
          (mergeY copies (detach (toX m))) =
      Prod.map id (PqxdhDeploymentIdealCut.unghost ∘ mergeY copies) <$>
        (PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
          (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created query).run
          (detach (toX m))) :
    Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (idealReg setup codec route checks t p created query).run (mergeX copies m) =
      Prod.map id (PqxdhDeploymentIdealCut.unghost ∘ mergeY copies) <$>
        (idealReg setup codec route checks t p created query).run (toX m) := by
  change Prod.map id _ <$> (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created query).run
      (mergeX copies m) =
    Prod.map id _ <$> (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created query).run
      (toX m)
  rw [PqxdhDeploymentIdealSlots.slotCore_run, PqxdhDeploymentIdealSlots.slotCore_run]
  have detached : detach (mergeX copies m) = mergeY copies (detach (toX m)) := rfl
  rw [detached]
  have left : ∀ {β : Type} (work : OracleComp SlotSpec (β × XState KemSK IdealCore 2))
      (state : PqxdhRegistrationJointKemSecondEntry.Alloc Coord 2 × TableState)
      (finish : XState KemSK IdealCore 2 → XState KemSK IdealCore 2),
      (fun r => (r.1.1, attach (finish r.1.2) r.2.1 r.2.2)) <$>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) work).run state =
        (fun r => (r.1.1, attach r.1.2 r.2.1 r.2.2)) <$>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
            (Prod.map id finish <$> work)).run state := by
    intro β work state finish
    rw [simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  rw [Functor.map_map, Functor.map_map]
  change (fun (r : (PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK IdealCore 2) ×
      (PqxdhRegistrationJointKemSecondEntry.Alloc Coord 2 × TableState)) =>
        (r.1.1, attach (PqxdhDeploymentIdealCut.unghost r.1.2) r.2.1 r.2.2)) <$> _ =
    (fun (r : (PqxdhRecordLiftInterface.EnvSpec.Range query × XState KemSK IdealCore 2) ×
      (PqxdhRegistrationJointKemSecondEntry.Alloc Coord 2 × TableState)) =>
        (r.1.1, attach ((PqxdhDeploymentIdealCut.unghost ∘ mergeY copies) r.1.2) r.2.1 r.2.2)) <$> _
  rw [left, left, commutes]
  rfl

/-- A forwarded registration command with logged reply, run by the compiled handler over the middle source handler. -/
theorem compiledMid_forward (request : PqxdhRegistrationSchedule.Request) (command : PqxdhDeploymentInterface.Command)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.CommandSpec command)
    (copies : Local) (m : Mid KemSK) :
    (simulateQ (sourceMid setup codec route checks t p created)
        ((PqxdhDeploymentCompile.forwardLogged request command reply).run copies)).run m =
      (fun result => ((reply result.1, { copies with log := (PqxdhDeploymentCompile.logReply copies.log command
        (reply result.1)) }), result.2)) <$> (sourceMid setup codec route checks t p created (.inl (.inr request))).run m := by
  show (simulateQ (sourceMid setup codec route checks t p created)
      (PqxdhDeploymentCompile.forwardLogged request command reply copies)).run m = _
  simp only [PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run_map]
  rfl

/-- The view of a middle state after a step of the ideal registration on `toX m`, with the copies merged, is the step's state with the copies merged and no ghosts. -/
theorem mergeX_fromX (copies : Local) (log : PqxdhDeploymentCompile.Log) (m : Mid KemSK)
    (z : XState KemSK (IdealBk TableState) 2) :
    mergeX { copies with log := log } (fromX m z) = PqxdhDeploymentIdealCut.unghost (mergeY copies z) := by
  simp only [mergeX, fromX, source_rejoin, PqxdhDeploymentCompileStep.merge_log, PqxdhDeploymentIdealCut.unghost,
    mergeY]


/-- The selected raw accept commutes with merging: under CE-3's merge invariant, the compiled step under the middle source handler, with the copies merged, is the ghost-free step of the handler with the ideal registration on the merged state. -/
theorem step_accept_selected (raw : Pqxdh.Bytes) (copies : Local) (m : Mid KemSK)
    (selected : m.backend.2.2.accepts = t.accept) :
    Prod.map id (fun state : Local × Mid KemSK => mergeX state.1 state.2) <$>
        (compiledMid setup codec route checks t p created (.inr (.accept raw))).run (copies, m) =
      Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) (.inr (.accept raw))).run
          (mergeX copies m) := by
  change Prod.map id _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((PqxdhDeploymentCompile.forwardLogged (.accept raw) (.accept raw) id).run copies)).run m) =
    Prod.map id PqxdhDeploymentIdealCut.unghost <$> (idealReg setup codec route checks t p created
      ⟨.accept raw, trivial⟩).run (mergeX copies m)
  rw [compiledMid_forward]
  have middle : (sourceMid setup codec route checks t p created (.inl (.inr (.accept raw)))).run m =
      (idealMid setup codec route checks t p created ⟨.accept raw, trivial⟩).run m := by
    change (if m.backend.2.2.accepts = t.accept then _ else _) = _
    exact ite_eq_left selected
  rw [middle]
  have commutes := acceptStep_selected_merge setup codec route checks t p created copies raw (detach (toX m)) selected
  have slot := idealReg_merge setup codec route checks t p created copies ⟨.accept raw, trivial⟩ m (by
    change Prod.map id _ <$> (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
      (mergeY copies (detach (toX m))) = Prod.map id _ <$>
        (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run (detach (toX m))
    rw [commutes, Functor.map_map]
    rfl)
  rw [slot]
  have unfolded : (idealMid setup codec route checks t p created ⟨.accept raw, trivial⟩).run m =
      (fun r => (r.1, fromX m r.2)) <$> (idealReg setup codec route checks t p created
        ⟨.accept raw, trivial⟩).run (toX m) := rfl
  rw [unfolded]
  simp only [Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  simp only [Prod.map, id_eq, Function.comp, mergeX_fromX]

/-- The marked build commutes with merging when every copied peer is installed. -/
theorem step_build_hidden (session : ℕ) (payload : Option Pqxdh.Bytes) (copies : Local) (m : Mid KemSK)
    (hidden : buildHiddenAt m session = true)
    (installed : PqxdhDeploymentCompileRegistration.Installed copies m.joint.shared.2) :
    Prod.map id (fun state : Local × Mid KemSK => mergeX state.1 state.2) <$>
        (compiledMid setup codec route checks t p created (.inr (.build session payload))).run (copies, m) =
      Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created)
          (.inr (.build session payload))).run (mergeX copies m) := by
  change Prod.map id _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((PqxdhDeploymentCompile.forwardLogged (.build session payload) (.build session payload) id).run copies)).run m) =
    Prod.map id PqxdhDeploymentIdealCut.unghost <$> (idealReg setup codec route checks t p created
      ⟨.build session payload, trivial⟩).run (mergeX copies m)
  rw [compiledMid_forward]
  have middle : (sourceMid setup codec route checks t p created (.inl (.inr (.build session payload)))).run m =
      (idealMid setup codec route checks t p created ⟨.build session payload, trivial⟩).run m := by
    change (if buildHiddenAt m session then _ else _) = _
    exact ite_eq_left hidden
  rw [middle]
  obtain ⟨coords, marked, pending⟩ : ∃ coords, m.backend.2.2.marks = some (session, coords) ∧
      (m.joint.shared.2.pending session).isSome = true := by
    unfold buildHiddenAt at hidden
    rcases found : m.backend.2.2.marks with _ | ⟨index, coords⟩
    · rw [found] at hidden
      cases hidden
    · rw [found] at hidden
      obtain ⟨same, pending⟩ := of_decide_eq_true hidden
      subst same
      exact ⟨coords, rfl, pending⟩
  have commutes := buildStep_hidden_merge setup codec route checks created copies session payload (detach (toX m))
    coords marked pending installed
  have slot := idealReg_merge setup codec route checks t p created copies ⟨.build session payload, trivial⟩ m (by
    change Prod.map id _ <$> (PqxdhDeploymentIdealSteps.buildStep setup codec route checks
      (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run
      (mergeY copies (detach (toX m))) = Prod.map id _ <$> (PqxdhDeploymentIdealSteps.buildStep setup codec route checks
        (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks) created session payload).run
        (detach (toX m))
    rw [commutes, Functor.map_map]
    rfl)
  rw [slot]
  have unfolded : (idealMid setup codec route checks t p created ⟨.build session payload, trivial⟩).run m =
      (fun r => (r.1, fromX m r.2)) <$> (idealReg setup codec route checks t p created
        ⟨.build session payload, trivial⟩).run (toX m) := rfl
  rw [unfolded]
  simp only [Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  simp only [Prod.map, id_eq, Function.comp, mergeX_fromX]

/-- Owner k's challenge finish commutes with merging when only established owners are copied. -/
theorem step_finish_hidden (owner : ℕ) (raw : Pqxdh.Bytes) (copies : Local) (m : Mid KemSK)
    (hidden : finishHiddenAt t m owner = true)
    (copied : PqxdhDeploymentCompileRegistration.Copied copies (PqxdhRegistrationJointSchedule.source m.joint)) :
    Prod.map id (fun state : Local × Mid KemSK => mergeX state.1 state.2) <$>
        (compiledMid setup codec route checks t p created (.inr (.finish owner raw))).run (copies, m) =
      Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created)
          (.inr (.finish owner raw))).run (mergeX copies m) := by
  change Prod.map id _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created)
      ((PqxdhDeploymentCompile.forwardLogged (.finish owner raw) (.finish owner raw) id).run copies)).run m) =
    Prod.map id PqxdhDeploymentIdealCut.unghost <$> (idealReg setup codec route checks t p created
      ⟨.finish owner raw, trivial⟩).run (mergeX copies m)
  rw [compiledMid_forward]
  have middle : (sourceMid setup codec route checks t p created (.inl (.inr (.finish owner raw)))).run m =
      (idealMid setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run m := by
    change (if finishHiddenAt t m owner then _ else _) = _
    exact ite_eq_left hidden
  rw [middle]
  have challenge := of_decide_eq_true hidden
  have free : copies.owners owner = none := by
    have sent := challenge.2.2
    unfold PqxdhDeploymentIdealSteps.initSentAt at sent
    rcases found : (PqxdhRegistrationJointSchedule.source m.joint).owners[owner]? with _ | current
    · rw [found] at sent
      cases sent
    · rw [found] at sent
      refine PqxdhDeploymentCompileRegistration.uncopied copies _ copied owner current found ?_
      rintro ⟨control, associatedData, kernel, phase⟩
      simp only [phase] at sent
      cases sent
  have slot := idealReg_merge setup codec route checks t p created copies ⟨.finish owner raw, trivial⟩ m
    (finishStep_challenge_merge setup codec route checks t p created copies owner raw (detach (toX m)) challenge free)
  rw [slot]
  have unfolded : (idealMid setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run m =
      (fun r => (r.1, fromX m r.2)) <$> (idealReg setup codec route checks t p created
        ⟨.finish owner raw, trivial⟩).run (toX m) := rfl
  rw [unfolded]
  simp only [Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  simp only [Prod.map, id_eq, Function.comp, mergeX_fromX]

/-- The selected raw accept with any native step that commutes with the override commutes with merging. -/
theorem selectedStep_merge (step : StateT (PqxdhServerAuthNative.NativeState KemSK) (OracleComp SlotSpec)
      PqxdhDeploymentIdealSteps.AcceptOut) (commutes : ShComm copies step) (y : XState KemSK IdealCore 2) :
    (PqxdhDeploymentIdealActive.selectedStep step).run (mergeY copies y) =
      Prod.map id (mergeY copies) <$> (PqxdhDeploymentIdealActive.selectedStep step).run y := by
  unfold PqxdhDeploymentIdealActive.selectedStep
  change _ <$> step.run (overrideShared copies y.base.native.shared) =
    Prod.map id (mergeY copies) <$> (_ <$> step.run y.base.native.shared)
  rw [commutes, Functor.map_map, Functor.map_map]
  rfl

end Slot

/-! ### The CE layer: the compiled middle execution merges to the ideal registration -/

section Layer
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- One step of the CE layer: under CE-3's merge invariant, merging the local copies into the middle state after the compiled step under the middle source handler is the ghost-free step of the handler with the ideal registration on the merged state, for every deployment command. -/
theorem step_mergeMid (query : PqxdhDeploymentInterface.Spec.Domain) (copies : Local) (m : Mid KemSK)
    (inv : PqxdhDeploymentCompileStep.Inv setup codec copies (PqxdhRegistrationJointSchedule.source m.joint)) :
    Prod.map id (fun state : Local × Mid KemSK => mergeX state.1 state.2) <$>
        (compiledMid setup codec route checks t p created query).run (copies, m) =
      Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run (mergeX copies m) := by
  by_cases real : RealAt t query (mergeX copies m)
  · exact step_real setup codec route checks t p created query copies m inv real
  · rcases query with coin | command
    · exact absurd trivial real
    · cases command with
      | accept raw =>
          have selected : m.backend.2.2.accepts = t.accept := not_not.mp real
          exact step_accept_selected setup codec route checks t p created raw copies m selected
      | build session payload =>
          have hidden : buildHiddenAt m session = true := by
            simp only [RealAt, not_forall, not_not] at real
            obtain ⟨index, coords, marked, same, pending⟩ := real
            subst same
            unfold buildHiddenAt
            rw [show m.backend.2.2.marks = some (index, coords) from marked]
            exact decide_eq_true ⟨rfl, pending⟩
          exact step_build_hidden setup codec route checks t p created session payload copies m hidden inv.installed
      | finish owner raw =>
          have hidden : finishHiddenAt t m owner = true := by
            have challenge := not_not.mp real
            unfold finishHiddenAt
            refine decide_eq_true ⟨challenge.1, challenge.2.1, ?_⟩
            have merged := initSentAt_merge copies (PqxdhRegistrationJointSchedule.source m.joint).owners owner
            rw [← merged]
            exact challenge.2.2
          exact step_finish_hidden setup codec route checks t p created owner raw copies m hidden inv.copied
      | _ => exact absurd trivial real

/-- The CE layer: for any invariant that implies CE-3's merge invariant and is kept by every compiled step under the middle source handler, merging the final local copies into the final middle state of the compiled program's middle execution gives the ghost-free run of the deployment program by the handler with the ideal registration from the merged state, jointly with the program's output. -/
theorem compile_simulationMid {X : Type} (good : Local → Mid KemSK → Prop)
    (sound : ∀ copies m, good copies m →
      PqxdhDeploymentCompileStep.Inv setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (preserved : ∀ query copies m, good copies m →
      ∀ result ∈ support ((compiledMid setup codec route checks t p created query).run (copies, m)),
        good result.2.1 result.2.2)
    (program : OracleComp PqxdhDeploymentInterface.Spec X) (copies : Local) (m : Mid KemSK) (start : good copies m) :
    (fun result => (result.1.1, mergeX result.1.2 result.2)) <$>
        (simulateQ (sourceMid setup codec route checks t p created)
          ((simulateQ (compileImpl setup codec route) program).run copies)).run m =
      Prod.map id PqxdhDeploymentIdealCut.unghost <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) program).run
          (mergeX copies m) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiledMid setup codec route checks t p created)
    (PqxdhRegistrationJointKemObserverFree.eraseImpl PqxdhDeploymentIdealCut.unghost
      (handlerWith setup codec route (idealReg setup codec route checks t p created)))
    (fun state => good state.1 state.2) (fun state => mergeX state.1 state.2)
    (fun query state holds result supported => preserved query state.1 state.2 holds result supported)
    (fun query state holds => step_mergeMid setup codec route checks t p created query state.1 state.2
      (sound state.1 state.2 holds))
    program (copies, m) start
  have erased := PqxdhRegistrationJointKemObserverFree.run_erase PqxdhDeploymentIdealCut.unghost (fun _ => rfl)
    (handlerWith setup codec route (idealReg setup codec route checks t p created))
    (fun query state => PqxdhDeploymentIdealCut.idealStep_unghost setup codec route checks t p created query state)
    program (mergeX copies m)
  have fixed : PqxdhDeploymentIdealCut.unghost (mergeX copies m) = mergeX copies m := rfl
  rw [fixed] at erased
  rw [erased, ← simulated]
  rfl

end Layer

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.source_rejoin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.source_rejoin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.postStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.postStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.unghost_of_base' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.unghost_of_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.postStep_unghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.postStep_unghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.bound_or_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.bound_or_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.compile_noHidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.compile_noHidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.sourceMid_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.sourceMid_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.realMid_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.realMid_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.sourceMid_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.sourceMid_single

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.initSentAt_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.initSentAt_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_local

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_romRootBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_romRootBytes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_liftS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_liftS

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_nativeClient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_nativeClient

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_tailRest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_tailRest

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_acceptLogged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_acceptLogged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.tailCE_clientQuery_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.tailCE_clientQuery_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.tailCE_client_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.tailCE_client_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.opaqueRest_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.opaqueRest_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.tailCE_tail_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.tailCE_tail_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptInactive_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptInactive_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptActive_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptActive_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptExposed_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptExposed_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptAfter_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptAfter_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_sourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.shComm_sourceRoot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.groupCE_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.groupCE_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.ownerImplCE_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.ownerImplCE_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.finishChallenge_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.finishChallenge_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.publish_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.publish_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.afterInitialization_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.afterInitialization_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.candidate_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.candidate_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.genericBuild_mapPeers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.genericBuild_mapPeers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.embed_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.embed_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.native_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.native_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.factored_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.factored_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.buildHidden_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.buildHidden_comm

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptStep_selected_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.acceptStep_selected_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.establishedAt_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.establishedAt_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.finishStep_challenge_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.finishStep_challenge_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.publishedKey_override' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.publishedKey_override

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.buildStep_hidden_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.buildStep_hidden_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.idealReg_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.idealReg_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.compiledMid_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.compiledMid_forward

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.mergeX_fromX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.mergeX_fromX

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_accept_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_accept_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_build_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_build_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_finish_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_finish_hidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.selectedStep_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.selectedStep_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_mergeMid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.step_mergeMid

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.compile_simulationMid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource.compile_simulationMid
