-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCompile

/-! LQ-F upstream, unit B2: the CE layer of the middle run of the later second compile lemma (the logged counterpart of CE-11b unit U6's merge layer in `PqxdhDeploymentIdealPostSource` and of `PqxdhDeploymentIdealPostGood`). `PqxdhDeploymentIdealLaterBranch` reduced the frozen target `PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget` to the active branch `ActiveBranchL`, in which both sides continue after the selected raw accept: item 2's side with the logged continuation `compiledNextL` (the compiled continuation of the run part, the terminal reads, the Server read and the post part, a program of the logged source), the CE side with the handler with the ideal registration and then the real post phase, which reads the LQ-F ghosts (the finish snapshot and the Server ephemeral log). This module runs the logged continuation under one source handler, the logged middle source handler, and shows that the CE side is its merge image, ghosts included.

- The logged middle state and handler: `MidL` (CE-11b's middle state with the log), `sourceMidL` (a raw accept is the logged annotated accept with the accept counter advanced, the Server read is the logged source's read, every other source14 request is CE-11b's middle source handler `sourceMid` with the log kept), its source14 part `sourceMidS` and the compiled handler with the finish snapshot over it, `compiledMidL`. Facts: `sourceMidL_embed`, `sourceMidL_inl`, `sourceMidS_quiet` (a program without raw accepts keeps the log), `preRead_mid` (the finish pre-read captures the current fields and changes nothing).
- The ghosts: `reghost`, and `idealStep_ghost`: every request of the handler with the ideal registration other than a raw accept writes the LQ-F ghosts (the snapshot capture of a finish, the log kept) and reads none (through `realRegAt_ghost`, `onBase_ghost`, `onSlots_ghost`, `slotCore_ghost`, `idealProg_ghost`); `handler_acceptOther`: a raw accept other than the selected ordinal is the native logged accept with the accept counter advanced and the logged entry appended.
- The merge layer: `mergeXL` (CE-3's merge of the compiled program's local copies into the native state of the annotated source state, with the backend, the seed table, the compiled program's snapshot and the log), `compiledMidL_quiet` and `compiledMidL_accept` (one compiled step, unfolded), `acceptSource_source` (the logged annotated accept erases to the native logged accept), `step_mergeMidL` (one step: a raw accept by `PqxdhDeploymentLaterServerCompile.accept_merge`, every other command by CE-11b's `PqxdhDeploymentIdealPostSource.step_mergeMid` with the ghosts of `idealStep_ghost` and `PqxdhDeploymentLaterCompile.snapshot_merge`), the invariant `GoodMidL` (CE-11b's `GoodMid`) and `goodMidL_step` (kept under the approved codec contracts, a raw accept through `PqxdhDeploymentLaterServerCompile.server_good`), `compile_simulationMidL` (the whole run part) and `compiled_run` (the embedded compiled program under the logged middle source handler is the compiled middle handler's run).
- The rest of the compiled LQ-F program (`PqxdhDeploymentIdealLaterCut.restOf`): `sourceStep_field`, `read_mid` and `terminal_mid` (the terminal reads return the reveal entries of the native owners and change only the annotated pools' transcripts), `serverRead_mid` (the Server read returns the Server's identity slot with the log), `post_zero` and `post_mid` (the post part runs as source14's native post phase on the merged state, `PqxdhDeploymentLaterCompile.compile_post`), `restOf_middle` (the rest, merged at the end, is the native post phase on the reveal of the merged state, as `PqxdhDeploymentLaterServerCompile.server_continuation`), and `laterTail_middle` (the real post phase from the merge image is the rest under the logged middle source handler, read off through the merge image with the mark of the middle state).

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`, CE-3's invariant, the selected accept behind the accept counter, and for the rest the Server's identity slot holding its seed. These are program equalities and invariant facts. They charge nothing and make no security claim. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentLater (Snap PostSpec snapshotAt finishOwner)
open PqxdhDeploymentLaterCompile (compileSnapImpl preRead)
open PqxdhDeploymentLaterServerSource (Log embed)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealBk IdealCore TableState idealReg idealProg realRegAt onSlots liftS)
open PqxdhDeploymentIdealSlots (detach)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid realMid compiledMid mergeX bumpSource)
open PqxdhDeploymentIdealCut (unghost)
open PqxdhRegistrationJointRevealCosts (sourceKind)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The logged middle state: the middle state of CE-11b's post-challenge simulation and the Server ephemeral log. -/
abbrev MidL (KemSK : Type) := Mid KemSK × Log

/-! ### The logged middle source handler and the compiled handler over it -/

section Handler
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The logged middle source handler: a raw accept is the logged annotated accept (`PqxdhDeploymentLaterServerSource.source`) with the accept counter advanced and its entry appended to the log; the Server read is the logged source's read; every other source14 request is CE-11b's middle source handler with the log kept. -/
noncomputable def sourceMidL :
    QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK) (StateT (MidL KemSK) ProbComp)
  | .inl (.inl (.inr (.accept raw))) => fun s =>
      (fun r => (r.1, (⟨r.2.1, bumpSource (KemSK := KemSK) (.inl (.inr (.accept raw))) s.1.backend, s.1.seeds⟩,
          r.2.2))) <$>
        (PqxdhDeploymentLaterServerSource.source setup codec checks created.seed
          created.server.server.metadata.identityIndex (.inl (.inl (.inr (.accept raw))))).run (s.1.joint, s.2)
  | .inl query => fun s => (fun r => (r.1, (r.2, s.2))) <$> (sourceMid setup codec route checks t p created query).run s.1
  | .inr read => fun s => (fun r => (r.1, (⟨r.2.1, s.1.backend, s.1.seeds⟩, r.2.2))) <$>
      (PqxdhDeploymentLaterServerSource.source setup codec checks created.seed
        created.server.server.metadata.identityIndex (.inr read)).run (s.1.joint, s.2)

/-- The logged middle source handler on source14 requests. -/
noncomputable def sourceMidS :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (MidL KemSK) ProbComp) :=
  fun query => sourceMidL setup codec route checks t p created (.inl query)

/-- The compiled handler with the finish snapshot (`PqxdhDeploymentLaterCompile.compileSnapImpl`) over the logged middle source handler, on the compiled program's snapshot and local copies and the logged middle state. -/
noncomputable def compiledMidL :
    QueryImpl Spec (StateT ((Snap × Local) × MidL KemSK) ProbComp) :=
  ((sourceMidS setup codec route checks t p created).mapStateTBase (compileSnapImpl setup codec route)).flattenStateT

/-- Embedded source14 programs run by the logged middle source handler are run by its source14 part. -/
theorem sourceMidL_embed {α : Type} (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α) :
    simulateQ (sourceMidL setup codec route checks t p created) (simulateQ embed work) =
      simulateQ (sourceMidS setup codec route checks t p created) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, embed, simulateQ_spec_query, ih]
      rfl

/-- The logged middle source handler on a source14 request other than a raw accept is the middle source handler with the log kept. -/
theorem sourceMidL_inl (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw))) (m : Mid KemSK) (log : Log) :
    (sourceMidL setup codec route checks t p created (.inl query)).run (m, log) =
      (fun r => (r.1, (r.2, log))) <$> (sourceMid setup codec route checks t p created query).run m := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case accept raw => exact absurd rfl (other raw)
    all_goals rfl
  · rfl

/-- A source14 program that issues no raw accept runs, under the logged middle source handler, as under the middle source handler, and keeps the log. -/
theorem sourceMidS_quiet {α : Type} (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α)
    (noAccept : work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 3) 0) (m : Mid KemSK)
    (log : Log) :
    (simulateQ (sourceMidS setup codec route checks t p created) work).run (m, log) =
      (fun r => (r.1, (r.2, log))) <$> (simulateQ (sourceMid setup codec route checks t p created) work).run m := by
  induction work using OracleComp.inductionOn generalizing m with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at noAccept
    obtain ⟨allowed, rest⟩ := noAccept
    have notAccept : sourceKind (KemSK := KemSK) query ≠ .inl 3 := by
      rcases allowed with free | impossible
      · exact free
      · omega
    have other : ∀ raw, query ≠ .inl (.inr (.accept raw)) := fun raw same => notAccept (by rw [same]; rfl)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [show (sourceMidS setup codec route checks t p created query).run (m, log) =
      (fun r => (r.1, (r.2, log))) <$> (sourceMid setup codec route checks t p created query).run m from
        sourceMidL_inl setup codec route checks t p created query other m log, bind_map_left]
    apply bind_congr
    intro result
    have next := rest result.1
    simp only [notAccept, ite_false] at next
    exact ih result.1 next result.2

/-- The finish pre-read under the middle source handler is the snapshot capture on the current owners of the annotated source state, and changes nothing. -/
theorem preRead_mid (snap : Snap) (target : Option ℕ) (m : Mid KemSK) :
    (simulateQ (sourceMid setup codec route checks t p created) (preRead (KemSK := KemSK) snap target)).run m =
      pure (snapshotAt snap (PqxdhRegistrationJointSchedule.source m.joint).owners target, m) := by
  have read : ∀ (index : ℕ) (field : PqxdhRegistrationJointLiveRead.Field), field ≠ .identity → field ≠ .kem →
      (simulateQ (sourceMid setup codec route checks t p created)
        (PqxdhDeploymentLaterCompile.readQuery (KemSK := KemSK) index field)).run m =
        pure (PqxdhDeploymentLater.fieldOf (PqxdhRegistrationJointSchedule.source m.joint).owners index field, m) := by
    intro index field notIdentity notKem
    simp only [PqxdhDeploymentLaterCompile.readQuery, simulateQ_spec_query]
    change (fun r => (r.1, ({ m with joint := r.2, backend := m.backend } : Mid KemSK))) <$>
      (pure (PqxdhRegistrationJointLiveRead.sourceStep (index, field) m.joint) : ProbComp _) = _
    rw [map_pure]
    simp only [PqxdhRegistrationJointLiveRead.sourceStep, PqxdhDeploymentLater.fieldOf,
      PqxdhRegistrationJointSchedule.source, List.getElem?_map]
    rcases found : m.joint.owners[index]? with _ | entry
    · rfl
    · cases field
      · exact absurd rfl notIdentity
      · exact absurd rfl notKem
      all_goals rfl
  cases target with
  | none => simp only [preRead, simulateQ_pure, StateT.run_pure, snapshotAt]
  | some index =>
      simp only [preRead, simulateQ_bind, StateT.run_bind, read index .prekey (by decide) (by decide), pure_bind,
        read index .oneTime (by decide) (by decide), simulateQ_pure, StateT.run_pure, snapshotAt]

end Handler

/-! ### The merge image of a logged middle state -/

/-- The extended deployment state of a logged middle state with the compiled program's snapshot and local copies: CE-3's merge of the copies into the native state of the annotated source, the backend, the seed table, the snapshot and the log. -/
def mergeXL (state : (Snap × Local) × MidL KemSK) : XState KemSK (IdealBk TableState) 2 :=
  ⟨merge state.1.2 (PqxdhRegistrationJointSchedule.source state.2.1.joint), state.2.1.backend, state.2.1.seeds,
    state.1.1, state.2.2⟩

/-- Resetting the ghosts of the merge image gives CE-11b's merge image. -/
theorem unghost_mergeXL (state : (Snap × Local) × MidL KemSK) :
    unghost (mergeXL state) = mergeX state.1.2 state.2.1 := rfl

/-! ### The LQ-F ghosts of the handler with the ideal registration -/

section Ghost
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The ghosts after a command other than a raw accept: the finish snapshot of the state before it at the command's target, and the log before it. -/
def reghost {Bk : Type} {n : ℕ} (target : Option ℕ) (x y : XState KemSK Bk n) : XState KemSK Bk n :=
  { y with snap := snapshotAt x.snap x.base.native.owners target, log := x.log }

/-- `realRegAt` on a command other than a raw accept writes the ghosts of `reghost` and reads none. -/
theorem realRegAt_ghost {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (notAccept : ∀ raw, query.val ≠ .accept raw) (y : XState KemSK Bk n) :
    (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run y =
      (fun r => (r.1, reghost (finishOwner (.inr query.val)) y r.2)) <$>
        (realRegAt (Bk := Bk) (n := n) setup codec route checks created query).run (unghost y) := by
  have quiet : ∀ raw, (.inr query.val : Spec.Domain) ≠ .inr (.accept raw) := fun raw same =>
    notAccept raw (Sum.inr.inj same)
  have left := PqxdhDeploymentLaterServerGame.handler_quiet setup codec checks route created.seed _ quiet y.base y.log
  have right := PqxdhDeploymentLaterServerGame.handler_quiet setup codec checks route created.seed _ quiet
    (unghost y).base (unghost y).log
  simp only [StateT.run] at left right
  simp only [realRegAt, StateT.run]
  rw [left, right, Functor.map_map, Functor.map_map, Functor.map_map]
  rfl

/-- A base step writes the ghosts of `reghost` at no target and reads none. -/
theorem onBase_ghost {Bk : Type} {n : ℕ} {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (y : XState KemSK Bk n) :
    (PqxdhDeploymentBackend.onBase step).run y =
      (fun r => (r.1, reghost none y r.2)) <$> (PqxdhDeploymentBackend.onBase step).run (unghost y) := by
  simp only [PqxdhDeploymentBackend.onBase, LazyOracleDiscard.StateLens.lift, StateT.run, Functor.map_map]
  rfl

/-- A coins-only slot step inherits the ghost behaviour of its probabilistic step. -/
theorem onSlots_ghost {Γ : Type} {n : ℕ} {α : Type} (step : StateT (XState KemSK Γ n) ProbComp α) (target : Option ℕ)
    (ghost : ∀ y, step.run y = (fun r => (r.1, reghost target y r.2)) <$> step.run (unghost y))
    (y : XState KemSK Γ n) :
    (onSlots step).run y = (fun r => (r.1, reghost target y r.2)) <$> (onSlots step).run (unghost y) := by
  change liftS (step.run y) = _ <$> liftS (step.run (unghost y))
  rw [liftS, liftS, ← OracleComp.liftComp_map, ghost]

/-- A slot core inherits the ghost behaviour of its slot program. -/
theorem slotCore_ghost {Γ : Type} {n : ℕ} (prog : PqxdhLiveServerConstruction.Created Unit → PqxdhDeploymentIdealSlots.SlotProgram KemSK Γ n)
    {S : Type} (svc : PqxdhDeploymentSeedSplit.SlotService S n) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (target : Option ℕ)
    (ghost : ∀ y, (prog created query).run y =
      (fun r => (r.1, reghost target y r.2)) <$> (prog created query).run (unghost y))
    (x : XState KemSK (S × (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord n × Γ)) n) :
    (PqxdhDeploymentIdealSlots.slotCore prog svc created query).run x =
      (fun r => (r.1, reghost target x r.2)) <$>
        (PqxdhDeploymentIdealSlots.slotCore prog svc created query).run (unghost x) := by
  rw [PqxdhDeploymentIdealSlots.slotCore_run, PqxdhDeploymentIdealSlots.slotCore_run,
    show detach (unghost x) = unghost (detach x) from rfl, ghost (detach x), simulateQ_map, StateT.run_map,
    Functor.map_map, Functor.map_map]
  rfl

variable {count : ℕ} (t : Target count) (p : Params KemSK count)
  (hidden : PqxdhRegistrationJointKemEntryFactor.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Every command of the ideal registration other than a raw accept writes the ghosts of `reghost` at its finish target and reads none. -/
theorem idealProg_ghost (query : PqxdhRecordLiftInterface.EnvQuery) (notAccept : ∀ raw, query.val ≠ .accept raw)
    (y : XState KemSK IdealCore 2) :
    (idealProg setup codec route checks t p hidden created query).run y =
      (fun r => (r.1, reghost (finishOwner (.inr query.val)) y r.2)) <$>
        (idealProg setup codec route checks t p hidden created query).run (unghost y) := by
  rcases query with ⟨command, env⟩
  cases command with
  | create pin keyId =>
      exact onSlots_ghost _ none (fun z => onBase_ghost _ z) y
  | bundle owner =>
      exact onSlots_ghost _ _ (fun z => realRegAt_ghost setup codec route checks created _ notAccept z) y
  | hmac key message =>
      exact onSlots_ghost _ _ (fun z => realRegAt_ghost setup codec route checks created _ notAccept z) y
  | accept raw => exact absurd rfl (notAccept raw)
  | build session payload =>
      change (PqxdhDeploymentIdealSteps.buildStep setup codec route checks hidden created session payload).run y =
        _ <$> (PqxdhDeploymentIdealSteps.buildStep setup codec route checks hidden created session payload).run
          (unghost y)
      rcases marked : y.backend.marks with _ | ⟨index, coords⟩
      · rw [PqxdhDeploymentIdealSteps.buildStep_unmarked setup codec route checks hidden created session payload y marked,
          PqxdhDeploymentIdealSteps.buildStep_unmarked setup codec route checks hidden created session payload (unghost y)
            marked]
        exact onSlots_ghost _ _ (fun z => realRegAt_ghost setup codec route checks created _ notAccept z) y
      · by_cases hit : index = session ∧ (y.base.native.shared.2.pending session).isSome
        · change (match y.backend.marks with
              | some (index, coords) => _
              | none => _) =
            _ <$> (match (unghost y).backend.marks with
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
          exact onSlots_ghost _ _ (fun z => realRegAt_ghost setup codec route checks created _ notAccept z) y
  | finish owner raw =>
      change (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p hidden created owner raw).run y =
        _ <$> (PqxdhDeploymentIdealSteps.finishStep setup codec route checks t p hidden created owner raw).run
          (unghost y)
      by_cases challenge : y.backend.active = true ∧ owner = t.kem.val ∧ PqxdhDeploymentIdealSteps.initSentAt
          y.base.native.owners owner = true
      · change (if y.backend.active = true ∧ owner = t.kem.val ∧
              PqxdhDeploymentIdealSteps.initSentAt y.base.native.owners owner = true then _ else _) =
          _ <$> (if (unghost y).backend.active = true ∧ owner = t.kem.val ∧
              PqxdhDeploymentIdealSteps.initSentAt (unghost y).base.native.owners owner = true then _ else _)
        have challenge' : (unghost y).backend.active = true ∧ owner = t.kem.val ∧
            PqxdhDeploymentIdealSteps.initSentAt (unghost y).base.native.owners owner = true := challenge
        rw [ite_eq_left challenge, ite_eq_left challenge']
        simp only [map_bind, map_pure]
        rfl
      · rw [PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p hidden created owner raw y challenge,
          PqxdhDeploymentIdealSteps.finishStep_real setup codec route checks t p hidden created owner raw (unghost y)
            challenge]
        exact onSlots_ghost _ _ (fun z => realRegAt_ghost setup codec route checks created _ notAccept z) y
  | hash bytes => exact absurd env id
  | serverSend keyId plaintext => exact absurd env id
  | serverRaw raw => exact absurd env id
  | beaconSend owner plaintext => exact absurd env id
  | beaconRaw owner raw => exact absurd env id

/-- Every request of the handler with the ideal registration other than a raw accept writes the LQ-F ghosts of `reghost` (the snapshot capture of a finish, the log kept) and reads none: its run from a state is its run from the state with the ghosts reset, with the ghosts set afterwards. -/
theorem idealStep_ghost (query : Spec.Domain) (notAccept : ∀ raw, query ≠ .inr (.accept raw))
    (x : XState KemSK (IdealBk TableState) 2) :
    (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run x =
      (fun r => (r.1, reghost (finishOwner query) x r.2)) <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run (unghost x) := by
  have core : ∀ env : PqxdhRecordLiftInterface.EnvQuery, (∀ raw, env.val ≠ .accept raw) →
      (idealReg setup codec route checks t p created env).run x =
        (fun r => (r.1, reghost (finishOwner (.inr env.val)) x r.2)) <$>
          (idealReg setup codec route checks t p created env).run (unghost x) := fun env other =>
    slotCore_ghost _ PqxdhDeploymentSeedSplit.tableService created env _
      (fun y => idealProg_ghost setup codec route checks t p _ created env other y) x
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, map_bind, map_pure]
    rfl
  · cases command with
    | create pin keyId => exact core ⟨.create pin keyId, trivial⟩ (fun _ same => by cases same)
    | bundle owner => exact core ⟨.bundle owner, trivial⟩ (fun _ same => by cases same)
    | accept raw => exact absurd rfl (notAccept raw)
    | build session payload => exact core ⟨.build session payload, trivial⟩ (fun _ same => by cases same)
    | finish owner raw => exact core ⟨.finish owner raw, trivial⟩ (fun _ same => by cases same)
    | hmac key message => exact core ⟨.hmac key message, trivial⟩ (fun _ same => by cases same)
    | hash bytes => exact onBase_ghost _ x
    | serverSend keyId plaintext => exact onBase_ghost _ x
    | serverRaw raw => exact onBase_ghost _ x
    | beaconSend owner plaintext => exact onBase_ghost _ x
    | beaconRaw owner raw => exact onBase_ghost _ x

/-- A raw accept other than the selected ordinal, under the handler with the ideal registration: the native logged accept on the shared state, with the accept counter advanced and the logged entry appended to the log. -/
theorem handler_acceptOther (raw : Pqxdh.Bytes) (x : XState KemSK (IdealBk TableState) 2)
    (other : x.backend.2.2.accepts ≠ t.accept) :
    (handlerWith setup codec route (idealReg setup codec route checks t p created) (.inr (.accept raw))).run x =
      (fun r => (r.1.1, (⟨{ x.base with native := r.2 },
          (x.backend.1, (x.backend.2.1, { x.backend.2.2 with accepts := x.backend.2.2.accepts + 1 })), x.seeds,
          x.snap, x.log ++ [r.1.2]⟩ : XState KemSK (IdealBk TableState) 2))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
          created.seed raw)).run x.base.native := by
  have run := PqxdhDeploymentIdealCut.slotCore_lift (idealProg setup codec route checks t p
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)) PqxdhDeploymentSeedSplit.tableService
    created ⟨.accept raw, trivial⟩ x _
    (PqxdhDeploymentIdealSteps.acceptStep_other setup codec route checks t p created raw (detach x) other)
  change (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created
    ⟨.accept raw, trivial⟩).run x = _
  rw [run]
  simp only [realRegAt, StateT.run, Functor.map_map]
  change _ <$> ((fun result => (result.1, ({ (detach x).base with native := result.2.1 }, result.2.2))) <$>
    ((fun result => (result.1.1, (result.2, (detach x).log ++ [result.1.2]))) <$>
      (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
        created.seed raw)).run (detach x).base.native)) = _
  simp only [Functor.map_map]
  rfl

end Ghost

/-! ### The compiled middle step and its merge image -/

section Merge
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A compiled command other than a raw accept over the logged middle source handler: CE-11b's compiled middle step (`PqxdhDeploymentIdealPostSource.compiledMid`) with the snapshot capture on the current owners of the annotated source state, and the log kept. -/
theorem compiledMidL_quiet (query : Spec.Domain) (notAccept : ∀ raw, query ≠ .inr (.accept raw)) (snap : Snap)
    (copies : Local) (m : Mid KemSK) (log : Log) :
    (compiledMidL setup codec route checks t p created query).run ((snap, copies), (m, log)) =
      (fun r => (r.1, ((snapshotAt snap (PqxdhRegistrationJointSchedule.source m.joint).owners (finishOwner query),
          r.2.1), (r.2.2, log)))) <$>
        (compiledMid setup codec route checks t p created query).run (copies, m) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMidS setup codec route checks t p created) ((compileSnapImpl setup codec route query).run
      (snap, copies))).run (m, log) = _
  rw [sourceMidS_quiet setup codec route checks t p created _
    (PqxdhDeploymentLaterServerCompile.snap_quiet setup codec route query notAccept (snap, copies)) m log]
  change _ = _ <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMid setup codec route checks t p created) ((compileImpl setup codec route query).run copies)).run m)
  have unfolded : (compileSnapImpl setup codec route query).run (snap, copies) =
      preRead snap (finishOwner query) >>= fun captured =>
        (compileImpl setup codec route query).run copies >>= fun result => pure (result.1, (captured, result.2)) := rfl
  rw [unfolded]
  simp only [simulateQ_bind, StateT.run_bind, preRead_mid, pure_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
    Functor.map_map]

/-- The logged annotated raw accept of the Server, with the annotations erased, is the native logged accept on the native registration state. -/
theorem acceptSource_source (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks
          created.seed created.server.server.metadata.identityIndex raw)).run state =
      (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
        created.seed raw)).run (PqxdhRegistrationJointSchedule.source state) := by
  rw [PqxdhRegistrationSchedule.onShared_run,
    show PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks created.seed raw
        (PqxdhRegistrationJointSchedule.source state).shared =
      (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks created.seed raw).run state.shared from rfl,
    ← PqxdhDeploymentLaterServerNative.acceptSource_native setup codec checks created.seed
      created.server.server.metadata.identityIndex raw (state.pool, state.shared)]
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, Functor.map_map]
  rfl

/-- A compiled raw accept over the logged middle source handler: the logged annotated accept on the annotated source state, with the accept counter advanced, the logged entry appended to the log and the reply recorded in the compiled program's public log. -/
theorem compiledMidL_accept (raw : Pqxdh.Bytes) (snap : Snap) (copies : Local) (m : Mid KemSK) (log : Log) :
    (compiledMidL setup codec route checks t p created (.inr (.accept raw))).run ((snap, copies), (m, log)) =
      (fun r => (r.1.1, ((snap, { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) r.1.1 }),
          ((⟨r.2, bumpSource (KemSK := KemSK) (.inl (.inr (.accept raw))) m.backend, m.seeds⟩ : Mid KemSK),
            log ++ [r.1.2])))) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks
          created.seed created.server.server.metadata.identityIndex raw)).run m.joint := by
  have program : (compileSnapImpl setup codec route (.inr (.accept raw))).run (snap, copies) =
      (fun answer => (answer, (snap, { copies with log := (PqxdhDeploymentCompile.logReply copies.log (.accept raw)
        answer) }))) <$> ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) :
          OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) := by
    simp only [compileSnapImpl, finishOwner, preRead, compileImpl, PqxdhDeploymentCompile.forwardLogged,
      PqxdhDeploymentCompile.forward, StateT.run, pure_bind, bind_assoc, map_eq_bind_pure_comp]
    rfl
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (sourceMidS setup codec route checks t p created) ((compileSnapImpl setup codec route
      (.inr (.accept raw))).run (snap, copies))).run (m, log) = _
  rw [program, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  change _ <$> (_ <$> ((fun r => (r.1, ((⟨r.2.1, bumpSource (KemSK := KemSK) (.inl (.inr (.accept raw))) m.backend,
      m.seeds⟩ : Mid KemSK), r.2.2))) <$> ((fun result => (result.1.1, (result.2, log ++ [result.1.2]))) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec
          checks created.seed created.server.server.metadata.identityIndex raw)).run m.joint))) = _
  simp only [Functor.map_map]

/-- One step of the logged middle compile lemma: from a state with CE-3's merge invariant and the selected accept behind the accept counter, the merge image after a compiled step over the logged middle source handler is the step of the handler with the ideal registration from the merge image, ghosts included. A raw accept is the native logged accept on both sides (`handler_acceptOther`, `PqxdhDeploymentLaterServerCompile.accept_merge`); every other command is CE-11b's `PqxdhDeploymentIdealPostSource.step_mergeMid` with the LQ-F ghosts of `idealStep_ghost` (the finish pre-read captures what the handler captures, `PqxdhDeploymentLaterCompile.snapshot_merge`). -/
theorem step_mergeMidL (query : Spec.Domain) (state : (Snap × Local) × MidL KemSK)
    (inv : PqxdhDeploymentCompileStep.Inv setup codec state.1.2
      (PqxdhRegistrationJointSchedule.source state.2.1.joint))
    (beyond : t.accept < state.2.1.backend.2.2.accepts) :
    (fun result => (result.1, mergeXL result.2)) <$>
        (compiledMidL setup codec route checks t p created query).run state =
      (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run (mergeXL state) := by
  obtain ⟨⟨snap, copies⟩, m, log⟩ := state
  by_cases accept : ∃ raw, query = .inr (.accept raw)
  · obtain ⟨raw, rfl⟩ := accept
    rw [compiledMidL_accept, handler_acceptOther setup codec route checks t p created raw _ (Nat.ne_of_gt beyond),
      show (mergeXL ((snap, copies), (m, log))).base.native =
        (merge copies (PqxdhRegistrationJointSchedule.source m.joint)).native from rfl,
      PqxdhDeploymentLaterServerCompile.accept_merge, Functor.map_map,
      ← acceptSource_source setup codec checks created raw m.joint, Functor.map_map, Functor.map_map]
    rfl
  · have notAccept : ∀ raw, query ≠ .inr (.accept raw) := fun raw same => accept ⟨raw, same⟩
    rw [compiledMidL_quiet setup codec route checks t p created query notAccept snap copies m log, Functor.map_map,
      idealStep_ghost setup codec route checks t p created query notAccept, unghost_mergeXL]
    have reghosted : (fun r => (r.1, reghost (finishOwner query) (mergeXL ((snap, copies), (m, log))) r.2)) <$>
        (handlerWith setup codec route (idealReg setup codec route checks t p created) query).run
          (mergeX copies m) =
        (fun r => (r.1, reghost (finishOwner query) (mergeXL ((snap, copies), (m, log))) r.2)) <$>
          (Prod.map id unghost <$> (handlerWith setup codec route (idealReg setup codec route checks t p created)
            query).run (mergeX copies m)) := by
      rw [Functor.map_map]
      rfl
    rw [reghosted, ← PqxdhDeploymentIdealPostSource.step_mergeMid setup codec route checks t p created query copies m
      inv, Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun r => ?_)
    simp only [Prod.map, id, mergeXL, reghost, mergeX, PqxdhDeploymentLaterCompile.snapshot_merge]

/-- The CE side of the logged middle invariant: CE-11b's `PqxdhDeploymentIdealPostGood.GoodMid` (CE-3's invariant on the local copies and the native state of the annotated source state, with the selected accept behind the accept counter) on the compiled program's local copies and the middle state. -/
def GoodMidL (t : Target count) (state : (Snap × Local) × MidL KemSK) : Prop :=
  PqxdhDeploymentIdealPostGood.GoodMid setup codec t state.1.2 state.2.1

/-- Every compiled step over the logged middle source handler keeps `GoodMidL`, under the approved codec contracts: a command other than a raw accept by CE-11b's `PqxdhDeploymentIdealPostGood.middleInv`, a raw accept by `PqxdhDeploymentLaterServerCompile.server_good` on its erasure. -/
theorem goodMidL_step (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (query : Spec.Domain)
    (state : (Snap × Local) × MidL KemSK) (good : GoodMidL setup codec t state)
    (result : Spec.Range query × ((Snap × Local) × MidL KemSK))
    (supported : result ∈ support ((compiledMidL setup codec route checks t p created query).run state)) :
    GoodMidL setup codec t result.2 := by
  obtain ⟨⟨snap, copies⟩, m, log⟩ := state
  by_cases accept : ∃ raw, query = .inr (.accept raw)
  · obtain ⟨raw, rfl⟩ := accept
    rw [compiledMidL_accept, support_map] at supported
    obtain ⟨r, member, rfl⟩ := supported
    have native : (r.1, PqxdhRegistrationJointSchedule.source r.2) ∈ support
        ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks
          created.seed raw)).run (PqxdhRegistrationJointSchedule.source m.joint)) := by
      rw [← acceptSource_source, support_map]
      exact ⟨r, member, rfl⟩
    have compiled : (r.1.1, ((snap, { copies with
        log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) r.1.1 }),
          (PqxdhRegistrationJointSchedule.source r.2, log ++ [r.1.2]))) ∈ support
        ((PqxdhDeploymentLaterServerCompile.compiledImpl setup codec checks route created.seed
          (.inr (.accept raw))).run ((snap, copies), (PqxdhRegistrationJointSchedule.source m.joint, log))) := by
      rw [PqxdhDeploymentLaterServerCompile.accept_compiled, support_map]
      exact ⟨(r.1, PqxdhRegistrationJointSchedule.source r.2), native, rfl⟩
    refine ⟨PqxdhDeploymentLaterServerCompile.server_good setup codec checks route created.seed phase1 phase2 _
      ((snap, copies), (PqxdhRegistrationJointSchedule.source m.joint, log)) good.1 _ compiled, ?_⟩
    have beyond : t.accept < m.backend.2.2.accepts := good.2
    change t.accept < m.backend.2.2.accepts + 1
    omega
  · have notAccept : ∀ raw, query ≠ .inr (.accept raw) := fun raw same => accept ⟨raw, same⟩
    rw [compiledMidL_quiet setup codec route checks t p created query notAccept snap copies m log, support_map]
      at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact (PqxdhDeploymentIdealPostGood.middleInv setup codec route checks phase1 phase2 t p created).preserved query
      copies m good inner member

/-- The logged middle compile lemma: from a state with `GoodMidL`, under the approved codec contracts, the compiled program over the logged middle source handler, with the merge image taken at the end, has exactly the distribution of the run of the handler with the ideal registration from the merge image, jointly with the output, the snapshot and the log. -/
theorem compile_simulationMidL (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) {X : Type} (program : OracleComp Spec X)
    (state : (Snap × Local) × MidL KemSK) (start : GoodMidL setup codec t state) :
    (fun result => (result.1, mergeXL result.2)) <$>
        (simulateQ (compiledMidL setup codec route checks t p created) program).run state =
      (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) program).run
        (mergeXL state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (GoodMidL setup codec t) mergeXL
    (fun query state good result supported =>
      goodMidL_step setup codec route checks t p created phase1 phase2 query state good result supported)
    (fun query state good => step_mergeMidL setup codec route checks t p created query state
      (PqxdhDeploymentCompileInvariant.good_inv setup codec _ _ good.1) good.2)
    program state start

/-- The compiled program with the finish snapshot, embedded in the logged source, under the logged middle source handler, is the compiled middle handler's run. -/
theorem compiled_run {X : Type} (program : OracleComp Spec X) (state : (Snap × Local) × MidL KemSK) :
    (simulateQ (sourceMidL setup codec route checks t p created)
        (simulateQ embed ((simulateQ (compileSnapImpl setup codec route) program).run state.1))).run state.2 =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (compiledMidL setup codec route checks t p created) program).run state := by
  rw [sourceMidL_embed, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  rfl

end Merge

/-! ### The rest of the compiled LQ-F program over the logged middle source handler -/

section Rest
open PqxdhDeploymentLaterCompile (terminal readQuery)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- An annotated field read returns the field of the native owners and changes only the annotated pools' transcripts. -/
theorem sourceStep_field (index : ℕ) (field : PqxdhRegistrationJointLiveRead.Field)
    (joint : PqxdhRegistrationJointSchedule.State KemSK) :
    (PqxdhRegistrationJointLiveRead.sourceStep (index, field) joint).1 =
      PqxdhDeploymentLater.fieldOf (PqxdhRegistrationJointSchedule.source joint).owners index field ∧
    PqxdhRegistrationJointSchedule.source (PqxdhRegistrationJointLiveRead.sourceStep (index, field) joint).2 =
      PqxdhRegistrationJointSchedule.source joint ∧
    (PqxdhRegistrationJointLiveRead.sourceStep (index, field) joint).2.pool.1.seeds = joint.pool.1.seeds := by
  unfold PqxdhRegistrationJointLiveRead.sourceStep
  rcases found : joint.owners[index]? with _ | entry
  · simp [PqxdhDeploymentLater.fieldOf, PqxdhRegistrationJointSchedule.source, List.getElem?_map, found]
  · refine ⟨?_, rfl, ?_⟩
    · simp only [PqxdhDeploymentLater.fieldOf, PqxdhRegistrationJointSchedule.source, List.getElem?_map, found,
        Option.map_some, Option.bind_some]
      cases field
      · rfl
      · simp only [PqxdhRegistrationJointLiveRead.entrySource, PqxdhRegistrationJointLiveRead.value]
        cases PqxdhRegistrationJointOwnership.activeKey entry.owner <;> rfl
      all_goals rfl
    · cases field
      · rfl
      · simp only [PqxdhRegistrationJointLiveRead.entrySource]
        cases PqxdhRegistrationJointOwnership.activeKey entry.owner <;> rfl
      all_goals rfl

/-- A source14 field read under the logged middle source handler returns the field of the native owners of the annotated source state, keeps the log, the backend and the seed table, and changes no native owner or identity seed. -/
theorem read_mid (index : ℕ) (field : PqxdhRegistrationJointLiveRead.Field) (m : Mid KemSK) (log : Log) :
    ∃ m' : Mid KemSK, PqxdhRegistrationJointSchedule.source m'.joint = PqxdhRegistrationJointSchedule.source m.joint ∧
      m'.joint.pool.1.seeds = m.joint.pool.1.seeds ∧ m'.backend = m.backend ∧ m'.seeds = m.seeds ∧
      (simulateQ (sourceMidS setup codec route checks t p created) (readQuery (KemSK := KemSK) index field)).run
        (m, log) =
        pure (PqxdhDeploymentLater.fieldOf (PqxdhRegistrationJointSchedule.source m.joint).owners index field,
          (m', log)) := by
  obtain ⟨value, source, seeds⟩ := sourceStep_field index field m.joint
  refine ⟨{ m with joint := (PqxdhRegistrationJointLiveRead.sourceStep (index, field) m.joint).2 }, source, seeds, rfl,
    rfl, ?_⟩
  simp only [readQuery, simulateQ_spec_query]
  change (fun r => (r.1, (r.2, log))) <$> ((fun r => (r.1, ({ m with joint := r.2, backend := m.backend } : Mid KemSK))) <$>
    (pure (PqxdhRegistrationJointLiveRead.sourceStep (index, field) m.joint) : ProbComp _)) = _
  rw [map_pure, map_pure, value]

/-- The terminal reads under the logged middle source handler return the reveal entries of the native owners of the annotated source state at the read handles, keep the log, the backend and the seed table, and change no native owner or identity seed. -/
theorem terminal_mid (snap : Snap) (indices : List ℕ) (m : Mid KemSK) (log : Log) :
    ∃ m' : Mid KemSK, PqxdhRegistrationJointSchedule.source m'.joint = PqxdhRegistrationJointSchedule.source m.joint ∧
      m'.joint.pool.1.seeds = m.joint.pool.1.seeds ∧ m'.backend = m.backend ∧ m'.seeds = m.seeds ∧
      (simulateQ (sourceMidS setup codec route checks t p created) (terminal (KemSK := KemSK) snap indices)).run
        (m, log) =
        pure (indices.filterMap (PqxdhDeploymentLater.revealAt (PqxdhRegistrationJointSchedule.source m.joint).owners
          snap), (m', log)) := by
  induction indices generalizing m with
  | nil => exact ⟨m, rfl, rfl, rfl, rfl, by simp only [terminal, simulateQ_pure, StateT.run_pure, List.filterMap_nil]⟩
  | cons index rest ih =>
      obtain ⟨m₁, source₁, seeds₁, backend₁, table₁, run₁⟩ :=
        read_mid setup codec route checks t p created index .identity m log
      obtain ⟨m₂, source₂, seeds₂, backend₂, table₂, run₂⟩ :=
        read_mid setup codec route checks t p created index .prekey m₁ log
      obtain ⟨m₃, source₃, seeds₃, backend₃, table₃, run₃⟩ :=
        read_mid setup codec route checks t p created index .oneTime m₂ log
      obtain ⟨m', source', seeds', backend', table', run'⟩ := ih m₃
      rw [source₂, source₁] at run₃
      rw [source₁] at run₂
      rw [source₃, source₂, source₁] at run'
      refine ⟨m', by rw [source', source₃, source₂, source₁], by rw [seeds', seeds₃, seeds₂, seeds₁],
        by rw [backend', backend₃, backend₂, backend₁], by rw [table', table₃, table₂, table₁], ?_⟩
      simp only [terminal, simulateQ_bind, StateT.run_bind, run₁, run₂, run₃, run', pure_bind, simulateQ_pure,
        StateT.run_pure, PqxdhDeploymentLaterCompile.revealEntry_field, List.filterMap_cons]
      cases PqxdhDeploymentLater.revealAt (PqxdhRegistrationJointSchedule.source m.joint).owners snap index <;> rfl

/-- The Server read under the logged middle source handler returns the Server's identity slot with the log, records the reveal in the identity pool's transcript and changes nothing else. -/
theorem serverRead_mid (m : Mid KemSK) (log : Log) :
    (sourceMidL setup codec route checks t p created (.inr ())).run (m, log) =
      pure ((m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]?, log),
        ((⟨{ m.joint with pool := (PqxdhDynamicIdentityPool.record (.inr (.reveal created.server.server.metadata.identityIndex))
          (m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]?) m.joint.pool.1, m.joint.pool.2) },
          m.backend, m.seeds⟩ : Mid KemSK), log)) := by
  simp only [sourceMidL, PqxdhDeploymentLaterServerSource.source, PqxdhRegistrationJointServerSchedule.onBackend,
    PqxdhRegistrationJointFinish.onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_pure]

/-- The post part of the compiled LQ-F program issues no request of a registration kind whose compile cost is zero for the coin, HMAC and BLAKE2b commands. -/
theorem post_zero {Out : Type} (kind : Fin 9) (coins : PqxdhDeploymentCompileBudget.cost (.inl kind) 0 = 0)
    (hmac : PqxdhDeploymentCompileBudget.cost (.inl kind) 6 = 0)
    (hash : PqxdhDeploymentCompileBudget.cost (.inl kind) 7 = 0) (adversary : OracleComp PostSpec Out)
    (copies : Local) :
    ((simulateQ (compileImpl setup codec route) (simulateQ PqxdhDeploymentLater.postEmbed adversary)).run
      copies).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = .inl kind) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  refine PqxdhDeploymentCompileSecrecy.simulate_zero ((compileImpl setup codec route) ∘ₛ PqxdhDeploymentLater.postEmbed)
    _ (fun query state => ?_) _ copies
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) (.inl kind) (.inl coin)
      state
    rwa [show PqxdhDeploymentCompileBudget.commandKind (.inl coin) = 0 from rfl, coins] at bound
  · simp only [QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) (.inl kind)
      (.inr (.hmac key message)) state
    rwa [show PqxdhDeploymentCompileBudget.commandKind (.inr (.hmac key message)) = 6 from rfl, hmac] at bound
  · simp only [QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) (.inl kind)
      (.inr (.hash bytes)) state
    rwa [show PqxdhDeploymentCompileBudget.commandKind (.inr (.hash bytes)) = 7 from rfl, hash] at bound

/-- The post part of the compiled LQ-F program under the logged middle source handler, from a state with CE-3's invariant: merged at the end, the native post phase on the merged state, with the log, the backend and the seed table kept (`PqxdhDeploymentLaterCompile.compile_post`; the post part issues no raw accept, build, finish or create, so it runs under the real middle handler, item 2's annotated pool source and source14's native handler). -/
theorem post_mid {Out : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (adversary : OracleComp PostSpec Out)
    (copies : Local) (m : Mid KemSK) (log : Log)
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint)) :
    (fun result => (result.1.1, (merge result.1.2 (PqxdhRegistrationJointSchedule.source result.2.1.joint),
        result.2.1.backend, result.2.2))) <$>
        (simulateQ (sourceMidS setup codec route checks t p created)
          ((simulateQ (compileImpl setup codec route) (simulateQ PqxdhDeploymentLater.postEmbed adversary)).run
            copies)).run (m, log) =
      (fun result => (result.1, (result.2, m.backend, log))) <$>
        (simulateQ (PqxdhDeploymentLater.postImpl setup codec checks created.seed) adversary).run
          (merge copies (PqxdhRegistrationJointSchedule.source m.joint)) := by
  have noAccept := post_zero setup codec route (KemSK := KemSK) 3 (by decide) (by decide) (by decide) adversary copies
  have noBuild := post_zero setup codec route (KemSK := KemSK) 4 (by decide) (by decide) (by decide) adversary copies
  have noFinish := post_zero setup codec route (KemSK := KemSK) 5 (by decide) (by decide) (by decide) adversary copies
  have noCreate := post_zero setup codec route (KemSK := KemSK) 1 (by decide) (by decide) (by decide) adversary copies
  have noHidden : ((simulateQ (compileImpl setup codec route) (simulateQ PqxdhDeploymentLater.postEmbed adversary)).run
      copies).IsQueryBoundP (PqxdhDeploymentIdealPostSource.HiddenKind (KemSK := KemSK)) 0 :=
    PqxdhDeploymentIdealPostSource.bound_or_zero _ _ _ noAccept
      (PqxdhDeploymentIdealPostSource.bound_or_zero _ _ _ noBuild noFinish)
  rw [sourceMidS_quiet setup codec route checks t p created _ noAccept m log,
    PqxdhDeploymentIdealPool.simulateQ_congr_none (sourceMid setup codec route checks t p created)
      (realMid setup codec checks t p created) PqxdhDeploymentIdealPostSource.HiddenKind
      (PqxdhDeploymentIdealPostSource.sourceMid_other setup codec route checks t p created) _ noHidden,
    PqxdhDeploymentIdealPostSource.realMid_frame setup codec checks t p created _ noAccept m, Functor.map_map,
    Functor.map_map]
  have native := PqxdhDeploymentIdealPoolSource.programPool_native setup codec checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)
    ((simulateQ (compileImpl setup codec route) (simulateQ PqxdhDeploymentLater.postEmbed adversary)).run copies) m.joint
  rw [PqxdhDeploymentIdealPool.simulateQ_congr_none (PqxdhDeploymentIdealPool.revealPool setup codec checks created.seed
    (p.pool t)) (PqxdhRegistrationJointRevealSchedule.native setup codec checks created.seed) _
    (PqxdhDeploymentIdealPool.revealPool_agree setup codec checks created.seed (p.pool t)) _ noCreate] at native
  rw [← PqxdhDeploymentLaterCompile.compile_post setup codec checks route created.seed phase1 phase2 adversary copies
    _ good, ← native, Functor.map_map, Functor.map_map]

/-- The rest of the compiled LQ-F program after its run part (the terminal reads, the Server read and the post part, `PqxdhDeploymentIdealLaterCut.restOf`) under the logged middle source handler, from a state with CE-3's invariant whose Server slot holds the Server's seed, with the merge image of the final state: the native post phase on the merged state, on the reveal of the merged state (the Beacon-side reveal and the Server seed with the log), with the ledger, the snapshot and the log kept. This is `PqxdhDeploymentLaterServerCompile.server_continuation` over the logged middle source handler. -/
theorem restOf_middle {X Out : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (value : X × PqxdhDeploymentSecrecy.Ledger) (snap : Snap) (copies : Local) (m : Mid KemSK) (log : Log)
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (slot : m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) :
    (fun result => (result.1.1, (result.1.2.1, (result.1.2.2.1,
        (merge result.1.2.2.2 (PqxdhRegistrationJointSchedule.source result.2.1.joint), result.2.2))))) <$>
        (simulateQ (sourceMidL setup codec route checks t p created)
          (PqxdhDeploymentIdealLaterCut.restOf setup codec route second (value, (snap, copies)))).run (m, log) =
      (fun post => (post.1, (value.2, (snap, (post.2, log))))) <$>
        (simulateQ (PqxdhDeploymentLater.postImpl setup codec checks created.seed)
          (second value.1 (PqxdhDeploymentLater.revealOf
            (merge copies (PqxdhRegistrationJointSchedule.source m.joint)).native.owners snap,
            (some created.seed, log)))).run (merge copies (PqxdhRegistrationJointSchedule.source m.joint)) := by
  obtain ⟨m₁, source₁, seeds₁, -, -, run₁⟩ := terminal_mid setup codec route checks t p created snap
    (List.range copies.log.owners.length) m log
  have slot₁ : m₁.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed := by
    rw [seeds₁]
    exact slot
  have reveal : (List.range copies.log.owners.length).filterMap
      (PqxdhDeploymentLater.revealAt (PqxdhRegistrationJointSchedule.source m.joint).owners snap) =
      PqxdhDeploymentLater.revealOf (merge copies (PqxdhRegistrationJointSchedule.source m.joint)).native.owners snap := by
    rw [PqxdhDeploymentLaterCompile.reveal_merge, good.count]
    rfl
  let m₂ : Mid KemSK := ⟨{ m₁.joint with
    pool := (PqxdhDynamicIdentityPool.record (.inr (.reveal created.server.server.metadata.identityIndex))
      (some created.seed) m₁.joint.pool.1, m₁.joint.pool.2) }, m₁.backend, m₁.seeds⟩
  have source₂ : PqxdhRegistrationJointSchedule.source m₂.joint = PqxdhRegistrationJointSchedule.source m.joint :=
    source₁
  have good₂ : Good setup codec copies (PqxdhRegistrationJointSchedule.source m₂.joint) := by
    rw [source₂]
    exact good
  have post := post_mid setup codec route checks t p created phase1 phase2
    (second value.1 (PqxdhDeploymentLater.revealOf
      (merge copies (PqxdhRegistrationJointSchedule.source m.joint)).native.owners snap, (some created.seed, log)))
    copies m₂ log good₂
  have mapped := congrArg (fun work => (fun x : Out × (PqxdhDeploymentNative.State KemSK × IdealBk TableState × Log) =>
    (x.1, (value.2, (snap, (x.2.1, x.2.2.2))))) <$> work) post
  simp only [Functor.map_map] at mapped
  unfold PqxdhDeploymentIdealLaterCut.restOf
  simp only [simulateQ_bind, StateT.run_bind, sourceMidL_embed, run₁, pure_bind, simulateQ_spec_query,
    serverRead_mid, slot₁, reveal, simulateQ_pure, StateT.run_pure, map_bind, map_pure]
  rw [bind_pure_comp]
  refine (Eq.trans ?_ mapped).trans ?_
  · rfl
  · rw [source₂]

/-- The CE side after the run part on the merge image: for a decision on the LQ-F outcome and the mark, the real post phase from the merge image of a logged middle state (`PqxdhDeploymentFinishErasure.laterTail`) is the rest of the compiled LQ-F program under the logged middle source handler, read off through the merge image, with the mark of the middle state. -/
theorem laterTail_middle {A X Out : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (value : X × PqxdhDeploymentSecrecy.Ledger) (snap : Snap) (copies : Local) (m : Mid KemSK) (log : Log)
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (slot : m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) :
    (fun outcome => decision (PqxdhDeploymentIdealLaterGame.laterOf outcome)
        (PqxdhDeploymentIdealLaterCut.markedL outcome)) <$>
        PqxdhDeploymentFinishErasure.laterTail (PqxdhDeploymentFinishErasure.realPost setup codec checks) created second
          id after (value, mergeXL ((snap, copies), (m, log))) =
      (fun result => decision (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, (result.1.2.1,
          (result.1.2.2.1, (merge result.1.2.2.2 (PqxdhRegistrationJointSchedule.source result.2.1.joint),
            result.2.2)))), after) m.backend.2.2.marks.isSome) <$>
        (simulateQ (sourceMidL setup codec route checks t p created)
          (PqxdhDeploymentIdealLaterCut.restOf setup codec route second (value, (snap, copies)))).run (m, log) := by
  have rest := restOf_middle setup codec route checks t p created phase1 phase2 second value snap copies m log good slot
  have mapped := congrArg (fun work => (fun result : Out × (PqxdhDeploymentSecrecy.Ledger × (Snap ×
    (PqxdhDeploymentNative.State KemSK × Log))) => decision (some (PqxdhRegistrationJointServerBirth.encode created,
      result.1, result.2), after) m.backend.2.2.marks.isSome) <$> work) rest
  simp only [Functor.map_map] at mapped
  rw [mapped]
  unfold PqxdhDeploymentFinishErasure.laterTail
  rw [PqxdhDeploymentIdealLaterCut.realPost_run, map_bind, bind_map_left]
  simp only [← bind_pure_comp]
  rfl

end Rest

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceMidL_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceMidL_embed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceMidL_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceMidL_inl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceMidS_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceMidS_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.preRead_mid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.preRead_mid

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.unghost_mergeXL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.unghost_mergeXL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.realRegAt_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.realRegAt_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.onBase_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.onBase_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.onSlots_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.onSlots_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.slotCore_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.slotCore_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.idealProg_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.idealProg_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.idealStep_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.idealStep_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.handler_acceptOther' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.handler_acceptOther

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compiledMidL_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compiledMidL_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.acceptSource_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.acceptSource_source

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compiledMidL_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compiledMidL_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.step_mergeMidL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.step_mergeMidL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.goodMidL_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.goodMidL_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compile_simulationMidL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compile_simulationMidL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.compiled_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceStep_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.sourceStep_field

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.read_mid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.read_mid

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.terminal_mid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.terminal_mid

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.serverRead_mid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.serverRead_mid

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.post_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.post_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.post_mid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.post_mid

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.restOf_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.restOf_middle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.laterTail_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid.laterTail_middle
