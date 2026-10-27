-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPool

/-! LQ-F upstream, unit B1: the cut of both sides of the later second compile lemma at the selected raw accept, pointwise in the challenger's draws (the logged counterpart of CE-11b unit U5's `PqxdhDeploymentIdealCut`).

- Item 2's logged scan of the compiled LQ-F program. The logged scan passes every request but a raw accept (`scanL_query_other`, `scanL_accept_succ`), completes on a program without raw accept (`scanL_quiet`), splits over a continuation without raw accept (`scanL_bind_quiet`) and is the embedded source14 scan on an embedded program (`scanL_embed`, `cutEmbed`). The source14 scan of a program compiled with the finish snapshot is the compiled CE scan (`compile_scanSnap`, `compileCutSnap`: `PqxdhDeploymentIdealCut.compile_scan` for `compileSnapImpl`). The compiled LQ-F program is its embedded run part followed by the rest (`runPart`, `restOf`, `compileServer_split`; the terminal reads, the Server read and the post part issue no raw accept, `restOf_quiet`), so its logged scan is the embedded compiled CE scan of the wrapped run-phase adversary followed by `scanRest` (`compile_scanServer`): a completed run part runs the rest, a pending cut appends the rest to its continuation.
- The CE side. `cutStateL` is the canonical extended state at the cut with the LQ-F ghosts of an LQ-F view (snapshot, deployment state, log), `markedL` whether the selected session is marked at the end, and `resumeL` the later ideal game resumed from it, followed by the real post phase, for a decision on the LQ-F outcome and the mark. The real post phase reads the state only through its LQ-F view and its mark (`realPost_run`, `laterTail_view`). `ideal_cutL`: the ideal run followed by the post phase is the scan's run by the logged snapshot handler with the pool create, then `resumeL` (the ghosts at the cut are the scan's, `PqxdhDeploymentIdealLaterPool.preScanL`; at a pending cut the state is exactly `cutStateL` of its view). `commonPrefixL` is the logged annotated pool source execution of the compiled scan; `pool_scan_sourceL` writes the scan's run as its merge and erasure image (`compile_simulation_poolL`, `programPool_nativeL`), and `ideal_prefixL` writes the later ideal game at the draws as the annotated Server birth, `commonPrefixL` and `resumeL` on the merged state with the ghosts of the prefix.
- Item 2's side. `opaqueRestL` is the rest of item 2's logged opaque scan after its logged commands (`opaqueScan_splitL`), `stopped_scan_sourceL` the stopped router over the logged commands of an embedded source14 program as the image of its logged annotated pool source execution (`PqxdhDeploymentIdealLaterPool.kemCommands_stoppedL`), `opaqueAfterL` the rest of the logged opaque scan after the common prefix (the logged commands of `scanRest`, then `opaqueRestL`) under the stopped router, and `item2_prefixL` writes item 2's logged prephase at the draws for the compiled LQ-F program as the same Server birth, `commonPrefixL` and `opaqueAfterL`.
- Facts at the cut. Forgetting the log gives item 2's annotated pool source execution (`programPool_projectionL`, `prefix_projectionL`). On every outcome of `commonPrefixL`: the source-side invariant at the pool and the owner positions (`cut_ownedL`), CE-3's merge invariant (`cut_goodL`), a prefix KEM pool within the creations (`cut_prefixL`) and the remaining creations of the compiled continuation (`cut_residualL`); together with owner `j` holding pool entry `j` they form `CutRelL` (`cut_relL`).

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` (through the logged pool compile lemma) and, on item 2's side and for the facts, budgets of the compiled run part, which the CE budget discharges. A budget of the whole compiled LQ-F program is not used: the rest after the run part runs inside the prefix only when the selected accept is never reached, where item 2's side accepts nothing. These are program equalities and support facts. They charge nothing and make no security claim. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhLiveKemReservation (Pair)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl logReply)
open PqxdhDeploymentLater (Snap finishOwner PostSpec postEmbed)
open PqxdhDeploymentLaterCompile (compileSnapImpl preRead terminal)
open PqxdhDeploymentLaterServerSource (Log embed)
open PqxdhDeploymentLaterServerReserve (laterKind)
open PqxdhDeploymentIdealCut (CutCE scanCE finishCE)
open PqxdhRegistrationJointRevealCosts (sourceKind)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-! ### The logged scan of the compiled LQ-F program -/

section Scan

/-- The logged scan passes a request other than a raw accept. -/
theorem scanL_query_other {β : Type} (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain)
    (other : laterKind (KemSK := KemSK) query ≠ some (.inl 3))
    (next : (PqxdhDeploymentLaterServerSource.Spec KemSK).Range query →
      OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) β) (index : ℕ) :
    PqxdhDeploymentLaterServerCommands.scan (((PqxdhDeploymentLaterServerSource.Spec KemSK).query query :
        OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _) >>= next) index =
      ((PqxdhDeploymentLaterServerSource.Spec KemSK).query query :
        OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _) >>= fun answer =>
          PqxdhDeploymentLaterServerCommands.scan (next answer) index := by
  rcases query with ((coin | request) | read) | later
  · rfl
  · cases request with
    | accept raw => exact absurd rfl other
    | _ => rfl
  · rfl
  · rfl

/-- The logged scan of a program without a raw accept completes with the program's result. -/
theorem scanL_quiet {β : Type} (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) β)
    (quiet : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inl 3)) 0) (index : ℕ) :
    PqxdhDeploymentLaterServerCommands.scan work index = PqxdhDeploymentLaterServerCommands.Cut.complete <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have other : laterKind (KemSK := KemSK) query ≠ some (.inl 3) := by
        intro accept
        rcases quiet.1 with absent | impossible
        · exact absent accept
        · exact absurd impossible (Nat.lt_irrefl 0)
      rw [scanL_query_other query other, map_bind]
      refine bind_congr fun answer => ih answer ?_
      simpa only [other, ↓reduceIte] using quiet.2 answer

/-- The logged scan stops at the raw accept of position zero and issues a raw accept before the cut position. -/
theorem scanL_accept_succ {β : Type} (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) β) (index : ℕ) :
    PqxdhDeploymentLaterServerCommands.scan (((PqxdhDeploymentLaterServerSource.Spec KemSK).query
        (.inl (.inl (.inr (.accept raw)))) : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _) >>= next)
        (index + 1) =
      ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl (.inl (.inr (.accept raw)))) :
        OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _) >>= fun answer =>
          PqxdhDeploymentLaterServerCommands.scan (next answer) index := rfl

/-- The logged scan of a program followed by a continuation without a raw accept: the scan of the program, then on completion the continuation's run, and at a pending cut the continuation appended to the saved one. -/
theorem scanL_bind_quiet {α β : Type} (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) α)
    (rest : α → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) β)
    (quiet : ∀ value, (rest value).IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some (.inl 3)) 0)
    (index : ℕ) :
    PqxdhDeploymentLaterServerCommands.scan (work >>= rest) index =
      PqxdhDeploymentLaterServerCommands.scan work index >>= fun cut => match cut with
        | .complete value => PqxdhDeploymentLaterServerCommands.Cut.complete <$> rest value
        | .pending raw next => pure (.pending raw fun answer => next answer >>= rest) := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure value =>
      rw [pure_bind, scanL_quiet (rest value) (quiet value)]
      rfl
  | query_bind query next ih =>
      by_cases accept : laterKind (KemSK := KemSK) query = some (.inl 3)
      · rcases query with ((coin | request) | read) | later
        · exact absurd accept (by simp [laterKind, sourceKind, PqxdhRegistrationSchedule.sourceKind])
        · cases request with
          | accept raw =>
              cases index with
              | zero => rfl
              | succ index =>
                  rw [bind_assoc, scanL_accept_succ, scanL_accept_succ, bind_assoc]
                  exact bind_congr fun answer => ih answer index
          | _ => exact absurd accept (by simp [laterKind, sourceKind, PqxdhRegistrationSchedule.sourceKind])
        · exact absurd accept (by simp [laterKind, sourceKind])
        · exact absurd accept (by simp [laterKind])
      · rw [bind_assoc, scanL_query_other query accept, scanL_query_other query accept, bind_assoc]
        exact bind_congr fun answer => ih answer index

/-- The logged form of a source14 cut. -/
noncomputable def cutEmbed {R : Type} :
    PqxdhRegistrationJointAcceptCut.Cut KemSK R → PqxdhDeploymentLaterServerCommands.Cut KemSK R
  | .complete result => .complete result
  | .pending raw next => .pending raw fun answer => simulateQ embed (next answer)

/-- The logged scan of an embedded source14 program is the embedded source14 scan. -/
theorem scanL_embed {R : Type} (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) R)
    (index : ℕ) :
    PqxdhDeploymentLaterServerCommands.scan (simulateQ embed program) index =
      cutEmbed <$> simulateQ embed (PqxdhRegistrationJointAcceptCut.scan program index) := by
  induction program using OracleComp.inductionOn generalizing index with
  | pure value => rfl
  | query_bind query next ih =>
      have embedded : simulateQ embed (((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query :
          OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= next) =
          ((PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inl query) :
            OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) _) >>= fun answer => simulateQ embed (next answer) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      by_cases accept : sourceKind (KemSK := KemSK) query = .inl 3
      · obtain ⟨raw, rfl⟩ := PqxdhDeploymentLaterServerNative.kind_accept query accept
        cases index with
        | zero => rfl
        | succ index =>
            have scanned : PqxdhRegistrationJointAcceptCut.scan (((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query
                (.inl (.inr (.accept raw))) : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= next)
                (index + 1) =
                ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) :
                  OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) >>= fun answer =>
                    PqxdhRegistrationJointAcceptCut.scan (next answer) index := rfl
            rw [embedded, scanL_accept_succ, scanned, simulateQ_bind, simulateQ_spec_query, map_bind]
            exact bind_congr fun answer => ih answer index
      · rw [embedded, scanL_query_other (.inl query) (by simpa [laterKind] using accept),
          PqxdhDeploymentIdealCut.scan_query_other query accept, simulateQ_bind, simulateQ_spec_query, map_bind]
        exact bind_congr fun answer => ih answer index

end Scan

section CompileScan
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The compiled form of a CE cut with the finish snapshot: a completed program with its snapshot and local copies, or the raw bytes of the suspended accept with the compiled continuation, which logs the accept's reply first (as `compileImpl` does); `PqxdhDeploymentIdealCut.compileCut` for `compileSnapImpl`. -/
noncomputable def compileCutSnap : CutCE X × (Snap × Local) → PqxdhRegistrationJointAcceptCut.Cut KemSK (X × (Snap × Local))
  | (.complete result, state) => .complete (result, state)
  | (.pending raw next, (snap, copies)) => .pending raw fun answer =>
      (simulateQ (compileSnapImpl setup codec route) (next answer)).run
        (snap, { copies with log := logReply copies.log (.accept raw) answer })

/-- The source14 accept scan of a program compiled with the finish snapshot is the compiled CE scan at the same position (`PqxdhDeploymentIdealCut.compile_scan` for `compileSnapImpl`: the finish pre-reads are field reads, not raw accepts). -/
theorem compile_scanSnap (work : OracleComp Spec X) (index : ℕ) (state : Snap × Local) :
    PqxdhRegistrationJointAcceptCut.scan ((simulateQ (compileSnapImpl setup codec route) work).run state) index =
      compileCutSnap setup codec route <$> (simulateQ (compileSnapImpl setup codec route) (scanCE work index)).run
        state := by
  induction work using OracleComp.inductionOn generalizing index state with
  | pure result => rfl
  | query_bind query next ih =>
    by_cases accept : ∃ raw, query = .inr (.accept raw)
    · obtain ⟨raw, rfl⟩ := accept
      cases index with
      | zero => rfl
      | succ index =>
          obtain ⟨snap, copies⟩ := state
          have scanned : scanCE ((Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= next) (index + 1) =
              (Spec.query (.inr (.accept raw)) : OracleComp Spec _) >>= fun answer => scanCE (next answer) index :=
            rfl
          rw [scanned, simulateQ_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_bind,
            map_bind]
          simp only [compileSnapImpl, finishOwner, preRead, compileImpl, PqxdhDeploymentCompile.forwardLogged,
            PqxdhDeploymentCompile.forward, StateT.run, bind_assoc, pure_bind, id]
          change ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query (.inl (.inr (.accept raw))) >>= fun answer =>
            PqxdhRegistrationJointAcceptCut.scan ((simulateQ (compileSnapImpl setup codec route) (next answer)).run
              (snap, { copies with log := logReply copies.log (.accept raw) answer })) index :
            OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) _) = _
          exact bind_congr fun answer => ih answer index _
    · have notAccept : ∀ raw, query ≠ .inr (.accept raw) := fun raw same => accept ⟨raw, same⟩
      have other : PqxdhDeploymentCompileBudget.commandKind query ≠ 3 := by
        rcases query with coin | command
        · simp [PqxdhDeploymentCompileBudget.commandKind]
        · cases command with
          | accept raw => exact absurd rfl (notAccept raw)
          | _ => simp [PqxdhDeploymentCompileBudget.commandKind]
      have shape : (simulateQ (compileSnapImpl setup codec route) ((Spec.query query : OracleComp Spec _) >>= next)).run
          state = (compileSnapImpl setup codec route query).run state >>= fun reached =>
            (simulateQ (compileSnapImpl setup codec route) (next reached.1)).run reached.2 := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [shape, PqxdhDeploymentIdealCut.scan_bind_noAccept _
          (PqxdhDeploymentLaterServerCompile.snap_quiet setup codec route query notAccept state),
        PqxdhDeploymentIdealCut.scanCE_other query other, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        map_bind]
      exact bind_congr fun reached => ih reached.1 index reached.2

end CompileScan

section Server
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentSecrecy (Ledger wrap)
variable {Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The run part of the compiled LQ-F program: the CE-3 compiler with the finish pre-read on the wrapped run-phase adversary, from the empty snapshot and local state. -/
noncomputable def runPart (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X) :
    OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) ((X × Ledger) × (Snap × Local)) :=
  (simulateQ (compileSnapImpl setup codec route)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run (Snap.empty, Local.empty)

/-- The rest of the compiled LQ-F program after its run part: the terminal reads, the Server read and the post part. -/
noncomputable def restOf (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (run : (X × Ledger) × (Snap × Local)) :
    OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) (Out × (Ledger × (Snap × Local))) := do
  let beacons ← simulateQ embed (terminal run.2.1 (List.range run.2.2.log.owners.length))
  let server ← (PqxdhDeploymentLaterServerSource.Spec KemSK).query (.inr ())
  let post ← simulateQ embed ((simulateQ (compileImpl setup codec route)
    (simulateQ postEmbed (second run.1.1 (beacons, server)))).run run.2.2)
  pure (post.1, (run.1.2, (run.2.1, post.2)))

/-- The compiled LQ-F program is its embedded run part followed by the rest. -/
theorem compileServer_split (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second =
      simulateQ embed (runPart setup codec route bounds mode first) >>= restOf setup codec route second := rfl

/-- The rest of the compiled LQ-F program issues no raw accept (`PqxdhDeploymentLaterServerCompile.terminal_quiet`, `post_quiet`; the Server read has no source kind). -/
theorem restOf_quiet (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (run : (X × Ledger) × (Snap × Local)) :
    (restOf setup codec route second run).IsQueryBoundP
      (fun query => laterKind (KemSK := KemSK) query = some (.inl 3)) 0 := by
  refine isQueryBoundP_bind (n := 0) (m := 0) (PqxdhDeploymentLaterServerCompileBudget.embed_bound _ _ 0
    (PqxdhDeploymentLaterServerCompile.terminal_quiet _ _)) fun beacons _ => ?_
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ fun server _ => ?_
  · rw [isQueryBoundP_query_iff]
    intro hit
    simp [laterKind] at hit
  · refine isQueryBoundP_bind (n := 0) (m := 0) (PqxdhDeploymentLaterServerCompileBudget.embed_bound _ _ 0
      (PqxdhDeploymentLaterServerCompile.post_quiet setup codec route _ _)) fun post _ => ?_
    trivial

/-- The continuation of the logged scan of the compiled LQ-F program after the scan of its run part: a completed run part runs the rest and completes, a pending cut appends the rest to its saved continuation. -/
noncomputable def scanRest (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    PqxdhRegistrationJointAcceptCut.Cut KemSK ((X × Ledger) × (Snap × Local)) →
      OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK)
        (PqxdhDeploymentLaterServerCommands.Cut KemSK (Out × (Ledger × (Snap × Local))))
  | .complete run => PqxdhDeploymentLaterServerCommands.Cut.complete <$> restOf setup codec route second run
  | .pending raw next => pure (.pending raw fun answer =>
      simulateQ embed (next answer) >>= restOf setup codec route second)

/-- The logged scan of the compiled LQ-F program at a raw-accept ordinal: the embedded compiled CE scan of the wrapped run-phase adversary (`compile_scanSnap`), then `scanRest`. -/
theorem compile_scanServer (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (index : ℕ) :
    PqxdhDeploymentLaterServerCommands.scan
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) index =
      simulateQ embed (compileCutSnap setup codec route <$> (simulateQ (compileSnapImpl setup codec route)
          (scanCE (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) index)).run
            (Snap.empty, Local.empty)) >>= scanRest setup codec route second := by
  rw [compileServer_split, scanL_bind_quiet _ _ (restOf_quiet setup codec route second), scanL_embed, runPart,
    compile_scanSnap, bind_map_left]
  refine bind_congr fun cut => ?_
  cases cut <;> rfl

end Server

/-! ### The CE side: the later ideal game cut at the selected accept -/

section CE
open PqxdhDeploymentBackend (XState handlerWith xinitial laterView)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentFinishErasure (laterTail realPost xreveal)
open PqxdhDeploymentIdealLaterGame (laterOf)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentIdealLaterPool (snapPoolL)
variable {A Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The canonical extended state at the cut for an LQ-F view (snapshot, deployment state, log): the ideal backend right before the selected accept (`PqxdhDeploymentIdealCut.cutState`), no seed, and the LQ-F ghosts of the view. -/
def cutStateL (view : Snap × (PqxdhDeploymentNative.State KemSK × Log)) : XState KemSK (IdealBk TableState) 2 :=
  ⟨view.2.1, PqxdhDeploymentIdealCut.withAccepts (idealInit created) t.accept, ∅, view.1, view.2.2⟩

/-- Whether the selected session is marked at the end of a later-game outcome. -/
def markedL (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × Ledger ×
    XState KemSK (IdealBk TableState) 2) × A) : Bool :=
  match outcome.1 with
  | some result => result.2.2.2.backend.2.2.marks.isSome
  | none => false

/-- The later ideal game after the cut, for a decision that reads the LQ-F outcome and whether the selected session is marked: from the canonical state at the cut for the view, resume the cut with the ideal registration, then the real post phase. -/
noncomputable def resumeL (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (cut : CutCE (X × Ledger)) (view : Snap × (PqxdhDeploymentNative.State KemSK × Log)) : ProbComp Bool :=
  (fun outcome => decision (laterOf outcome) (markedL outcome)) <$>
    ((simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) (finishCE cut)).run
      (cutStateL t created view) >>= laterTail (realPost setup codec checks) created second id after)

/-- The real post phase runs the native post handler on the deployment state and keeps the rest of the extended state. -/
theorem realPost_run {Bk : Type} {n : ℕ} {α : Type} (work : OracleComp PostSpec α) (x : XState KemSK Bk n) :
    (simulateQ (realPost (Bk := Bk) (n := n) setup codec checks created) work).run x =
      (fun result => (result.1, { x with base := result.2 })) <$>
        (simulateQ (PqxdhDeploymentLater.postImpl setup codec checks created.seed) work).run x.base :=
  PqxdhDeploymentFinishErasure.simulateQ_lift PqxdhDeploymentBackend.baseLens
    (PqxdhDeploymentLater.postImpl setup codec checks created.seed) work x

/-- A decision on the LQ-F outcome and the mark after the real post phase reads the state at the start of the post phase only through its LQ-F view and its mark. -/
theorem laterTail_view (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (value : X × Ledger) (x y : XState KemSK (IdealBk TableState) 2) (viewed : laterView x = laterView y)
    (marks : x.backend.2.2.marks = y.backend.2.2.marks) :
    (fun outcome => decision (laterOf outcome) (markedL outcome)) <$>
        laterTail (realPost setup codec checks) created second id after (value, x) =
      (fun outcome => decision (laterOf outcome) (markedL outcome)) <$>
        laterTail (realPost setup codec checks) created second id after (value, y) := by
  have snap : x.snap = y.snap := congrArg Prod.fst viewed
  have base : x.base = y.base := congrArg (fun view => view.2.1) viewed
  have log : x.log = y.log := congrArg (fun view => view.2.2) viewed
  have reveal : xreveal created x = xreveal created y := by
    simp only [xreveal, snap, base, log]
  simp only [laterTail, map_bind]
  rw [realPost_run, realPost_run, reveal, base, bind_map_left, bind_map_left]
  refine bind_congr fun post => ?_
  simp only [map_pure, laterOf, markedL, Option.map_some, laterView, snap, log, id_eq, marks]

/-- The later ideal game's run and post phase cut at the selected accept (CE side of the later prefix): for every decision on the LQ-F outcome and the mark, the run of a deployment program by the handler with the ideal registration from the initial state, followed by the real post phase, is the run of the program's scan up to the selected accept by the logged snapshot handler with the pool create, followed by `resumeL` (the LQ-F ghosts at the cut are those of the scan; `PqxdhDeploymentIdealLaterPool.preScanL`). -/
theorem ideal_cutL (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool)
    (work : OracleComp Spec (X × Ledger))
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A) :
    (fun outcome => decision (laterOf outcome) (markedL outcome)) <$>
        ((simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) work).run
          (xinitial created (idealInit created)) >>= laterTail (realPost setup codec checks) created second id after) =
      (simulateQ (snapPoolL setup codec checks route created.seed (p.pool t)) (scanCE work t.accept)).run
          (Snap.empty, (PqxdhDeploymentNative.initial created, [])) >>= fun reached =>
        resumeL setup codec route checks t p created decision second after reached.1 reached.2 := by
  have pre : PqxdhDeploymentIdealCut.PreCut (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)) :=
    ⟨rfl, rfl⟩
  have room : (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)).backend.2.2.accepts + t.accept ≤
      t.accept := by
    simp [xinitial, idealInit, PqxdhDeploymentIdealSteps.IdealCore.initial]
  have facts := (PqxdhDeploymentIdealCut.preScan setup codec route checks t p created work t.accept _ pre room).2
  have viewed := PqxdhDeploymentIdealLaterPool.preScanL setup codec route checks t p created work t.accept _ pre room
  rw [PqxdhDeploymentIdealCut.run_scanCE _ work t.accept, bind_assoc, map_bind]
  rw [show ((Snap.empty, (PqxdhDeploymentNative.initial created, [])) :
      Snap × (PqxdhDeploymentNative.State KemSK × Log)) =
        laterView (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)) from rfl, ← viewed,
    bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun reached member => ?_
  obtain ⟨accepts, backend, seeds, pending⟩ := facts reached member
  unfold resumeL
  rw [map_bind]
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  rcases cut : reached.1 with result | ⟨raw, next⟩
  · simp only [finishCE, simulateQ_pure, StateT.run_pure, pure_bind]
    refine laterTail_view setup codec checks created decision second after result reached.2 _ rfl ?_
    rw [backend]
    rfl
  · have counted := pending raw next cut
    have same : reached.2 = cutStateL t created (laterView reached.2) := by
      have : reached.2 = ⟨reached.2.base, reached.2.backend, reached.2.seeds, reached.2.snap, reached.2.log⟩ := rfl
      rw [this]
      simp only [cutStateL, laterView, backend, seeds, counted]
      simp [xinitial, idealInit, PqxdhDeploymentIdealSteps.IdealCore.initial]
    rw [same, map_bind]
    rfl

end CE

/-! ### The common prefix of both sides -/

section Prefix
open PqxdhDeploymentIdealSteps (idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentFinishErasure (laterWith realPost)
open PqxdhDeploymentIdealLaterGame (laterOf)
open PqxdhDeploymentSecrecy (wrap)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentIdealLaterPool (snapPoolL sourcePoolL nativePoolL compiledPoolL)
variable {A Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The common prefix of both sides of the later second compile lemma at the pool: the logged annotated pool source execution of the CE scan compiled with the finish snapshot, up to the selected raw accept, from the constructed Server's initial annotated source state with the private pools after its construction and the empty log. -/
noncomputable def commonPrefixL {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (work : OracleComp Spec Y) :
    ProbComp ((CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log)) :=
  (simulateQ (sourcePoolL setup codec checks created.seed created.server.server.metadata.identityIndex (p.pool t))
    ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run (Snap.empty, Local.empty))).run
      (PqxdhDeploymentIdealCut.sourceInit created pool, [])

/-- The logged pool scan on the deployment side is an image of the logged annotated pool source execution of the compiled scan (`compile_simulation_poolL`, then the erasure `programPool_nativeL`), under the approved codec contracts and for a Server constructed with the experiment's key ID and no peer. -/
theorem pool_scan_sourceL {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (identityIndex : ℕ)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (work : OracleComp Spec Y) (index : ℕ) :
    (simulateQ (snapPoolL setup codec checks route created.seed (p.pool t)) (scanCE work index)).run
        (Snap.empty, (PqxdhDeploymentNative.initial created, [])) =
      (fun result => (result.1.1, (result.1.2.1, (merge result.1.2.2 (PqxdhRegistrationJointSchedule.source result.2.1),
          result.2.2)))) <$>
        (simulateQ (sourcePoolL setup codec checks created.seed identityIndex (p.pool t))
          ((simulateQ (compileSnapImpl setup codec route) (scanCE work index)).run (Snap.empty, Local.empty))).run
            (PqxdhDeploymentIdealCut.sourceInit created pool, []) := by
  have good := PqxdhDeploymentCompileInvariant.good_initial setup codec (PqxdhRegistrationSchedule.initial created) sender
    peers rfl (fun _ => rfl)
  have simulated := PqxdhDeploymentIdealLaterPool.compile_simulation_poolL setup codec checks route created.seed
    (p.pool t) phase1 phase2 (scanCE work index) Snap.empty Local.empty (PqxdhRegistrationSchedule.initial created) []
    good
  rw [PqxdhDeploymentCompile.merge_empty] at simulated
  change _ = _ <$> (simulateQ (sourcePoolL setup codec checks created.seed identityIndex (p.pool t)) _).run
    (PqxdhDeploymentIdealCut.sourceInit created pool, [])
  rw [show PqxdhDeploymentNative.initial created =
      (⟨PqxdhRegistrationSchedule.initial created, 0, fun _ => 0, []⟩ : PqxdhDeploymentNative.State KemSK) from rfl,
    ← simulated]
  have flat := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (nativePoolL setup codec checks created.seed (p.pool t)) (compileSnapImpl setup codec route) (scanCE work index)
    (Snap.empty, Local.empty) (PqxdhRegistrationSchedule.initial created, [])
  have erased := PqxdhDeploymentIdealLaterPool.programPool_nativeL setup codec checks created.seed identityIndex
    (p.pool t) ((simulateQ (compileSnapImpl setup codec route) (scanCE work index)).run (Snap.empty, Local.empty))
    (PqxdhDeploymentIdealCut.sourceInit created pool) []
  rw [show PqxdhRegistrationJointSchedule.source (PqxdhDeploymentIdealCut.sourceInit created pool) =
    PqxdhRegistrationSchedule.initial created from rfl, flat] at erased
  have back := congrArg (fun work => (fun z => (z.1.1, (z.1.2, z.2))) <$> work) erased
  simp only [Functor.map_map] at back
  change (fun result => (result.1, (result.2.1.1, (merge result.2.1.2 result.2.2.1, result.2.2.2)))) <$>
      (simulateQ (compiledPoolL setup codec checks route created.seed (p.pool t)) (scanCE work index)).run
        ((Snap.empty, Local.empty), (PqxdhRegistrationSchedule.initial created, [])) = _
  have eta : (simulateQ (compiledPoolL setup codec checks route created.seed (p.pool t)) (scanCE work index)).run
      ((Snap.empty, Local.empty), (PqxdhRegistrationSchedule.initial created, [])) =
      (fun a => (a.1.1, (a.1.2, (PqxdhRegistrationJointSchedule.source a.2.1, a.2.2)))) <$>
        (simulateQ (sourcePoolL setup codec checks created.seed identityIndex (p.pool t))
          ((simulateQ (compileSnapImpl setup codec route) (scanCE work index)).run (Snap.empty, Local.empty))).run
            (PqxdhDeploymentIdealCut.sourceInit created pool, []) := by
    rw [back]
    simp only [Prod.mk.eta]
    exact (id_map _).symm
  rw [eta, Functor.map_map]

/-- The prefix of the later ideal game at the challenger's draws (CE side): for every decision on the LQ-F outcome and the mark, the later game with the ideal registration at the draws, the real post phase, identity index 0, is the Server construction (as item 2's annotated birth, which also installs the Server's seed in the joint identity pool), then the common prefix (`commonPrefixL`), then the later ideal game resumed from the canonical state at the cut with the ghosts of the prefix (`resumeL`) on the merged deployment state. Premises: the approved codec contracts. -/
theorem ideal_prefixL (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool) :
    (fun outcome => decision (laterOf outcome) (PqxdhDeploymentIdealLaterCut.markedL outcome)) <$>
        (laterWith setup codec route idealInit (idealReg setup codec route checks t p) (realPost setup codec checks)
          ensureInit 0 bounds mode first second).run runtime =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => pure (decision (none, born.2.2) false)
        | some created =>
            commonPrefixL setup codec route checks t p created born.2.1
                (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) >>= fun reached =>
              resumeL setup codec route checks t p created decision second born.2.2 reached.1.1
                (reached.1.2.1, (merge reached.1.2.2 (PqxdhRegistrationJointSchedule.source reached.2.1), reached.2.2)) := by
  rw [PqxdhDeploymentIdealLaterGame.laterWith_split]
  simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, map_bind, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun born member => ?_
  rcases born with ⟨_ | created, after⟩
  · simp [laterOf, PqxdhDeploymentIdealLaterCut.markedL]
  · obtain ⟨sender, peers⟩ := PqxdhDeploymentCompileGame.construct_fields setup.joint ensureInit 0 setup.serverKeyId
      runtime created after member
    dsimp only
    have cut := ideal_cutL setup codec route checks t p created decision
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) second after
    rw [pool_scan_sourceL setup codec route checks t p created phase1 phase2 sender peers
        created.server.server.metadata.identityIndex
        (PqxdhRegistrationJointServerBirth.install created (PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty)),
      bind_map_left] at cut
    simp only [StateT.run] at cut
    exact cut

end Prefix

/-! ### Item 2's side: the logged prephase cut at the selected accept -/

section Item2
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentSecrecy (Ledger wrap)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentIdealLaterPool (sourcePoolL)
open PqxdhDeploymentLaterServerOpaque (OpaqueCut rejectRun)
open PqxdhRegistrationJointGeneratedFinish (encodeState)
variable {A Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- The rest of item 2's logged opaque scan after its logged command prefix (`PqxdhDeploymentLaterServerOpaque.opaqueScan` after the scanned logged commands): a completed prefix completes; at the selected raw accept, a rejected attached verification or a rejection before encapsulation completes the run with the logged entry, and otherwise the source parameters of the active cut are saved. -/
noncomputable def opaqueRestL {Z R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : Z × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (reached : (PqxdhDeploymentLaterServerCommands.Cut KemSK Z × PqxdhDeploymentLaterServerCommands.Local) ×
      PqxdhServerAuthNative.NativeState KemSK) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (OpaqueCut Reader KemSK Z R) :=
  match reached.1.1 with
  | .complete result => pure (.complete ((observe (result, none), reached.1.2.1), reached.2))
  | .pending raw next =>
    match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
    | none =>
      rejectRun setup codec checks identityIndex publicIdentity observe raw next reached.1.2.1 reached.1.2.2 reached.2
        (none, reached.2.2.server.consumed) none
    | some value => do
      let prepared ← simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
          (PqxdhDeploymentLaterServerSource.beforeLogged value)).run reached.2.2.server.consumed)
      match prepared.1.1 with
      | none =>
        rejectRun setup codec checks identityIndex publicIdentity observe raw next reached.1.2.1 reached.1.2.2 reached.2
          (none, prepared.2) prepared.1.2
      | some ephemeral =>
        pure (.pending raw value ephemeral prepared.2 reached.2 reached.1.2.1 reached.1.2.2 next)

/-- Item 2's logged opaque scan is its logged command prefix followed by `opaqueRestL`. -/
theorem opaqueScan_splitL {Z R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : Z × PqxdhRegistrationJointAcceptCutTag.Tag → R)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Z) (index : ℕ)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (log : Log)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhDeploymentLaterServerOpaque.opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity
        observe work index owners log state =
      simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
            (PqxdhDeploymentLaterServerCommands.scan work index) owners log state) >>=
        opaqueRestL setup codec checks identityIndex publicIdentity observe := rfl

/-- The prefix of item 2's logged opaque scan of an embedded source14 program, under the stopped selected-first router at the pool from the constructed Server's initial state, is an image of its logged annotated pool source execution (`PqxdhDeploymentIdealLaterPool.kemCommands_stoppedL`). The premises are a budget of the program that reads no identity or KEM field and creates no more KEM keys than the pool holds, the Server's identity slot in the joint pool and an empty KEM pool. -/
theorem stopped_scan_sourceL {Result : Type} (created : PqxdhLiveServerConstruction.Created Unit) (identityIndex : ℕ)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[identityIndex]? = some created.seed)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex (setup.joint.publicKeys created.seed)
            (simulateQ embed program) [] [] (PqxdhRegistrationSchedule.initial created).shared))).run).run
        (pool.1, PqxdhDynamicKemRouter.empty) =
      (fun result => (some ((result.1, ((encodeState setup result.2.1).owners, result.2.2)), result.2.1.shared),
          (result.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.1.pool.2))) <$>
        (simulateQ (sourcePoolL setup codec checks created.seed identityIndex (p.pool t)) program).run
          (PqxdhDeploymentIdealCut.sourceInit created pool, []) := by
  have owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed identityIndex
      (PqxdhDeploymentIdealCut.sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [PqxdhDeploymentIdealCut.sourceInit, PqxdhRegistrationJointSchedule.initial, empty,
        PqxdhLiveKemBirth.empty]⟩
  have prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t)
      (PqxdhDeploymentIdealCut.sourceInit created pool).pool.2 := by
    simp [PqxdhDeploymentIdealCut.sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty,
      PqxdhDeploymentIdealPoolSource.PoolPrefix]
  have routerEmpty : PqxdhDynamicKemRouter.empty =
      PqxdhDeploymentIdealPoolSource.routerOf (PqxdhDeploymentIdealCut.sourceInit created pool).pool.2 := by
    simp only [PqxdhDeploymentIdealCut.sourceInit, PqxdhRegistrationJointSchedule.initial, empty]
    rfl
  rw [routerEmpty]
  exact PqxdhDeploymentIdealLaterPool.kemCommands_stoppedL setup codec checks t.kem.val created.seed identityIndex
    (p.pool t) program budget certified unreadIdentity unreadKem (PqxdhDeploymentIdealCut.sourceInit created pool) []
    owned prefixed (by simpa [PqxdhDeploymentIdealCut.sourceInit, PqxdhRegistrationJointSchedule.initial, empty,
      PqxdhLiveKemBirth.empty] using room)

/-- The rest of item 2's logged opaque scan after the common prefix, under the stopped selected-first router at the pool: the logged commands of `scanRest` at the compiled cut (on a completed run part, the terminal reads, the Server read and the post part), from the encoded owners, the log and the native state at the cut, then `opaqueRestL`. -/
noncomputable def opaqueAfterL (decision : Out × (Ledger × (Snap × Local)) → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (reached : (CutCE (X × Ledger) × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log)) :
    ProbComp (Option (OpaqueCut Reader KemSK (Out × (Ledger × (Snap × Local))) Bool) ×
      PqxdhDynamicKemJointSource.State KemSK) :=
  ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
    (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      (PqxdhDeploymentLaterServerCommands.run setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (scanRest setup codec route second (compileCutSnap setup codec route reached.1))
        (encodeState setup reached.2.1).owners reached.2.2 reached.2.1.shared) >>=
      opaqueRestL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
        (PqxdhRegistrationJointAcceptCutTag.decideTag decision))).run).run
    (reached.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.1.pool.2)

/-- The prefix of item 2's logged world at the challenger's draws (item 2's side): item 2's logged prephase at the drawn family (`PqxdhDeploymentIdealLaterParams.preOpaquePoolL`) for the compiled LQ-F program, at the target's raw-accept ordinal and KEM index, is the Server construction of `ideal_prefixL`, then the same common prefix (`commonPrefixL`), then `opaqueAfterL`. Premises: a budget of the compiled scan of the run part that reads no identity or KEM field and creates no more KEM keys than the pool holds. -/
theorem item2_prefixL (ensureInit : StateT A ProbComp Bool) (decision : Out × (Ledger × (Snap × Local)) → Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (compileCutSnap setup codec route <$> (simulateQ (compileSnapImpl setup codec route)
      (scanCE (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) t.accept)).run
        (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    PqxdhDeploymentIdealLaterParams.preOpaquePoolL (Reader := Reader) setup codec checks ensureInit none decision
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime count t.kem
        t.accept p.chosen p.others =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        (match born.1 with
        | none => pure (.failed born.2)
        | some created =>
            (commonPrefixL setup codec route checks t p created born.2.1
              (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) >>=
                opaqueAfterL setup codec route checks t p decision second
                  (PqxdhRegistrationJointServerBirth.encode created)) >>= fun result =>
              pure (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others result.1 result.2 born.2.2)) := by
  unfold PqxdhDeploymentIdealLaterParams.preOpaquePoolL
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
    rw [opaqueScan_splitL, compile_scanServer, PqxdhDeploymentLaterServerCommands.run_bind]
    simp only [simulateQ_bind, bind_assoc, OptionT.run_bind, Option.elimM, StateT.run_bind]
    change ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (PqxdhDeploymentLaterServerCommands.run setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (simulateQ embed _) [] []
          (PqxdhRegistrationSchedule.initial created).shared))).run).run (after.1.1, PqxdhDynamicKemRouter.empty) >>= _ = _
    rw [publicSame, stopped_scan_sourceL setup codec checks t p created created.server.server.metadata.identityIndex
      after.1 empty slot _ budget certified unreadIdentity unreadKem room, simulateQ_map, StateT.run_map,
      Functor.map_map, bind_map_left]
    unfold commonPrefixL
    refine bind_congr fun reached => ?_
    simp only [Option.elim_some]
    unfold opaqueAfterL
    simp only [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
    rfl


end Item2

/-! ### Facts at the cut -/

section Facts
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealLaterPool (sourcePoolL nativePoolL compiledPoolL)
open PqxdhDeploymentIdealCut (sourceInit PoolIndexed)
open PqxdhDeploymentIdealPoolSource (PoolOwned PoolPrefix sourcePool)
open PqxdhRegistrationJointOwnership (Entry)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Forgetting the log, the logged annotated pool source execution of any source14 program is item 2's annotated pool source execution. -/
theorem programPool_projectionL {Result : Type} (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) :
    (fun result => (result.1, result.2.1)) <$>
        (simulateQ (sourcePoolL setup codec checks seed identityIndex pairs) program).run (state, log) =
      (simulateQ (sourcePool setup codec checks seed identityIndex pairs) program).run state := by
  induction program using OracleComp.inductionOn generalizing state log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← PqxdhDeploymentIdealLaterPool.sourcePoolL_projection setup codec checks seed identityIndex pairs query state
        log, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2.1 result.2.2

/-- Every outcome of the common prefix, with the log forgotten, is an outcome of item 2's annotated pool source execution of the compiled scan. -/
theorem prefix_projectionL {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (work : OracleComp Spec Y)
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (member : reached ∈ support (commonPrefixL setup codec route checks t p created pool work)) :
    (reached.1, reached.2.1) ∈ support ((simulateQ (sourcePool setup codec checks created.seed
      created.server.server.metadata.identityIndex (p.pool t)) ((simulateQ (compileSnapImpl setup codec route)
        (scanCE work t.accept)).run (Snap.empty, Local.empty))).run (sourceInit created pool)) := by
  rw [← programPool_projectionL setup codec checks created.seed created.server.server.metadata.identityIndex
    (p.pool t) _ (sourceInit created pool) [], support_map]
  exact ⟨reached, member, rfl⟩

/-- On every outcome of the common prefix, the annotated source state keeps the source-side invariant at the pool and every owner entry's KEM index is its position. -/
theorem cut_ownedL {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (member : reached ∈ support (commonPrefixL setup codec route checks t p created pool work)) :
    PoolOwned created.seed created.server.server.metadata.identityIndex reached.2.1 ∧ PoolIndexed reached.2.1 := by
  have start : PoolOwned created.seed created.server.server.metadata.identityIndex (sourceInit created pool) ∧
      PoolIndexed (sourceInit created pool) :=
    ⟨⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩,
      by simp [PoolIndexed, sourceInit, PqxdhRegistrationJointSchedule.initial]⟩
  exact (PqxdhServerAuthExperiment.run_rel (sourcePool setup codec checks created.seed
      created.server.server.metadata.identityIndex (p.pool t))
    (fun before after => PoolOwned created.seed created.server.server.metadata.identityIndex before ∧
        PoolIndexed before →
      PoolOwned created.seed created.server.server.metadata.identityIndex after ∧ PoolIndexed after)
    (fun _ facts => facts) (fun _ _ _ left right facts => right (left facts))
    (fun query before after supported facts =>
      ⟨PqxdhDeploymentIdealPoolSource.query_poolOwned setup codec checks created.seed
        created.server.server.metadata.identityIndex (p.pool t) query before after facts.1 supported,
      PqxdhDeploymentIdealCut.query_indexed setup codec checks created.seed created.server.server.metadata.identityIndex
        (p.pool t) query before after facts.1 facts.2 supported⟩)
    _ _ _ (prefix_projectionL setup codec route checks t p created pool work reached member)) start

/-- On every outcome of the common prefix, the compiled program's local copies and the erased source state satisfy CE-3's merge invariant, under the approved codec contracts and for a Server constructed with the experiment's key ID and no peer. -/
theorem cut_goodL {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (work : OracleComp Spec Y)
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (member : reached ∈ support (commonPrefixL setup codec route checks t p created pool work)) :
    PqxdhDeploymentCompileInvariant.Good setup codec reached.1.2.2 (PqxdhRegistrationJointSchedule.source reached.2.1) := by
  have image := PqxdhDeploymentIdealLaterPool.programPool_nativeL setup codec checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)
    ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run (Snap.empty, Local.empty))
    (sourceInit created pool) []
  have erased : (reached.1, (PqxdhRegistrationJointSchedule.source reached.2.1, reached.2.2)) ∈ support
      ((simulateQ (nativePoolL setup codec checks created.seed (p.pool t))
        ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run (Snap.empty, Local.empty))).run
          (PqxdhRegistrationSchedule.initial created, [])) := by
    change _ ∈ support ((simulateQ (nativePoolL setup codec checks created.seed (p.pool t)) _).run
      (PqxdhRegistrationJointSchedule.source (sourceInit created pool), []))
    rw [← image, support_map]
    exact ⟨reached, member, rfl⟩
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at erased
  obtain ⟨final, finalMember, same⟩ := erased
  have copies : final.2.1.2 = reached.1.2.2 := congrArg (fun value => value.1.2.2) same
  have native : final.2.2.1 = PqxdhRegistrationJointSchedule.source reached.2.1 := congrArg (fun value => value.2.1) same
  rw [← copies, ← native]
  exact (PqxdhServerAuthExperiment.run_rel (compiledPoolL setup codec checks route created.seed (p.pool t))
    (fun before after => PqxdhDeploymentCompileInvariant.Good setup codec before.1.2 before.2.1 →
      PqxdhDeploymentCompileInvariant.Good setup codec after.1.2 after.2.1)
    (fun _ good => good) (fun _ _ _ left right good => right (left good))
    (fun query before after supported good => PqxdhDeploymentIdealLaterPool.good_step_poolL setup codec checks route
      created.seed (p.pool t) phase1 phase2 query before good after supported)
    _ _ final finalMember)
    (PqxdhDeploymentCompileInvariant.good_initial setup codec (PqxdhRegistrationSchedule.initial created) sender peers
      rfl (fun _ => rfl))

/-- On every outcome of the common prefix, the KEM pool holds the first entries of the challenger's pool, at most as many as the budget's creations, when the budget of the compiled run part creates no more KEM keys than the pool holds. -/
theorem cut_prefixL {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (whole : ∀ source, ((simulateQ (compileSnapImpl setup codec route) work).run (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (room : budget (.inl 1) ≤ (p.pool t).length)
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (member : reached ∈ support (commonPrefixL setup codec route checks t p created pool work)) :
    PoolPrefix (p.pool t) reached.2.1.pool.2 ∧ reached.2.1.pool.2.keys.length ≤ budget (.inl 1) := by
  have owned : PoolOwned created.seed created.server.server.metadata.identityIndex (sourceInit created pool) :=
    ⟨⟨PqxdhRegistrationJointSchedule.initial_owned pool _, slot⟩,
      by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]⟩
  have certified' : ∀ source, ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run
      (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source) := by
    intro source
    have bound := PqxdhRegistrationJointAcceptCut.scan_bound _ t.accept _ _ (whole source)
    rw [compile_scanSnap, isQueryBoundP_map_iff] at bound
    exact bound
  have creations := PqxdhRegistrationJointKemCommands.creations setup codec checks
    created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed)
    ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run (Snap.empty, Local.empty)) budget
    certified' (PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).owners
    (sourceInit created pool).shared
  have image := PqxdhDeploymentIdealPoolSource.kemCommands_reserved setup codec checks created.seed
    created.server.server.metadata.identityIndex (p.pool t)
    ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run (Snap.empty, Local.empty))
    (sourceInit created pool) owned
  have mapped : (((reached.1, (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2.1).owners),
      reached.2.1.shared), reached.2.1.pool) ∈ support ((simulateQ (PqxdhDeploymentIdealPoolSource.reservedAt setup
        (p.pool t)) (PqxdhRegistrationJointKemCommands.program setup codec checks
          created.server.server.metadata.identityIndex (setup.joint.publicKeys created.seed)
          ((simulateQ (compileSnapImpl setup codec route) (scanCE work t.accept)).run (Snap.empty, Local.empty))
          (PqxdhRegistrationJointGeneratedFinish.encodeState setup (sourceInit created pool)).owners
          (sourceInit created pool).shared)).run (sourceInit created pool).pool) := by
    rw [image, support_map]
    exact ⟨(reached.1, reached.2.1), prefix_projectionL setup codec route checks t p created pool work reached member,
      rfl⟩
  have prefixed := PqxdhDeploymentIdealPoolSource.reserved_program_prefix setup (p.pool t) _ _ creations
    (sourceInit created pool).pool.1 (sourceInit created pool).pool.2
    (by simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty,
      PqxdhDeploymentIdealPoolSource.PoolPrefix])
    (by simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using room) _ mapped
  refine ⟨prefixed.1, ?_⟩
  simpa [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty] using prefixed.2

/-- On every outcome of the common prefix, the KEM key pairs created so far are at most the budget's creations, and at a pending compiled cut the compiled continuation, for every reply of the suspended accept, stays within the budget of the whole compiled run part with only the remaining creations (`PqxdhDeploymentIdealCut.cut_residual` for the compiler with the finish snapshot). -/
theorem cut_residualL {Y : Type} (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (whole : ∀ source, ((simulateQ (compileSnapImpl setup codec route) work).run (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (member : reached ∈ support (commonPrefixL setup codec route checks t p created pool work)) :
    reached.2.1.pool.2.keys.length ≤ budget (.inl 1) ∧
      ∀ raw next, compileCutSnap setup codec route reached.1 = .pending raw next → ∀ reply source,
        (next reply).IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source)
          (Function.update budget (.inl 1) (budget (.inl 1) - reached.2.1.pool.2.keys.length) source) := by
  have scanned : (compileCutSnap setup codec route reached.1, reached.2.1) ∈ support
      ((simulateQ (sourcePool setup codec checks created.seed created.server.server.metadata.identityIndex (p.pool t))
        (PqxdhRegistrationJointAcceptCut.scan ((simulateQ (compileSnapImpl setup codec route) work).run
          (Snap.empty, Local.empty)) t.accept)).run (sourceInit created pool)) := by
    rw [compile_scanSnap, simulateQ_map, StateT.run_map, support_map]
    exact ⟨(reached.1, reached.2.1), prefix_projectionL setup codec route checks t p created pool work reached member,
      rfl⟩
  have start : (sourceInit created pool).pool.2.keys.length = 0 := by
    simp [sourceInit, PqxdhRegistrationJointSchedule.initial, empty, PqxdhLiveKemBirth.empty]
  have creations := PqxdhDeploymentIdealCut.scan_residual _
    (fun state : PqxdhRegistrationJointSchedule.State KemSK => state.pool.2.keys.length)
    (fun query => sourceKind (KemSK := KemSK) query = .inl 1)
    (fun query state result supported => (PqxdhDeploymentIdealCut.sourcePool_keys setup codec checks created.seed
      created.server.server.metadata.identityIndex (p.pool t) query state result supported).le)
    _ t.accept _ (whole (.inl 1)) _ _ scanned
  simp only [start, Nat.zero_add] at creations
  refine ⟨creations.1, fun raw next pending reply source => ?_⟩
  by_cases kind : source = .inl 1
  · subst kind
    simpa only [Function.update_self] using creations.2 raw next pending reply
  · have other := PqxdhDeploymentIdealCut.scan_residual _ (fun _ : PqxdhRegistrationJointSchedule.State KemSK => 0)
      (fun query => sourceKind (KemSK := KemSK) query = source)
      (fun _ _ _ _ => Nat.zero_le _) _ t.accept _ (whole source) _ _ scanned
    simpa only [Function.update_of_ne kind, Nat.zero_add, Nat.sub_zero] using other.2 raw next pending reply

/-- The relation at the cut, on an outcome of the common prefix (`commonPrefixL`), from which the CE side resumes with `resumeL` and item 2's side with `opaqueAfterL`: the source-side invariant at the pool, the owner positions, CE-3's merge invariant of the local copies and the erased source state, a prefix KEM pool within the budget's creations, owner `j` holding pool entry `j`, and the remaining creations of the compiled continuation at a pending cut (the logged form of `PqxdhDeploymentIdealBranch.CutRelIndexed`). -/
structure CutRelL {Y : Type} (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log)) : Prop where
  owned : PoolOwned created.seed created.server.server.metadata.identityIndex reached.2.1
  indexed : PoolIndexed reached.2.1
  good : PqxdhDeploymentCompileInvariant.Good setup codec reached.1.2.2 (PqxdhRegistrationJointSchedule.source reached.2.1)
  prefixed : PoolPrefix (p.pool t) reached.2.1.pool.2
  bounded : reached.2.1.pool.2.keys.length ≤ budget (.inl 1)
  entries : ∀ (j : ℕ) (entry : Entry KemSK), reached.2.1.owners[j]? = some entry →
    ∀ keys, PqxdhRegistrationJointOwnership.activeKey entry.owner = some keys → (p.pool t)[j]? = some keys
  residual : ∀ raw next, compileCutSnap setup codec route reached.1 = .pending raw next → ∀ reply source,
    (next reply).IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = source)
      (Function.update budget (.inl 1) (budget (.inl 1) - reached.2.1.pool.2.keys.length) source)

/-- Every outcome of the common prefix satisfies the relation at the cut, under the approved codec contracts, for a Server constructed with the experiment's key ID and no peer whose seed sits at its identity slot of the joint pool, with an empty KEM pool, and for a budget of the whole compiled run part that creates no more KEM keys than the pool holds. -/
theorem cut_relL {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (whole : ∀ source, ((simulateQ (compileSnapImpl setup codec route) work).run (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (room : budget (.inl 1) ≤ (p.pool t).length)
    (reached : (CutCE Y × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (member : reached ∈ support (commonPrefixL setup codec route checks t p created pool work)) :
    CutRelL setup codec route t p created budget reached := by
  obtain ⟨owned, indexed⟩ := cut_ownedL setup codec route checks t p created pool empty slot work reached member
  obtain ⟨prefixed, bounded⟩ := cut_prefixL setup codec route checks t p created pool empty slot work budget whole room
    reached member
  refine ⟨owned, indexed, cut_goodL setup codec route checks t p created phase1 phase2 sender peers pool work reached
    member, prefixed, bounded, fun j entry found keys active => ?_,
    (cut_residualL setup codec route checks t p created pool empty work budget whole reached member).2⟩
  have index := PqxdhDeploymentIdealCut.indexed_entry reached.2.1 indexed j entry found
  have stored := (owned.1.1 entry (List.mem_of_getElem? found)).2 keys active
  rw [index] at stored
  have bound : j < reached.2.1.pool.2.keys.length := (List.getElem?_eq_some_iff.mp stored).1
  rw [prefixed, List.getElem?_take] at stored
  simpa only [bound, ↓reduceIte] using stored

end Facts

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_query_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_query_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_accept_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_accept_succ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_bind_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_bind_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.scanL_embed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.compile_scanSnap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.compile_scanSnap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.compileServer_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.compileServer_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.restOf_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.restOf_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.compile_scanServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.compile_scanServer

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.realPost_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.realPost_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.laterTail_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.laterTail_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.ideal_cutL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.ideal_cutL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.pool_scan_sourceL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.pool_scan_sourceL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.ideal_prefixL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.ideal_prefixL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.opaqueScan_splitL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.opaqueScan_splitL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.stopped_scan_sourceL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.stopped_scan_sourceL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.item2_prefixL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.item2_prefixL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.programPool_projectionL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.programPool_projectionL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.prefix_projectionL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.prefix_projectionL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_ownedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_ownedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_goodL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_goodL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_prefixL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_prefixL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_residualL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_residualL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_relL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut.cut_relL
