-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLater
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! CE-COMPILE for the later-quantum game (stage LQ-2). The compiled program `compileLater A₁ A₂` is an ordinary source14 program in three parts. The run part is the CE-3 compiler applied to the wrapped run-phase adversary with one changed case (`compileSnapImpl`): before forwarding a `finish` on owner `c`, it issues the source14 field reads of `c`'s prekey and one-time scalar and captures them in its own snapshot; these reads are pure local reads that change no state and write no pool entry. The terminal part reads the identity, prekey and one-time fields of every created owner (the count is the compiled program's own log of successful creates) and builds the reveal with the snapshot. The post part runs `A₂` on the run's output and that reveal, forwarding its coins, HMAC and BLAKE2b queries to source14 through the unchanged compiler. The compiler modules of the CE-3 trial are reused unchanged: the finish pre-read is a wrapper around `compileImpl`, not a change to it. The field reads never read the R1 cache, the ghost touches or the family history, and the reveal is built only from identity, prekey and one-time field values. `compile_later_game` and `compile_later_source` state that the later-quantum game equals the merged initialized execution of the compiled program, jointly over the Server's public data, `A₂`'s output, the ledger, the snapshot, the complete final deployment state and the runtime state, under exactly the two approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`. `compile_later_bound` transports the run-phase budget and the post-run budget to source14 caps. The field-read caps need only the run-phase budget (`compile_later_reads`): `qCreate` identity reads and `qFinish + qCreate` prekey and one-time reads each, for every post-run adversary; the compiled program issues no KEM read for any adversary (`compile_later_no_kem`). Every raw accept is issued by the run part (`continuation_no_accept`), so the terminal identity reads, which are reveal requests to the identity pool in the annotated source execution, come after every raw accept and every raw-accept cut: no freshness reading made at an accept or at a cut sees them, but whole-run unrevealedness (`PqxdhDeploymentQuiet.kernel_reads_unrevealed`) is not available for `compileLater`. Authentication is not claimed in this mode: the run-phase authentication results (A2, T5) are cited on the classical compiled program of `A₁`, whose run is the run phase of the later game (`PqxdhDeploymentLater.snap_erase`), and not on `compileLater`, whose terminal reads and post part would enter their reductions. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhRegistrationJointLiveRead (Field Value value)
open PqxdhDeploymentInterface (Spec Command ModeSpec Mode FreshBounds Budget asModeO)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl wrap)
open PqxdhDeploymentCompile (Local merge compileImpl mergeOwner)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open PqxdhDeploymentCompileStep (compiledImpl)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentLater (Snap Revealed Reveal PostSpec PostBudget postClass postEmbed postImpl snapImpl
  finishOwner snapshotAt capture scalarOf fieldOf revealed revealAt revealOf LaterState)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type}

/-- One source14 field read of the owner at a handle. -/
def readQuery (index : Nat) (field : Field) : OracleComp (SourceSpec KemSK) (Option (Value KemSK)) :=
  ((SourceSpec KemSK).query (.inr (index, field)) : OracleComp (SourceSpec KemSK) _)

/-- The finish pre-read: before a `finish` on an owner, read its prekey and one-time fields and capture them; no other command reads. -/
def preRead (snap : Snap) : Option Nat → OracleComp (SourceSpec KemSK) Snap
  | none => pure snap
  | some index => do
      let prekey ← readQuery (KemSK := KemSK) index .prekey
      let oneTime ← readQuery (KemSK := KemSK) index .oneTime
      pure (capture snap index prekey oneTime)

/-- The compiler with the finish snapshot: the finish pre-read, then the unchanged CE-3 compiled command. -/
noncomputable def compileSnapImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT (Snap × Local) (OracleComp (SourceSpec KemSK))) := fun query state => do
  let snap ← preRead state.1 (finishOwner query)
  let result ← (compileImpl setup codec route query).run state.2
  pure (result.1, (snap, result.2))

/-- The reveal entry built from the identity, prekey and one-time field reads of one handle and the snapshot. -/
def revealEntry (snap : Snap) (index : Nat) (identity prekey oneTime : Option (Value KemSK)) : Option Revealed :=
  match identity with
  | some (.identity seed) =>
      some ⟨seed, (scalarOf prekey).or (snap index).prekey, (scalarOf oneTime).or (snap index).oneTime⟩
  | _ => none

/-- The terminal reads: for each handle in order, the identity, prekey and one-time field reads, turned into a reveal entry. -/
def terminal (snap : Snap) : List Nat → OracleComp (SourceSpec KemSK) Reveal
  | [] => pure []
  | index :: rest => do
      let identity ← readQuery (KemSK := KemSK) index .identity
      let prekey ← readQuery (KemSK := KemSK) index .prekey
      let oneTime ← readQuery (KemSK := KemSK) index .oneTime
      let tail ← terminal snap rest
      pure ((revealEntry snap index identity prekey oneTime).toList ++ tail)

/-- The compiled later-quantum program: the run part (the CE-3 compiler with the finish pre-read, on the wrapped run-phase adversary), the terminal reads of every created owner, and the post part (the post-run adversary on the run's output and the reveal, through the unchanged compiler). It returns the post-run output, the ledger, the snapshot and the final local state. -/
noncomputable def compileLater (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) :
    OracleComp (SourceSpec KemSK) (Out × (Ledger × (Snap × Local))) := do
  let run ← (simulateQ (compileSnapImpl setup codec route)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run (Snap.empty, Local.empty)
  let reveal ← terminal run.2.1 (List.range run.2.2.log.owners.length)
  let post ← (simulateQ (compileImpl setup codec route) (simulateQ postEmbed (second run.1.1 reveal))).run run.2.2
  pure (post.1, (run.1.2, (run.2.1, post.2)))

/-- The compiled handler with the finish snapshot under the source14 native handler, on the product of snapshot, local and source14 state. -/
noncomputable def compiledSnapImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT ((Snap × Local) × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed).mapStateTBase
    (compileSnapImpl setup codec route)).flattenStateT

/-- A source14 field read under the source14 native handler returns the current field and changes nothing. -/
theorem read_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (index : Nat) (field : Field) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (readQuery index field)).run native = pure (fieldOf native.owners index field, native) := by
  simp only [readQuery, simulateQ_spec_query, PqxdhRegistrationJointRevealSchedule.native]
  rfl

/-- The finish pre-read under the source14 native handler is the native snapshot capture on the current owners and changes nothing. -/
theorem preRead_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (snap : Snap) (target : Option Nat) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (preRead snap target)).run native = pure (snapshotAt snap native.owners target, native) := by
  cases target with
  | none => simp only [preRead, simulateQ_pure, StateT.run_pure, snapshotAt]
  | some index =>
      simp only [preRead, simulateQ_bind, StateT.run_bind, read_run, pure_bind, simulateQ_pure, StateT.run_pure,
        snapshotAt]

/-- One step of the compiled handler with the finish snapshot is the CE-3 compiled step with the native capture on the current source14 owners. -/
theorem compiledSnap_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledSnapImpl setup codec checks route serverSeed query).run ((snap, copies), native) =
      (fun result => (result.1, ((snapshotAt snap native.owners (finishOwner query), result.2.1), result.2.2))) <$>
        (compiledImpl setup codec checks route serverSeed query).run (copies, native) := by
  rw [PqxdhDeploymentCompileStep.compiledImpl_run]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
        ((compileSnapImpl setup codec route query).run (snap, copies))).run native = _
  have unfolded : (compileSnapImpl setup codec route query).run (snap, copies) =
      preRead snap (finishOwner query) >>= fun captured =>
        (compileImpl setup codec route query).run copies >>= fun result => pure (result.1, (captured, result.2)) := rfl
  rw [unfolded]
  simp only [simulateQ_bind, StateT.run_bind, preRead_run, pure_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
    Functor.map_map]

/-- `merge_fields`, per owner: merging replaces only an established owner's kernel, so the identity seed is kept. -/
theorem mergeOwner_identity (kernel : Option PqxdhDeploymentCompile.Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    (mergeOwner kernel owner).beacon.identity = owner.beacon.identity := by
  cases kernel with
  | none => rfl
  | some current => cases phase : owner.beacon.phase <;> simp [mergeOwner, phase]

/-- `merge_fields`, per owner: every field value other than the kernel is unchanged by merging. -/
theorem mergeOwner_value (kernel : Option PqxdhDeploymentCompile.Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (field : Field) (notKernel : field ≠ .kernel) : value field (mergeOwner kernel owner) = value field owner := by
  cases kernel with
  | none => rfl
  | some current =>
      cases phase : owner.beacon.phase <;> cases field <;>
        simp_all [mergeOwner, value, PqxdhRegistrationJointLiveRead.localValue, PqxdhRegistrationJointOwnership.activeKey]

/-- `merge_fields`: merging the compiled program's local copies into the source14 state changes no identity, KEM, prekey or one-time field of any owner. -/
theorem merge_fields (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (index : Nat) (field : Field)
    (notKernel : field ≠ .kernel) :
    fieldOf (merge copies native).native.owners index field = fieldOf native.owners index field := by
  simp only [fieldOf, PqxdhDeploymentCompileRecords.merge_owner]
  cases native.owners[index]? with
  | none => rfl
  | some owner => simp only [Option.map_some, Option.bind_some, mergeOwner_value _ _ _ notKernel]

/-- Merging keeps the number of owners. -/
theorem merge_length (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (merge copies native).native.owners.length = native.owners.length := by
  simp only [PqxdhDeploymentCompile.merge, List.length_mapIdx]

/-- Merging keeps every owner's revealed secrets. -/
theorem revealed_merge (snap : Snap) (index : Nat) (kernel : Option PqxdhDeploymentCompile.Kernel)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    revealed snap index (mergeOwner kernel owner) = revealed snap index owner := by
  simp only [revealed, mergeOwner_identity, mergeOwner_value kernel owner .prekey (by decide),
    mergeOwner_value kernel owner .oneTime (by decide)]

/-- Merging keeps the reveal: it is the same function of the source14 owners and of the merged owners. -/
theorem reveal_merge (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (snap : Snap) :
    revealOf (merge copies native).native.owners snap = revealOf native.owners snap := by
  simp only [revealOf, merge_length]
  congr 1
  funext index
  simp only [revealAt, PqxdhDeploymentCompileRecords.merge_owner, Option.map_map]
  cases native.owners[index]? with
  | none => rfl
  | some owner => simp only [Option.map_some, Function.comp_apply, revealed_merge]

/-- Merging keeps every finish capture. -/
theorem snapshot_merge (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (snap : Snap)
    (target : Option Nat) :
    snapshotAt snap (merge copies native).native.owners target = snapshotAt snap native.owners target := by
  cases target with
  | none => rfl
  | some index => simp only [snapshotAt, merge_fields copies native index .prekey (by decide),
      merge_fields copies native index .oneTime (by decide)]

/-- The finish pre-read case of the compile step: under the compile-step invariant, merging after a compiled step with the finish snapshot is the snapshot-handler step from the merged state; the pre-read captures exactly what the native handler captures. -/
theorem snap_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain) (snap : Snap)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (inv : PqxdhDeploymentCompileStep.Inv setup codec copies native) :
    Prod.map id (fun state : (Snap × Local) × PqxdhRegistrationSchedule.State KemSK => (state.1.1, merge state.1.2 state.2)) <$>
        (compiledSnapImpl setup codec checks route serverSeed query).run ((snap, copies), native) =
      (snapImpl setup codec checks route serverSeed query).run (snap, merge copies native) := by
  rw [compiledSnap_run, Functor.map_map]
  change _ = (fun result => (result.1, (snapshotAt snap (merge copies native).native.owners (finishOwner query), result.2))) <$>
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run (merge copies native)
  rw [snapshot_merge, ← PqxdhDeploymentCompileStep.step_merge setup codec checks route serverSeed query copies native inv,
    Functor.map_map]
  rfl

/-- Every compiled step with the finish snapshot keeps the CE-3 simulation invariant: the pre-reads change nothing. -/
theorem snap_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (query : Spec.Domain)
    (state : (Snap × Local) × PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec state.1.2 state.2)
    (result : Spec.Range query × ((Snap × Local) × PqxdhRegistrationSchedule.State KemSK))
    (supported : result ∈ support ((compiledSnapImpl setup codec checks route serverSeed query).run state)) :
    Good setup codec result.2.1.2 result.2.2 := by
  obtain ⟨⟨snap, copies⟩, native⟩ := state
  rw [compiledSnap_run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact PqxdhDeploymentCompileInvariant.good_step setup codec checks route serverSeed phase1 phase2 query copies native
    good inner member

/-- The run part of CE-COMPILE-L: from a state with the CE-3 invariant, the compiled program with the finish snapshot, merged at the end, has exactly the distribution of the snapshot-handler run from the merged state, jointly with the output and the snapshot. -/
theorem compile_snap_run {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (program : OracleComp Spec Result)
    (snap : Snap) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native) :
    Prod.map id (fun state : (Snap × Local) × PqxdhRegistrationSchedule.State KemSK => (state.1.1, merge state.1.2 state.2)) <$>
        (simulateQ (compiledSnapImpl setup codec checks route serverSeed) program).run ((snap, copies), native) =
      (simulateQ (snapImpl setup codec checks route serverSeed) program).run (snap, merge copies native) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv' _ _ (fun state => Good setup codec state.1.2 state.2) _
    (fun query state good result supported =>
      snap_good setup codec checks route serverSeed phase1 phase2 query state good result supported)
    (fun query state good => snap_step setup codec checks route serverSeed query state.1.1 state.1.2 state.2
      (PqxdhDeploymentCompileInvariant.good_inv setup codec _ _ good))
    program ((snap, copies), native) good

/-- Post-phase commutation: from a state with the CE-3 invariant, the post-run adversary's queries forwarded through the unchanged compiler, merged at the end, have exactly the distribution of the native post phase on the merged state. -/
theorem compile_post (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (adversary : OracleComp PostSpec Out)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec copies native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          ((simulateQ (compileImpl setup codec route) (simulateQ postEmbed adversary)).run copies)).run native =
      (simulateQ (postImpl setup codec checks serverSeed) adversary).run (merge copies native) := by
  rw [PqxdhDeploymentCompileStep.compile_simulation setup codec checks route serverSeed (Good setup codec)
    (PqxdhDeploymentCompileInvariant.good_inv setup codec)
    (PqxdhDeploymentCompileInvariant.good_step setup codec checks route serverSeed phase1 phase2) _ copies native good,
    PqxdhDeploymentLater.post_embed]

/-- The reveal entry of the field reads at a handle is the native reveal of the owner there. -/
theorem revealEntry_field (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (snap : Snap) (index : Nat) :
    revealEntry snap index (fieldOf owners index .identity) (fieldOf owners index .prekey) (fieldOf owners index .oneTime) =
      revealAt owners snap index := by
  simp only [fieldOf, revealAt]
  cases owners[index]? with
  | none => rfl
  | some owner => rfl

/-- Terminal reads under the source14 native handler return the native reveal entries of the read handles and change nothing. -/
theorem terminal_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (snap : Snap) (indices : List Nat) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (terminal snap indices)).run native = pure (indices.filterMap (revealAt native.owners snap), native) := by
  induction indices with
  | nil => simp only [terminal, simulateQ_pure, StateT.run_pure, List.filterMap_nil]
  | cons index rest ih =>
      simp only [terminal, simulateQ_bind, StateT.run_bind, read_run, pure_bind, ih, simulateQ_pure, StateT.run_pure,
        revealEntry_field, List.filterMap_cons]
      cases revealAt native.owners snap index <;> rfl

/-- The terminal reads of the compiled program, over every handle its log counts, return exactly the reveal of the merged final state. -/
theorem terminal_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (snap : Snap) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (count : copies.log.owners.length = native.owners.length) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (terminal snap (List.range copies.log.owners.length))).run native =
      pure (revealOf (merge copies native).native.owners snap, native) := by
  rw [terminal_run, count, reveal_merge]
  rfl

/-- The continuation after the run part: terminal reads and the post part, from a state with the CE-3 invariant, merged at the end, are the native reveal and post phase on the merged state. -/
theorem later_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (second : X → Reveal → OracleComp PostSpec Out)
    (output : X) (ledger : Ledger) (snap : Snap) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec copies native) :
    (fun result => (result.1.1, (result.1.2.1, (result.1.2.2.1, merge result.1.2.2.2 result.2)))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          (terminal snap (List.range copies.log.owners.length) >>= fun reveal =>
            (simulateQ (compileImpl setup codec route) (simulateQ postEmbed (second output reveal))).run copies >>=
              fun post => pure (post.1, (ledger, (snap, post.2))))).run native =
      (simulateQ (postImpl setup codec checks serverSeed)
          (second output (revealOf (merge copies native).native.owners snap))).run (merge copies native) >>=
        fun post => pure (post.1, (ledger, (snap, post.2))) := by
  rw [simulateQ_bind, StateT.run_bind, terminal_merge setup codec checks serverSeed snap copies native good.count, pure_bind,
    ← compile_post setup codec checks route serverSeed phase1 phase2 _ copies native good]
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind, map_pure, bind_map_left]

/-- CE-COMPILE-L at the native level: under the approved Phase 1 and Phase 2 read-back contracts, the compiled later-quantum program run under the source14 native handler from a fresh source14 state, with the compiled program's final local copies merged into the final source14 state, has exactly the distribution of the later execution (run phase with the finish snapshot, reveal of the final state, post phase) from the same state with zero raw-attempt counters, jointly over the post-run output, the ledger, the snapshot and the final deployment state. -/
theorem compile_later_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (peers : ∀ kid, native.shared.2.server.server.peers kid = none) (owners : native.owners = [])
    (pending : ∀ session, native.shared.2.pending session = none) :
    (fun result => (result.1.1, (result.1.2.1, (result.1.2.2.1, merge result.1.2.2.2 result.2)))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          (compileLater setup codec route bounds mode first second)).run native =
      PqxdhDeploymentLater.laterExec setup codec checks route serverSeed bounds mode first second
        ⟨native, 0, fun _ => 0, []⟩ := by
  have start := PqxdhDeploymentCompileInvariant.good_initial setup codec native keyId peers owners pending
  have flattened := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed) (compileSnapImpl setup codec route)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) (Snap.empty, Local.empty) native
  change _ = (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (compiledSnapImpl setup codec checks route serverSeed)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run ((Snap.empty, Local.empty), native)
    at flattened
  have run := compile_snap_run setup codec checks route serverSeed phase1 phase2
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) Snap.empty Local.empty native start
  rw [PqxdhDeploymentCompile.merge_empty] at run
  simp only [compileLater, simulateQ_bind, StateT.run_bind, flattened, bind_map_left, map_bind]
  simp only [PqxdhDeploymentLater.laterExec, PqxdhDeploymentLater.later_run_wrap, ← run, bind_map_left, Functor.map_map]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨output, ledger⟩, ⟨⟨snap, copies⟩, reached⟩⟩ member
  have good := OracleComp.simulateQ_run_preserves_inv_of_query _ (fun state => Good setup codec state.1.2 state.2)
    (fun query state good result supported =>
      snap_good setup codec checks route serverSeed phase1 phase2 query state good result supported)
    _ _ start _ member
  have cont := later_continuation setup codec checks route serverSeed phase1 phase2 second output ledger snap copies
    reached good
  simp only [simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure, StateT.run_pure, map_pure] at cont ⊢
  exact cont

/-- The merged outcome of the compiled later-quantum program's initialized execution. -/
def mergeLater (outcome : Option (PqxdhRegistrationJointInitializedSchedule.NativeOutcome KemSK
    (Out × (Ledger × (Snap × Local)))) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × LaterState KemSK) × A :=
  (outcome.1.map fun result =>
    (result.1, result.2.1.1, (result.2.1.2.1, (result.2.1.2.2.1, merge result.2.1.2.2.2 result.2.2))), outcome.2)

/-- Theorem CE-COMPILE-L: under the approved Phase 1 and Phase 2 read-back contracts, the later-quantum game with a generated Server seed is exactly the initialized source14 native execution of the compiled later-quantum program with the merged final state, jointly over the constructed Server's public data, the post-run output, the ledger, the snapshot, the complete final deployment state and the runtime state. -/
theorem compile_later_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) (runtime : A) :
    mergeLater <$> (PqxdhRegistrationJointInitializedSchedule.native setup codec checks ensureInit identityIndex none
        (compileLater setup codec route bounds mode first second)).run runtime =
      (PqxdhDeploymentLater.laterGame setup codec checks route ensureInit identityIndex bounds mode first second).run
        runtime := by
  simp only [PqxdhRegistrationJointInitializedSchedule.native, PqxdhDeploymentLater.laterGame, StateT.run, map_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | created, after⟩ born
  · simp only [map_pure, mergeLater, Option.map_none]
  · obtain ⟨sender, peers⟩ := PqxdhDeploymentCompileGame.construct_fields setup.joint ensureInit identityIndex
      setup.serverKeyId runtime created after born
    have compiled := compile_later_native setup codec checks route created.seed phase1 phase2 bounds mode first second
      (PqxdhRegistrationSchedule.initial created) sender peers rfl (fun _ => rfl)
    simp only [PqxdhDeploymentNative.initial]
    rw [← compiled, Functor.map_map, Functor.map_map]
    rfl

/-- CE-COMPILE-L at the level of the initialized source14 execution used by the KEM and root theorems: erasing the private service annotations and merging the compiled program's local copies maps that execution of the compiled later-quantum program exactly onto the later-quantum game, whose Server identity index is the private identity pool's current size. In that annotated execution the terminal identity reads are reveal requests to the identity pool; they follow every raw accept (`continuation_no_accept`), so freshness read at an accept or at a raw-accept cut does not see them, but whole-run unrevealedness (`PqxdhDeploymentQuiet.kernel_reads_unrevealed`) is not available for this program. -/
theorem compile_later_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    (fun result => mergeLater (result.1.map PqxdhRegistrationJointInitializedSchedule.eraseOutcome, result.2.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit none
          (compileLater setup codec route bounds mode first second)).run state =
      (PqxdhDeploymentLater.laterGame setup codec checks route ensureInit state.1.1.seeds.length bounds mode first
        second).run state.2 := by
  rw [← compile_later_game setup codec checks route ensureInit state.1.1.seeds.length phase1 phase2 bounds mode first
    second state.2, ← PqxdhRegistrationJointInitializedSchedule.initialized_native setup codec checks ensureInit none
      (compileLater setup codec route bounds mode first second) state, Functor.map_map]

/-- Native command caps of the wrapped run-phase adversary, transported through the secrecy layer. -/
def runCap (bounds : FreshBounds) (budget : Budget) (core : Fin 12) : Nat :=
  ∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds core full * budget.cap full

/-- Source queries of one kind issued by one run-phase command with the finish pre-read: the CE-3 cost, plus one prekey and one one-time read for a finish. -/
def laterCost (kind : SourceKind) (core : Fin 12) : Nat :=
  cost kind core + if core = 5 then unit kind (.inr 2) + unit kind (.inr 3) else 0

/-- Source queries of one kind issued by the terminal reads of one owner: one identity, one prekey and one one-time read. -/
def readCost (kind : SourceKind) : Nat := unit kind (.inr 0) + unit kind (.inr 2) + unit kind (.inr 3)

/-- The native command class repeated by each post-run class: coin, HMAC, BLAKE2b. -/
def postCore : Fin 3 → Fin 12 := ![0, 6, 7]

/-- A pure source14 program issues no query. -/
theorem pure_bound {Result : Type} (value : Result) (predicate : (SourceSpec KemSK).Domain → Prop) [DecidablePred predicate]
    (bound : Nat) : (pure value : OracleComp (SourceSpec KemSK) Result).IsQueryBoundP predicate bound :=
  trivial

/-- One source14 field read costs one query of its field's kind. -/
theorem read_bound (kind : SourceKind) (index : Nat) (field : Field) :
    (readQuery (KemSK := KemSK) index field).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind)
      (unit kind (.inr (PqxdhRegistrationJointRevealCosts.fieldIndex field))) := by
  unfold readQuery
  rw [isQueryBoundP_query_iff]
  intro same
  subst same
  simp [unit, sourceKind]

/-- The finish pre-read of a command costs one prekey and one one-time read for a finish and nothing otherwise. -/
theorem preRead_bound (kind : SourceKind) (snap : Snap) (query : Spec.Domain) :
    (preRead (KemSK := KemSK) snap (finishOwner query)).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (if commandKind query = 5 then unit kind (.inr 2) + unit kind (.inr 3) else 0) := by
  rcases query with coin | command
  · trivial
  · cases command with
    | finish index raw =>
        refine IsQueryBoundP.mono (isQueryBoundP_bind (read_bound kind index .prekey) fun _ _ =>
          isQueryBoundP_bind (read_bound kind index .oneTime) fun _ _ => pure_bound _ _ 0) ?_
        simp [commandKind, PqxdhRegistrationJointRevealCosts.fieldIndex]
    | _ => trivial

/-- Every compiled run-phase command with the finish pre-read issues at most its class's later cost of each source kind. -/
theorem snap_step_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind) (query : Spec.Domain) (state : Snap × Local) :
    ((compileSnapImpl setup codec route query).run state).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (laterCost kind (commandKind query)) := by
  refine IsQueryBoundP.mono (isQueryBoundP_bind (preRead_bound kind state.1 query) fun _ _ =>
    isQueryBoundP_bind (PqxdhDeploymentCompileBudget.step_bound setup codec route kind query state.2) fun _ _ =>
      pure_bound _ _ 0) ?_
  simp only [laterCost]
  omega

/-- The terminal reads cost one identity, one prekey and one one-time read per handle. -/
theorem terminal_bound (kind : SourceKind) (snap : Snap) (indices : List Nat) :
    (terminal (KemSK := KemSK) snap indices).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind)
      (readCost kind * indices.length) := by
  induction indices with
  | nil => trivial
  | cons index rest ih =>
      refine IsQueryBoundP.mono (isQueryBoundP_bind (read_bound kind index .identity) fun _ _ =>
        isQueryBoundP_bind (read_bound kind index .prekey) fun _ _ =>
          isQueryBoundP_bind (read_bound kind index .oneTime) fun _ _ =>
            isQueryBoundP_bind ih fun _ _ => pure_bound _ _ 0) ?_
      simp only [readCost, PqxdhRegistrationJointRevealCosts.fieldIndex, List.length_cons, Nat.mul_succ]
      omega

/-- The post part costs, of each source kind, the CE-3 cost of the repeated command class times the post-run cap of each post-run class. -/
theorem post_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind) (adversary : OracleComp PostSpec Out)
    (budget : PostBudget) (respects : budget.Respects adversary) (copies : Local) :
    ((simulateQ (compileImpl setup codec route) (simulateQ postEmbed adversary)).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (∑ post, cost kind (postCore post) * budget.cap post) := by
  rw [← QueryImpl.simulateQ_compose]
  refine FinitePartitionQueryBounds.weighted_bound postClass (fun post => cost kind (postCore post)) budget.cap
    ((compileImpl setup codec route) ∘ₛ postEmbed) _ adversary respects (fun query state => ?_) copies
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    exact PqxdhDeploymentCompileBudget.step_bound setup codec route kind (.inl coin) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    exact PqxdhDeploymentCompileBudget.step_bound setup codec route kind (.inr (.hmac key message)) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    exact PqxdhDeploymentCompileBudget.step_bound setup codec route kind (.inr (.hash bytes)) state

/-- A successful-reply log entry never adds a created owner. -/
theorem logReply_owners (log : PqxdhDeploymentCompile.Log) (command : Command)
    (reply : PqxdhDeploymentInterface.CommandSpec command) :
    (PqxdhDeploymentCompile.logReply log command reply).owners = log.owners := by
  cases command <;> simp only [PqxdhDeploymentCompile.logReply] <;> split <;> rfl

/-- A compiled Server record command keeps the log, for every source14 reply. -/
theorem serverLocal_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) (copies : Local)
    (result : RawCtxServerMixed.SourceSpec.Range query × Local)
    (supported : result ∈ support ((PqxdhDeploymentCompile.serverLocal (KemSK := KemSK) setup codec route query).run copies)) :
    result.2.log = copies.log := by
  cases target : PqxdhDeploymentCompile.serverTarget route query with
  | none =>
      rw [PqxdhDeploymentCompileRecords.serverLocal_none setup codec route query copies target, support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | some kid =>
      rw [PqxdhDeploymentCompileRecords.serverLocal_some setup codec route query copies kid target,
        mem_support_bind_iff] at supported
      obtain ⟨_, _, supported⟩ := supported
      rw [support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl

/-- A compiled Beacon record command keeps the log, for every source14 reply. -/
theorem beaconLocal_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (copies : Local) (result : RawCtxMixedOwner.SourceSpec.Range query × Local)
    (supported : result ∈ support ((PqxdhDeploymentCompile.beaconLocal (KemSK := KemSK) setup codec index query).run copies)) :
    result.2.log = copies.log := by
  by_cases inside : index < copies.log.owners.length
  · rw [PqxdhDeploymentCompileRecords.beaconLocal_present setup codec index query copies inside,
      mem_support_bind_iff] at supported
    obtain ⟨_, _, supported⟩ := supported
    rw [support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    rfl
  · rw [PqxdhDeploymentCompileRecords.beaconLocal_absent setup codec index query copies inside, support_pure,
      Set.mem_singleton_iff] at supported
    subst supported
    rfl

/-- A forwarded registration command with logged reply keeps the created owners of the log, for every source14 reply. -/
theorem forwardLogged_owners (request : PqxdhRegistrationSchedule.Request) (command : Command)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.CommandSpec command)
    (copies : Local) (result : PqxdhDeploymentInterface.CommandSpec command × Local)
    (supported : result ∈ support ((PqxdhDeploymentCompile.forwardLogged (KemSK := KemSK) request command reply).run copies)) :
    result.2.log.owners = copies.log.owners := by
  have run : (PqxdhDeploymentCompile.forwardLogged (KemSK := KemSK) request command reply).run copies =
      PqxdhDeploymentCompile.forward request >>= fun answer =>
        pure (reply answer, { copies with log := PqxdhDeploymentCompile.logReply copies.log command (reply answer) }) := rfl
  rw [run, mem_support_bind_iff] at supported
  obtain ⟨_, _, supported⟩ := supported
  rw [support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact logReply_owners _ _ _

/-- A forwarded command without a logged reply keeps the whole local state, for every source14 reply. -/
theorem lift_local {Result : Type} (work : OracleComp (SourceSpec KemSK) Result) (copies : Local)
    (result : Result × Local)
    (supported : result ∈ support ((StateT.lift work : StateT Local (OracleComp (SourceSpec KemSK)) Result).run copies)) :
    result.2 = copies := by
  rw [StateT.run_lift, mem_support_bind_iff] at supported
  obtain ⟨_, _, supported⟩ := supported
  rw [support_pure, Set.mem_singleton_iff] at supported
  subst supported
  rfl

/-- A compiled command adds at most one created owner to the log, and only a create adds one, for every source14 reply. -/
theorem compile_owners (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain) (copies : Local)
    (result : Spec.Range query × Local) (supported : result ∈ support ((compileImpl setup codec route query).run copies)) :
    result.2.log.owners.length ≤ copies.log.owners.length + if commandKind query = 1 then 1 else 0 := by
  rcases query with coin | command
  · rw [lift_local ((SourceSpec KemSK).query (.inl (.inl coin)) : OracleComp (SourceSpec KemSK) _) copies result supported]
    simp
  · cases command with
    | create pin keyId =>
        cases parsed : PqxdhDeploymentInterface.parsePin pin with
        | none =>
            have run : (compileImpl setup codec route (.inr (.create pin keyId))).run copies = pure (none, copies) := by
              simp only [compileImpl, StateT.run, parsed]
            rw [run, support_pure, Set.mem_singleton_iff] at supported
            subst supported
            simp
        | some word =>
            have run : (compileImpl setup codec route (.inr (.create pin keyId))).run copies =
                PqxdhDeploymentCompile.forward (KemSK := KemSK) (.create word keyId) >>= fun index =>
                  pure (some index, { copies with log := { copies.log with owners := copies.log.owners ++ [(word, keyId)] } }) := by
              simp only [compileImpl, StateT.run, parsed]
            rw [run, mem_support_bind_iff] at supported
            obtain ⟨_, _, supported⟩ := supported
            rw [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            simp [commandKind]
    | bundle owner =>
        rw [forwardLogged_owners (.bundle owner) (.bundle owner) id copies result supported]
        simp
    | accept raw =>
        rw [forwardLogged_owners (.accept raw) (.accept raw) id copies result supported]
        simp
    | build session payload =>
        rw [forwardLogged_owners (.build session payload) (.build session payload) id copies result supported]
        simp
    | finish owner raw =>
        rw [forwardLogged_owners (.finish owner raw) (.finish owner raw) id copies result supported]
        simp
    | hmac key message =>
        rw [lift_local (PqxdhDeploymentCompile.forward (.hmac key message)) copies result supported]
        simp
    | hash bytes =>
        rw [lift_local (PqxdhDeploymentCompile.forward (.hash bytes)) copies result supported]
        simp
    | serverSend kid plaintext =>
        rw [serverLocal_log setup codec route (.inl (plaintext, kid)) copies result supported]
        simp
    | serverRaw raw =>
        rw [serverLocal_log setup codec route (.inr raw) copies result supported]
        simp
    | beaconSend index plaintext =>
        rw [beaconLocal_log setup codec index (.inl plaintext) copies result supported]
        simp
    | beaconRaw index raw =>
        rw [beaconLocal_log setup codec index (.inr raw) copies result supported]
        simp

/-- A compiled run-phase command with the finish pre-read adds at most one created owner to the log, and only a create adds one. -/
theorem snap_owners (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain) (state : Snap × Local)
    (result : Spec.Range query × (Snap × Local))
    (supported : result ∈ support ((compileSnapImpl setup codec route query).run state)) :
    result.2.2.log.owners.length ≤ state.2.log.owners.length + if commandKind query = 1 then 1 else 0 := by
  have run : (compileSnapImpl setup codec route query).run state =
      preRead state.1 (finishOwner query) >>= fun captured =>
        (compileImpl setup codec route query).run state.2 >>= fun inner => pure (inner.1, (captured, inner.2)) := rfl
  rw [run, mem_support_bind_iff] at supported
  obtain ⟨_, _, supported⟩ := supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨inner, member, supported⟩ := supported
  rw [support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact compile_owners setup codec route query state.2 inner member

/-- The log of the run part counts at most the transported create cap of created owners, so the terminal part reads at most that many owners. -/
theorem owners_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects first)
    (result : (X × Ledger) × (Snap × Local))
    (supported : result ∈ support ((simulateQ (compileSnapImpl setup codec route)
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run (Snap.empty, Local.empty))) :
    result.2.2.log.owners.length ≤ runCap bounds budget 1 := by
  have counted := run_count (compileSnapImpl setup codec route) (fun query => commandKind query = 1)
    (fun state => state.2.log.owners.length) (snap_owners setup codec route)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) (runCap bounds budget 1)
    (PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode first budget respects 1)
    (Snap.empty, Local.empty) result supported
  simpa [Local.empty, PqxdhDeploymentCompile.Log.empty] using counted

/-- The transported create cap is the create budget: tests and fresh messages issue no create. -/
theorem runCap_create (bounds : FreshBounds) (budget : Budget) : runCap bounds budget 1 = budget.create := by
  simp [runCap, PqxdhDeploymentCompileSecrecy.wrapCost, Fin.sum_univ_succ, Budget.cap]

/-- The transported finish cap is the finish budget: tests and fresh messages issue no finish. -/
theorem runCap_finish (bounds : FreshBounds) (budget : Budget) : runCap bounds budget 5 = budget.finish := by
  simp [runCap, PqxdhDeploymentCompileSecrecy.wrapCost, Fin.sum_univ_succ, Budget.cap]

/-- Budget transport for the compiled later-quantum program: if `A₁` respects the run-phase budget and `A₂` respects the post-run budget on every input, the compiled program makes at most the run-part cost (the CE-3 cost plus the finish pre-reads), plus one identity, prekey and one-time read per transported create, plus the post-part cost, source14 queries of each kind. This is the `certified` premise of the KEM and root theorems for `compileLater`. -/
theorem compile_later_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal)) (kind : SourceKind) :
    (compileLater setup codec route bounds mode first second).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ core, laterCost kind core * runCap bounds budget core + readCost kind * runCap bounds budget 1 +
        ∑ postKind, cost kind (postCore postKind) * post.cap postKind) := by
  have runBound := FinitePartitionQueryBounds.weighted_bound commandKind (laterCost kind) (runCap bounds budget)
    (compileSnapImpl setup codec route) (fun request => sourceKind (KemSK := KemSK) request = kind)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode first
      budget respects core)
    (fun query state => snap_step_bound setup codec route kind query state) (Snap.empty, Local.empty)
  have restBound : ∀ run ∈ support ((simulateQ (compileSnapImpl setup codec route)
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run (Snap.empty, Local.empty)),
      (terminal run.2.1 (List.range run.2.2.log.owners.length) >>= fun reveal =>
        (simulateQ (compileImpl setup codec route) (simulateQ postEmbed (second run.1.1 reveal))).run run.2.2 >>=
          fun result => pure (result.1, (run.1.2, (run.2.1, result.2)))).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = kind)
        (readCost kind * runCap bounds budget 1 + (∑ postKind, cost kind (postCore postKind) * post.cap postKind + 0)) := by
    intro run member
    have count := owners_bound setup codec route bounds mode first budget respects run member
    have reads := IsQueryBoundP.mono (terminal_bound (KemSK := KemSK) kind run.2.1
      (List.range run.2.2.log.owners.length)) (Nat.mul_le_mul_left (readCost kind) (by simpa only [List.length_range] using count))
    exact isQueryBoundP_bind reads fun reveal _ =>
      isQueryBoundP_bind (post_bound setup codec route kind (second run.1.1 reveal) post (postRespects _ _) run.2.2)
        fun _ _ => pure_bound _ _ 0
  exact IsQueryBoundP.mono (isQueryBoundP_bind runBound restBound) (by omega)

/-- The field-read caps of the compiled later-quantum program: at most `qCreate` identity reads, no KEM read, and at most `qFinish + qCreate` prekey reads and one-time reads each. Only the run-phase budget is assumed: the post part forwards only coin, HMAC and BLAKE2b commands, which issue no field read, so the caps hold for every post-run adversary. -/
theorem compile_later_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) :
    (compileLater setup codec route bounds mode first second).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = .inr 0) budget.create ∧
      (compileLater setup codec route bounds mode first second).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = .inr 1) 0 ∧
      (compileLater setup codec route bounds mode first second).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = .inr 2) (budget.finish + budget.create) ∧
      (compileLater setup codec route bounds mode first second).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = .inr 3) (budget.finish + budget.create) := by
  have zero : ∀ (field : Fin 5) (core : Fin 12), field ≠ 4 → cost (.inr field) core = 0 := by
    intro field core notKernel
    fin_cases core <;> simp [cost, unit, notKernel]
  have fieldReads : ∀ field : Fin 5, field ≠ 4 →
      (compileLater setup codec route bounds mode first second).IsQueryBoundP
        (fun request => sourceKind (KemSK := KemSK) request = .inr field)
        (∑ core, laterCost (.inr field) core * runCap bounds budget core +
          readCost (.inr field) * runCap bounds budget 1) := by
    intro field notKernel
    have runBound := FinitePartitionQueryBounds.weighted_bound commandKind (laterCost (.inr field))
      (runCap bounds budget) (compileSnapImpl setup codec route)
      (fun request => sourceKind (KemSK := KemSK) request = .inr field)
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
      (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode
        first budget respects core)
      (fun query state => snap_step_bound setup codec route (.inr field) query state) (Snap.empty, Local.empty)
    have restBound : ∀ run ∈ support ((simulateQ (compileSnapImpl setup codec route)
        (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run (Snap.empty, Local.empty)),
        (terminal run.2.1 (List.range run.2.2.log.owners.length) >>= fun reveal =>
          (simulateQ (compileImpl setup codec route) (simulateQ postEmbed (second run.1.1 reveal))).run run.2.2 >>=
            fun result => pure (result.1, (run.1.2, (run.2.1, result.2)))).IsQueryBoundP
          (fun request => sourceKind (KemSK := KemSK) request = .inr field)
          (readCost (.inr field) * runCap bounds budget 1 + (0 + 0)) := by
      intro run member
      have count := owners_bound setup codec route bounds mode first budget respects run member
      have reads := IsQueryBoundP.mono (terminal_bound (KemSK := KemSK) (.inr field) run.2.1
        (List.range run.2.2.log.owners.length))
        (Nat.mul_le_mul_left (readCost (.inr field)) (by simpa only [List.length_range] using count))
      exact isQueryBoundP_bind reads fun reveal _ =>
        isQueryBoundP_bind (PqxdhDeploymentCompileSecrecy.simulate_zero (compileImpl setup codec route) _
          (fun query copies => by
            simpa only [zero field _ notKernel] using
              PqxdhDeploymentCompileBudget.step_bound setup codec route (.inr field) query copies)
          _ run.2.2) fun _ _ => pure_bound _ _ 0
    exact IsQueryBoundP.mono (isQueryBoundP_bind runBound restBound) (by omega)
  refine ⟨IsQueryBoundP.mono (fieldReads 0 (by decide)) ?_, IsQueryBoundP.mono (fieldReads 1 (by decide)) ?_,
    IsQueryBoundP.mono (fieldReads 2 (by decide)) ?_, IsQueryBoundP.mono (fieldReads 3 (by decide)) ?_⟩
  all_goals simp [laterCost, readCost, zero, unit, runCap_create, runCap_finish]

/-- The compiled later-quantum program issues no KEM read, for every pair of adversaries and without a budget: the finish pre-reads, the terminal reads and the post part read only identity, prekey and one-time fields. The KEM read cap of the approved GoodKem argument therefore stays 0. -/
theorem compile_later_no_kem (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → Reveal → OracleComp PostSpec Out) :
    (compileLater setup codec route bounds mode first second).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr 1) 0 := by
  have zero : ∀ core : Fin 12, cost (.inr 1) core = 0 := by
    intro core
    fin_cases core <;> simp [cost, unit]
  have laterZero : ∀ core, laterCost (.inr 1) core = 0 := by
    intro core
    simp [laterCost, zero, unit]
  have runZero := PqxdhDeploymentCompileSecrecy.simulate_zero (compileSnapImpl setup codec route) _
    (fun query state => by simpa only [laterZero] using snap_step_bound setup codec route (.inr 1) query state)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) (Snap.empty, Local.empty)
  refine isQueryBoundP_bind (n := 0) (m := 0) runZero fun run _ => ?_
  have readZero : (terminal (KemSK := KemSK) run.2.1 (List.range run.2.2.log.owners.length)).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr 1) 0 := by
    simpa [readCost, unit] using terminal_bound (KemSK := KemSK) (.inr 1) run.2.1 (List.range run.2.2.log.owners.length)
  refine isQueryBoundP_bind (n := 0) (m := 0) readZero fun reveal _ => ?_
  exact isQueryBoundP_bind (n := 0) (m := 0) (PqxdhDeploymentCompileSecrecy.simulate_zero (compileImpl setup codec route) _
    (fun query copies => by simpa only [zero] using PqxdhDeploymentCompileBudget.step_bound setup codec route (.inr 1) query copies)
    _ run.2.2) fun _ _ => pure_bound _ _ 0

/-- Every raw accept of `compileLater` is issued by its run part: the continuation after the run part, the terminal reads followed by the post part, issues no raw accept, for every run-part result and every post-run adversary, without a budget. So the terminal identity reads follow every raw accept and every raw-accept cut. -/
theorem continuation_no_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (second : X → Reveal → OracleComp PostSpec Out)
    (run : (X × Ledger) × (Snap × Local)) :
    (terminal (KemSK := KemSK) run.2.1 (List.range run.2.2.log.owners.length) >>= fun reveal =>
        (simulateQ (compileImpl setup codec route) (simulateQ postEmbed (second run.1.1 reveal))).run run.2.2 >>=
          fun result => pure (result.1, (run.1.2, (run.2.1, result.2)))).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
  have readZero : (terminal (KemSK := KemSK) run.2.1 (List.range run.2.2.log.owners.length)).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 3) 0 := by
    simpa [readCost, unit] using terminal_bound (KemSK := KemSK) (.inl 3) run.2.1 (List.range run.2.2.log.owners.length)
  refine isQueryBoundP_bind (n := 0) (m := 0) readZero fun reveal _ => ?_
  rw [← QueryImpl.simulateQ_compose]
  refine isQueryBoundP_bind (n := 0) (m := 0) (PqxdhDeploymentCompileSecrecy.simulate_zero
    ((compileImpl setup codec route) ∘ₛ postEmbed) _ (fun query state => ?_) _ run.2.2) fun _ _ => pure_bound _ _ 0
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [commandKind, cost, unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) (.inl coin) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [commandKind, cost, unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) (.inr (.hmac key message)) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    simpa [commandKind, cost, unit] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 3) (.inr (.hash bytes)) state

end BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.read_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.read_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.preRead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.preRead_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compiledSnap_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compiledSnap_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.mergeOwner_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.mergeOwner_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.mergeOwner_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.mergeOwner_value

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.merge_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.merge_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.merge_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.merge_length

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.revealed_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.revealed_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.reveal_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.reveal_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snapshot_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snapshot_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_good

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_snap_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_snap_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_post

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.revealEntry_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.revealEntry_field

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.terminal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.terminal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.terminal_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.terminal_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.later_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.later_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.pure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.pure_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.read_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.read_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.preRead_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.preRead_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_step_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.terminal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.terminal_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.post_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.logReply_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.logReply_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.serverLocal_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.serverLocal_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.beaconLocal_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.beaconLocal_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.forwardLogged_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.forwardLogged_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.lift_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.lift_local

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.snap_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.owners_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.owners_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.runCap_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.runCap_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.runCap_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.runCap_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_no_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.compile_later_no_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.continuation_no_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile.continuation_no_accept
