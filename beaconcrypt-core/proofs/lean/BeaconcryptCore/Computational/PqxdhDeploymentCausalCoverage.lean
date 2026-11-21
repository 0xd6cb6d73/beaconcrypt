-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCausalPublication
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage

/-! The actual legacy/source14 secrecy handler appends exactly its input and returned mode-O reply. Its simultaneous observer therefore retains the same complete chronological journal as the original secrecy ledger, both currently and at every saved prefix. These are source14 execution invariants. Historical acceptance/budget equivalence and transfer to the mandatory-ML native experiment remain separate. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage
open PqxdhDeploymentInterface (FullSpec Entry FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentSessionSnapshots (Journal)
variable {ι KemSK Reader Response Index X A : Type} {baseSpec : OracleSpec ι}

/-- Exact ledger update for every forwarded, admitted or rejected query. -/
theorem ledger_records (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (result : FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKeyId bounds query).run ledger)) :
    result.2.transcript = ledger.transcript ++ [⟨query, result.1⟩] := by
  classical
  rcases query with forwarded | (⟨handle, left, right⟩ | ⟨handle, length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rfl
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    repeat' split at supported
    all_goals first
      | obtain rfl := (mem_support_pure_iff _ _).mp supported
        rfl
      | obtain ⟨_, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
        first
          | obtain rfl := (mem_support_pure_iff _ _).mp supported
            rfl
          | obtain ⟨_, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
            obtain rfl := (mem_support_pure_iff _ _).mp supported
            rfl
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run] at supported
    repeat' split at supported
    all_goals first
      | obtain rfl := (mem_support_pure_iff _ _).mp supported
        rfl
      | obtain ⟨_, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
        obtain ⟨_, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
        obtain rfl := (mem_support_pure_iff _ _).mp supported
        rfl

/-- The source secrecy layer is run through the actual deployment handler on its original shared state. -/
theorem handler_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (query : FullSpec.Domain) (before : PqxdhDeploymentSecrecy.State KemSK) :
    (PqxdhDeploymentSecrecy.handler setup codec checks route seed bounds query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhDeploymentNative.handler setup codec checks route seed)
          ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run before.1)).run
          before.2 := rfl

/-- Every supported actual callback appends exactly its query and actual mode-O reply, including optional failures. -/
theorem handler_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (query : FullSpec.Domain) (before : PqxdhDeploymentSecrecy.State KemSK)
    (result : FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)
    (supported : result ∈ support ((PqxdhDeploymentSecrecy.handler setup codec checks route seed bounds query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] := by
  rw [handler_run, support_map] at supported
  obtain ⟨after, reached, rfl⟩ := supported
  exact ledger_records setup.source.crypto codec setup.serverKeyId bounds query before.1 after.1
    (OracleComp.support_simulateQ_run'_subset
      (PqxdhDeploymentNative.handler setup codec checks route seed)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run before.1) before.2
      (by simpa only [StateT.run'_eq, support_map] using Set.mem_image_of_mem Prod.fst reached))

def entries (journal : Journal FullSpec) : List Entry :=
  journal.map fun entry => ⟨entry.1, entry.2⟩

abbrev SnapshotState (Index KemSK : Type) :=
  PqxdhDeploymentSessionSnapshots.State Index FullSpec (PqxdhDeploymentSecrecy.State KemSK)

/-- The current ledger and every saved ledger are the literal journals of their own actual execution prefixes. -/
def Consistent (state : SnapshotState Index KemSK) : Prop :=
  state.native.1.transcript = entries state.journal ∧
    ∀ index snapshot, state.captured index = some snapshot → snapshot.2.1.transcript = entries snapshot.1

theorem advance_consistent
    (stop : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stop index)]
    (state : SnapshotState Index KemSK) (query : FullSpec.Domain) (reply : FullSpec.Range query)
    (native : PqxdhDeploymentSecrecy.State KemSK) (consistent : Consistent state)
    (recorded : native.1.transcript = state.native.1.transcript ++ [⟨query, reply⟩]) :
    Consistent (PqxdhDeploymentSessionSnapshots.advance stop state query reply native) := by
  have current : native.1.transcript = entries (state.journal ++ [⟨query, reply⟩]) := by
    simpa [entries] using recorded.trans (congrArg (fun transcript => transcript ++ [⟨query, reply⟩]) consistent.1)
  refine ⟨current, ?_⟩
  intro index snapshot saved
  cases previous : state.captured index with
  | none =>
      simp [PqxdhDeploymentSessionSnapshots.advance, previous] at saved
      rcases saved with ⟨_, rfl⟩
      exact current
  | some receipt =>
      have same : receipt = snapshot := by
        simpa [PqxdhDeploymentSessionSnapshots.advance, previous] using saved
      exact same ▸ consistent.2 index receipt previous

/-- Linkage is preserved along the complete adaptive program, including all callbacks after a saved acceptance. -/
theorem program_consistent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (stop : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp FullSpec X) (state : SnapshotState Index KemSK) (consistent : Consistent state)
    (outcome : X × SnapshotState Index KemSK)
    (supported : outcome ∈ support ((simulateQ
      (PqxdhDeploymentSessionSnapshots.handler (PqxdhDeploymentSecrecy.handler setup codec checks route seed bounds) stop)
        program).run state)) : Consistent outcome.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simpa only [supported] using consistent
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, PqxdhDeploymentSessionSnapshots.handler_run,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨step, reached, continued⟩ := supported
      exact ih step.1 _ (advance_consistent stop state query step.1 step.2 consistent
        (handler_records setup codec checks route seed bounds query state.native step reached)) continued

theorem initial_consistent (native : PqxdhDeploymentNative.State KemSK) :
    Consistent (⟨[], fun _ => none, (PqxdhDeploymentSecrecy.Ledger.empty, native)⟩ : SnapshotState Index KemSK) :=
  ⟨rfl, fun _ _ impossible => nomatch impossible⟩

/-- All current and saved source14 ledgers equal their actual journals in the same complete run. -/
theorem run_consistent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (stop : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp FullSpec X) (native : PqxdhDeploymentNative.State KemSK)
    (outcome : X × SnapshotState Index KemSK)
    (supported : outcome ∈ support (PqxdhDeploymentSessionSnapshots.run
      (PqxdhDeploymentSecrecy.handler setup codec checks route seed bounds) stop program
        (PqxdhDeploymentSecrecy.Ledger.empty, native))) : Consistent outcome.2 :=
  program_consistent setup codec checks route seed bounds stop program _ (initial_consistent native) outcome supported

/-- Constructor-aware linkage and coverage for the actual instrumented source14 game, retaining the complete original suffix. -/
theorem instrumented_facts (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds)
    (count : Nat) (adversary : OracleComp FullSpec X) (runtime afterRuntime : A)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (value : X)
    (final : PqxdhDeploymentCausalPublication.Snapshots count KemSK)
    (reached : (some (created, value, final), afterRuntime) ∈ support
      ((PqxdhDeploymentCausalPublication.instrumented setup codec checks route ensureInit bounds count adversary).run runtime)) :
    Consistent final ∧ PqxdhDeploymentSessionSnapshotCoverage.Covered
      (fun ordinal : Fin count => PqxdhDeploymentCausalPublication.stopAt ordinal.val) final := by
  simp only [PqxdhDeploymentCausalPublication.instrumented, StateT.run, mem_support_bind_iff] at reached
  obtain ⟨born, _, continued⟩ := reached
  cases constructed : born.1 with
  | none => simp [constructed] at continued
  | some generated =>
      simp only [constructed, support_map] at continued
      obtain ⟨returned, supported, same⟩ := continued
      have finalSame : returned.2 = final := congrArg
        (fun result : PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
          PqxdhDeploymentCausalPublication.Snapshots count KemSK => result.2.2)
        (Option.some.inj (congrArg Prod.fst same))
      exact finalSame ▸
        ⟨run_consistent setup codec checks route generated.seed bounds
          (fun ordinal : Fin count => PqxdhDeploymentCausalPublication.stopAt ordinal.val)
          adversary (PqxdhDeploymentNative.initial generated) returned supported,
        PqxdhDeploymentSessionSnapshotCoverage.run_covered
          (PqxdhDeploymentSecrecy.handler setup codec checks route generated.seed bounds)
          (fun ordinal : Fin count => PqxdhDeploymentCausalPublication.stopAt ordinal.val)
          adversary (PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial generated)
          (fun ordinal => PqxdhDeploymentCausalPublication.stopAt_empty ordinal.val) returned supported⟩

end BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.ledger_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.ledger_records

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.handler_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.handler_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.handler_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.handler_records

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.advance_consistent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.advance_consistent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.program_consistent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.initial_consistent' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.initial_consistent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.run_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.run_consistent

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.instrumented_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage.instrumented_facts
