-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealingAligned

/-!
# AG lift R2, seal side: one successful seal per frame and handle (CE-12 P4 step 3, design-v2 section 7.6)

Two structural facts of every ideal CTX world (`PqxdhRecordLiftIdeal.ctxRun` with every assignment of the replay and random modes and every plaintext replacement), used by the mode-O plaintext lift (`PqxdhDeploymentHeadlinePlain`) to identify the seal that an accepted receive matched (AG, `PqxdhDeploymentHeadlineAgree`) with the seal behind a returned record of the same frame on the same handle:

- Alignment (`ctxRun_aligned`): every successful seal at a label (a material coordinate: slot, direction, position) carries the wire sequence `position + 1` of that label. Every hidden sealing request of the compiled program is source-aligned (`PqxdhRecordFactsOriginSealingAligned.program`), and a private service changes the seal dictionaries at most by prepending one entry, carrying its sealing request's sequence, at the request's own coordinate (`SealEffect`, `service_sealEffect`). `keep_satisfying` is the invariant form of `PqxdhRecordLiftFlat.support_keep_oracle` for a client whose queries all satisfy a predicate.
- One seal per label (`ctxRun_unique`): any two successful seals at one label are equal. The run is traced with its history of sealing coordinates (`PqxdhRecordLiftProtocolHistory.traceService`; `traced_run`: the trace changes neither results nor states); every label's dictionary is at most as long as the number of its occurrences in the history (`Counted`, `counted_step`, `ctxRun_counted`), and on every reply path the source never issues two sealing requests at one coordinate (`PqxdhRecordLiftProtocolHistory.initial_schedule_nodup`).
- `frame_seal_unique`: on a private state with both properties, two successful seals that match one decoded frame at labels of one slot and direction are equal, because alignment makes the two positions equal.

No premise, assumption or contract, and no probability. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginServices
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftWorldProvenance (sealingCoordinates)
open PqxdhRecordFactsOriginSealingAligned (SealingAligned)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhRecordLiftInterface (Environment)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The seal-dictionary effect of one private service: every label keeps its dictionary, except that a hidden sealing may prepend one entry, carrying the sealing request's wire sequence, at its own material coordinate. -/
def SealEffect (query : PqxdhRecordLiftProtocol.Service n) (before after : CtxPrivate n) : Prop :=
  ∀ label, (after.keys label).1.successfulSeals = (before.keys label).1.successfulSeals ∨
    ∃ pending, query = .sealing pending ∧ label = pending.material ∧
      ∃ entry : CtxSuccessfulSeal, entry.input.context.ad.seq = pending.sequence.val ∧
        (after.keys label).1.successfulSeals = entry :: (before.keys label).1.successfulSeals

/-- Every private service of every ideal CTX world has the seal-dictionary effect `SealEffect`. -/
theorem service_sealEffect (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (before : CtxPrivate n)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec query).run before)) :
    SealEffect query before result.2 := by
  cases query
  case sealing pending =>
    obtain ⟨_, unchanged | ⟨width, record, inserted, _, _⟩⟩ :=
      sealing_trace modes ideal replace setup codec pending before result supported
    · exact fun label => Or.inl (unchanged.2.2 label)
    · intro label
      by_cases same : label = pending.material
      · subst same
        exact Or.inr ⟨pending, rfl, rfl, _, rfl, inserted⟩
      · exact Or.inl (congrArg (fun state : KeyEntry => state.1.successfulSeals)
          (PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending before result supported label same))
  case opening pending =>
    exact fun label => Or.inl (opening_seals modes ideal replace setup codec pending before result supported label)
  case lookup coordinate =>
    exact fun label => Or.inl (congrArg (fun keys => (keys label : KeyEntry).1.successfulSeals)
      (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec coordinate before result supported).1)
  case publish tag =>
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      StateT.run, map_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ fun _ => Or.inl rfl
  all_goals first
    | exact fun label => Or.inl (congrArg (fun keys => (keys label : KeyEntry).1.successfulSeals)
        (PqxdhRecordFactsOriginAmbient.environmental_kept modes replace setup codec _ (by trivial) before result
          supported).keys)
    | skip
  all_goals simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  all_goals obtain ⟨inner, reached, rfl⟩ := supported
  all_goals exact fun _ => Or.inl rfl

/-- The invariant form of `support_keep_oracle` for a client all of whose queries satisfy `P`: a state predicate kept by every query satisfying `P` holds at every supported final state. -/
theorem keep_satisfying {ι' ι'' σ α : Type} {spec : OracleSpec ι'} {spec' : OracleSpec ι''}
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (P : ι' → Prop) (B : σ → Prop)
    (keep : ∀ q s, P q → B s → ∀ p ∈ support ((impl q).run s), B p.2) (oa : OracleComp spec α)
    (satisfied : oa.AllQueriesSatisfy P) (s : σ) (hs : B s) :
    ∀ p ∈ support ((simulateQ impl oa).run s), B p.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
      intro p hp
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact hs
  | query_bind q k ih =>
      rw [allQueriesSatisfy_query_bind_iff] at satisfied
      intro p hp
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind] at hp
      obtain ⟨mid, hmid, hp⟩ := (MonadAttach.mem_support_bind).mp hp
      exact ih mid.1 (satisfied.2 mid.1) mid.2 (keep q s satisfied.1 hs mid hmid) p hp

/-- Label/sequence alignment of the seal dictionaries: every successful seal at a label carries the wire sequence `position + 1` of that label. -/
def Aligned (state : CtxPrivate n) : Prop :=
  ∀ label, ∀ entry ∈ (state.keys label).1.successfulSeals, entry.input.context.ad.seq = label.position + 1

/-- A service whose sealing request is source-aligned keeps the alignment. -/
theorem aligned_step (query : PqxdhRecordLiftProtocol.Service n) (before after : CtxPrivate n)
    (aligned : SealingAligned query) (good : Aligned before) (effect : SealEffect query before after) :
    Aligned after := by
  intro label entry member
  rcases effect label with same | ⟨pending, rfl, rfl, added, sequence, inserted⟩
  · exact good label entry (same ▸ member)
  · rw [inserted, List.mem_cons] at member
    rcases member with rfl | member
    · exact sequence.trans aligned
    · exact good _ entry member

/-- The initial private state has empty seal dictionaries. -/
theorem initial_seals (label : Label n) : ((CtxPrivate.initial (n := n)).keys label).1.successfulSeals = [] := rfl

/-- **Alignment.** On every supported outcome of every ideal CTX world, every successful seal at a label carries the wire sequence `position + 1` of that label (`PqxdhRecordFactsOriginSealingAligned.program`). -/
theorem ctxRun_aligned (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    Aligned result.2 :=
  keep_satisfying (ctxInterpreter modes replace setup codec) SealingAligned Aligned
    (fun query state aligned good output reached => aligned_step query state output.2 aligned good
      (service_sealEffect modes ideal replace setup codec query state output reached))
    _ (PqxdhRecordFactsOriginSealingAligned.program env setup.source.crypto codec route serverKid bounds mode adversary)
    CtxPrivate.initial (fun label entry member => by simp [initial_seals] at member) result supported

/-! ### One successful seal per label -/

/-- Tracing a private interpreter with the attempted sealing history changes neither its results nor its private states. -/
theorem traced_run {P α : Type} (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P ProbComp))
    (oa : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) α) (s : P) (past : List (Label n)) :
    (fun p : α × (P × List (Label n)) => (p.1, p.2.1)) <$>
        (simulateQ (PqxdhRecordLiftProtocolHistory.traceService (fun _ => service)) oa).run (s, past) =
      (simulateQ service oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s past with
  | pure a => simp
  | query_bind q k ih =>
      have step : (PqxdhRecordLiftProtocolHistory.traceService (fun _ => service) q).run (s, past) =
          (fun result => (result.1, (result.2, past ++ sealingCoordinates q))) <$> (service q).run s := by
        simp only [PqxdhRecordLiftProtocolHistory.traceService, StateT.run, bind_pure_comp]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, step, map_bind, bind_map_left]
      exact bind_congr fun (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range q × P) => ih result.1 result.2 _

/-- Each label's dictionary holds at most as many successful seals as the traced history has sealing requests at that label. -/
def Counted (state : CtxPrivate n × List (Label n)) : Prop :=
  ∀ label, (state.1.keys label).1.successfulSeals.length ≤ state.2.count label

/-- One service keeps the count: a sealing adds at most one entry at its own coordinate and one occurrence of it to the history. -/
theorem counted_step (query : PqxdhRecordLiftProtocol.Service n) (before after : CtxPrivate n) (past : List (Label n))
    (good : Counted (before, past)) (effect : SealEffect query before after) :
    Counted (after, past ++ sealingCoordinates query) := by
  intro label
  rcases effect label with same | ⟨pending, rfl, rfl, added, _, inserted⟩
  · change (after.keys label).1.successfulSeals.length ≤ (past ++ sealingCoordinates query).count label
    rw [same, List.count_append]
    exact (good label).trans (Nat.le_add_right _ _)
  · change (after.keys pending.material).1.successfulSeals.length ≤
      (past ++ sealingCoordinates (.sealing pending)).count pending.material
    rw [inserted, List.length_cons, List.count_append]
    simp only [sealingCoordinates, List.count_singleton_self]
    exact Nat.add_le_add_right (good _) 1

/-- On every supported outcome of every ideal CTX world, some duplicate-free sealing history bounds every label's dictionary size. -/
theorem ctxRun_counted (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∃ past : List (Label n), past.Nodup ∧ Counted (result.2, past) := by
  have equal := traced_run (ctxInterpreter modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
    CtxPrivate.initial []
  change result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
    (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
      CtxPrivate.initial) at supported
  rw [← equal, support_map] at supported
  obtain ⟨traced, tracedSupported, rfl⟩ := supported
  refine ⟨traced.2.2, PqxdhRecordLiftProtocolHistory.initial_schedule_nodup
    (fun _ => ctxInterpreter modes replace setup codec) codec.frameRead route _ CtxPrivate.initial traced
    tracedSupported, ?_⟩
  exact PqxdhRecordLiftFlat.support_keep_oracle
    (PqxdhRecordLiftProtocolHistory.traceService (fun _ => ctxInterpreter modes replace setup codec)) Counted
    (fun query state good output reached => by
      simp only [PqxdhRecordLiftProtocolHistory.traceService, StateT.run, bind_pure_comp, support_map] at reached
      obtain ⟨inner, innerReached, rfl⟩ := reached
      exact counted_step query state.1 inner.2 state.2 good
        (service_sealEffect modes ideal replace setup codec query state.1 inner innerReached))
    _ (CtxPrivate.initial, []) (fun label => by simp [initial_seals]) traced tracedSupported

/-- Two members of a list of length at most one are equal. -/
theorem eq_of_length_le_one {α : Type} (list : List α) (short : list.length ≤ 1) (first second : α)
    (firstMember : first ∈ list) (secondMember : second ∈ list) : first = second := by
  match list, short with
  | [], _ => cases firstMember
  | [single], _ =>
      rw [List.mem_singleton] at firstMember secondMember
      rw [firstMember, secondMember]
  | _ :: _ :: _, short => simp at short

/-- **One successful seal per label.** On every supported outcome of every ideal CTX world, any two successful seals at one label are equal: the source never issues two sealing requests at one coordinate (`PqxdhRecordLiftProtocolHistory.initial_schedule_nodup`), and each request adds at most one seal. -/
theorem ctxRun_unique (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (label : Label n) (first second : CtxSuccessfulSeal)
    (firstMember : first ∈ (result.2.keys label).1.successfulSeals)
    (secondMember : second ∈ (result.2.keys label).1.successfulSeals) : first = second := by
  obtain ⟨past, nodup, counted⟩ := ctxRun_counted modes ideal replace setup codec route env serverKid bounds mode
    adversary result supported
  exact eq_of_length_le_one _ ((counted label).trans (List.nodup_iff_count_le_one.mp nodup label)) first second
    firstMember secondMember

/-- Two successful seals of one frame at labels of one slot and direction are equal, on every state with aligned and single-entry dictionaries. -/
theorem frame_seal_unique (state : CtxPrivate n) (aligned : Aligned state)
    (unique : ∀ label, ∀ first ∈ (state.keys label).1.successfulSeals, ∀ second ∈ (state.keys label).1.successfulSeals,
      first = second)
    (frame : RawCtxReceive.DecodedFrame) (firstLabel secondLabel : Label n)
    (slotEq : firstLabel.slot = secondLabel.slot) (directionEq : firstLabel.direction = secondLabel.direction)
    (first second : CtxSuccessfulSeal) (firstMember : first ∈ (state.keys firstLabel).1.successfulSeals)
    (secondMember : second ∈ (state.keys secondLabel).1.successfulSeals)
    (firstMatches : PqxdhRecordFactsOriginReplay.Matches frame first)
    (secondMatches : PqxdhRecordFactsOriginReplay.Matches frame second) : first = second := by
  have positions : firstLabel.position = secondLabel.position := by
    have left := aligned firstLabel first firstMember
    have right := aligned secondLabel second secondMember
    have shared := firstMatches.1.symm.trans secondMatches.1
    omega
  have labelEq : firstLabel = secondLabel := by
    obtain ⟨slot, direction, position⟩ := firstLabel
    obtain ⟨slot', direction', position'⟩ := secondLabel
    simp only at slotEq directionEq positions
    subst slotEq directionEq positions
    rfl
  subst labelEq
  exact unique firstLabel first firstMember second secondMember

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.service_sealEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.service_sealEffect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.keep_satisfying' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.keep_satisfying

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.aligned_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.aligned_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.initial_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.initial_seals

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.ctxRun_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.ctxRun_aligned

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.traced_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.traced_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.counted_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.counted_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.ctxRun_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.ctxRun_counted

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.eq_of_length_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.eq_of_length_le_one

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.ctxRun_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.ctxRun_unique

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.frame_seal_unique' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePlainUnique.frame_seal_unique
