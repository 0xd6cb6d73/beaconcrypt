-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace
import BeaconcryptCore.Computational.PqxdhDeploymentCompileCaps

/-! The publication audit is bounded by the source program's actual bundle-query budget. Prepared tuples carry strictly increasing global call positions; missing and inactive owners still consume a counter position. These bounds include failed signing/writer attempts and introduce no cleanliness or caller-supplied occurrence bound. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhDeploymentPublicationSuppressionTrace
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Every recorded tuple is before the next public call position, and tuple positions are strictly increasing. -/
def Valid (audit : Audit) : Prop :=
  (∀ occurrence ∈ audit.occurrences, occurrence.ordinal < audit.nextBundle) ∧
    audit.occurrences.Pairwise (fun left right => left.ordinal < right.ordinal)

/-- The empty real audit has no issued tuple or consumed call. -/
theorem valid_empty : Valid Audit.empty := by simp [Valid, Audit.empty]

/-- A call records at most one prepared tuple, at its actual call position, even when it failed. -/
theorem record_valid (audit : Audit) (address index : Nat) (reply : Option Pqxdh.Bytes)
    (tuples : List Phase1KeyTuple) (bounded : tuples.length ≤ 1) (before : Valid audit) :
    Valid (audit.record address index reply tuples) := by
  constructor
  · intro occurrence member
    rcases List.mem_append.mp member with old | added
    · have bound := before.1 occurrence old
      change occurrence.ordinal < audit.nextBundle + 1
      omega
    · obtain ⟨keys, _, same⟩ := List.mem_map.mp added
      subst occurrence
      exact Nat.lt_succ_self _
  · change (audit.occurrences ++ tuples.map (fun keys => (⟨audit.nextBundle, address, index, keys, reply⟩ : Occurrence))).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨before.2, ?_, ?_⟩
    · cases tuples with
      | nil => simp
      | cons first tail =>
        cases tail with
        | nil => simp
        | cons second rest => simp only [List.length_cons] at bounded; omega
    · intro left old right added
      obtain ⟨_, _, same⟩ := List.mem_map.mp added
      subst right
      exact before.1 left old

private theorem issued_length (setup : Setup baseSpec KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option PqxdhJointGapDh.ScalarBytes) :
    (PqxdhRegistrationJointAttemptTrace.issued setup owner generated).length ≤ 1 := by
  unfold PqxdhRegistrationJointAttemptTrace.issued
  cases PqxdhBeaconPhase1Publication.prepare owner generated <;> simp

/-- Every supported literal source bundle audit is one counter increment and at most one prepared tuple append. -/
theorem trace_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) (audit : Audit)
    (result : PqxdhRegistrationJointAttemptTrace.NativeResult KemSK × Audit)
    (supported : result ∈ support (trace setup codec address index owner pool audit)) :
    ∃ tuples : List Phase1KeyTuple, tuples.length ≤ 1 ∧
      result.2 = audit.record address index result.1.1.1 tuples := by
  rw [trace_after] at supported
  cases phase : owner.beacon.phase <;> simp only [phase] at supported
  case fresh =>
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, same⟩ := supported
    subst result
    exact ⟨_, issued_length setup owner (some scalar), rfl⟩
  case freshWithCoins =>
    have same := supported
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    exact ⟨_, issued_length setup owner none, rfl⟩
  all_goals
    have same := supported
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    exact ⟨[], by simp, rfl⟩

/-- Every actual public bundle call increments once, preserving the strict tuple-position invariant. -/
theorem bundle_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) :
    result.2.2.nextBundle = state.2.nextBundle + 1 ∧ (Valid state.2 → Valid result.2.2) := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨rfl, record_valid _ _ _ _ [] (by simp)⟩
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, returnedSupport, same⟩ := supported
    subst result
    have traced : returned.1 ∈ support (trace setup codec address entry.identityIndex entry.owner
        state.1.pool.1 state.2) := by
      rw [← traceLogged_trace setup codec address entry.identityIndex entry.owner state.1.pool.1 state.2
        (state.1.inits address), support_map]
      exact ⟨returned, returnedSupport, rfl⟩
    obtain ⟨tuples, bounded, recorded⟩ := trace_record setup codec address entry.identityIndex entry.owner
      state.1.pool.1 state.2 returned.1 traced
    change returned.1.2.nextBundle = state.2.nextBundle + 1 ∧ (Valid state.2 → Valid returned.1.2)
    rw [recorded]
    exact ⟨rfl, record_valid _ _ _ _ tuples bounded⟩

/-- The original source query class counted by the deployment's transported bundle cap. -/
abbrev IsBundle (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) : Prop :=
  PqxdhRegistrationJointRevealCosts.sourceKind query = .inl 2

/-- The monitor counter advances on precisely the actual source bundle query class. -/
theorem query_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks serverSeed serverIndex query).run state)) :
    result.2.2.nextBundle = state.2.nextBundle + (if IsBundle query then 1 else 0) ∧
      (Valid state.2 → Valid result.2.2) := by
  rcases query with (coin | command) | read
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact ⟨by simp [IsBundle, PqxdhRegistrationJointRevealCosts.sourceKind,
      PqxdhRegistrationSchedule.sourceKind], id⟩
  · cases command
    case bundle address =>
      simpa only [IsBundle, PqxdhRegistrationJointRevealCosts.sourceKind,
        PqxdhRegistrationSchedule.sourceKind, ite_true] using
        bundle_audit setup codec address state result supported
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, same⟩ := supported
      subst result
      exact ⟨by simp [IsBundle, PqxdhRegistrationJointRevealCosts.sourceKind,
        PqxdhRegistrationSchedule.sourceKind], id⟩
  · simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, same⟩ := supported
    subst result
    exact ⟨by simp [IsBundle, PqxdhRegistrationJointRevealCosts.sourceKind], id⟩

/-- Strictly increasing tuple positions also give uniqueness of every recorded global ordinal. -/
theorem ordinal_nodup (audit : Audit) (valid : Valid audit) :
    (audit.occurrences.map Occurrence.ordinal).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  exact valid.2.imp (fun increasing => Nat.ne_of_lt increasing)

/-- A bounded source program gives the actual audit counter bound and strict chronological invariant on every supported outcome. -/
theorem program_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (count : Nat) (bounded : program.IsQueryBoundP (IsBundle (KemSK := KemSK)) count)
    (state : State KemSK) (valid : Valid state.2) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex) program).run state)) :
    Valid result.2.2 ∧ result.2.2.nextBundle ≤ state.2.nextBundle + count := by
  have preserved := run_rel (handler setup codec checks serverSeed serverIndex)
    (fun before after => Valid before.2 → Valid after.2) (fun _ => id)
    (fun _ _ _ first second => second ∘ first)
    (fun query before after member => (query_audit setup codec checks serverSeed serverIndex query before after member).2)
    program state result supported
  have counter := run_count (handler setup codec checks serverSeed serverIndex) (IsBundle (KemSK := KemSK))
    (fun current => current.2.nextBundle)
    (fun query before after member => (query_audit setup codec checks serverSeed serverIndex query before after member).1.le)
    program count bounded state result supported
  exact ⟨preserved valid, counter⟩

/-- The deployment's existing all-reply source budget bounds the actual audit; no occurrence bound is supplied by a caller. -/
theorem compileFull_audit {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty))) :
    Valid result.2.2 ∧ result.2.2.nextBundle ≤ budget.bundle := by
  have bounded := PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary
    budget respects (.inl 2)
  change (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary).IsQueryBoundP
    (IsBundle (KemSK := KemSK)) budget.bundle at bounded
  simpa only [Audit.empty, Nat.zero_add] using program_audit setup codec checks serverSeed serverIndex _
    budget.bundle bounded (native, Audit.empty) valid_empty result supported

/-- Every prepared occurrence of the actual deployment lies below the public bundle-call cap, including failed Fresh attempts. -/
theorem compileFull_occurrence_bound {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary)
    (native : PqxdhRegistrationJointSchedule.State KemSK)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed serverIndex)
      (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)).run (native, Audit.empty)))
    (occurrence : Occurrence) (member : occurrence ∈ result.2.2.occurrences) :
    occurrence.ordinal < budget.bundle := by
  obtain ⟨valid, bounded⟩ := compileFull_audit setup codec checks serverSeed serverIndex route bounds mode adversary
    budget respects native result supported
  exact (valid.1 occurrence member).trans_le bounded

/-- The first matching prepared tuple is selected by its global call ordinal, retaining all earlier failures and repeated messages. -/
theorem earliest_occurrence (audit : Audit) (valid : Valid audit) (matchesMessage : Occurrence → Bool)
    (present : ∃ occurrence ∈ audit.occurrences, matchesMessage occurrence = true) :
    ∃ occurrence ∈ audit.occurrences, occurrence.ordinal < audit.nextBundle ∧ matchesMessage occurrence = true ∧
      ∀ previous ∈ audit.occurrences, previous.ordinal < occurrence.ordinal → matchesMessage previous = false := by
  have witnessed : ∃ ordinal, ∃ occurrence ∈ audit.occurrences,
      occurrence.ordinal = ordinal ∧ matchesMessage occurrence = true := by
    obtain ⟨occurrence, member, matched⟩ := present
    exact ⟨occurrence.ordinal, occurrence, member, rfl, matched⟩
  obtain ⟨occurrence, member, selected, matched⟩ := Nat.find_spec witnessed
  refine ⟨occurrence, member, valid.1 occurrence member, matched, ?_⟩
  intro previous earlier before
  apply Bool.eq_false_iff.mpr
  intro previousMatched
  rw [selected] at before
  exact Nat.find_min witnessed before ⟨previous, earlier, rfl, previousMatched⟩

private theorem map_eq_on_support {Input Output : Type} (work : ProbComp Input) (left right : Input → Output)
    (same : ∀ value ∈ support work, left value = right value) : left <$> work = right <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value =>
    have equal := same value (by simp)
    simp only [map_pure, equal]
  | query_bind query next ih =>
    simp only [map_bind]
    congr 1
    funext reply
    apply ih reply
    intro value member
    apply same value
    exact (mem_support_bind_iff _ _ _).mpr ⟨reply, by simp, member⟩

/-- The original complete source handler with an independent count of all bundle queries, including calls that issue no tuple. -/
noncomputable def countedSource (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) :
    StateT (PqxdhRegistrationJointSchedule.State KemSK × Nat) ProbComp
      ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query) := fun state =>
  (fun outcome => (outcome.1, (outcome.2, state.2 + if IsBundle query then 1 else 0))) <$>
    (PqxdhRegistrationJointServerSchedule.source setup codec checks serverSeed serverIndex query).run state.1

/-- Remove the tuple list while retaining its actual global public-call count. -/
def counterState (state : State KemSK) : PqxdhRegistrationJointSchedule.State KemSK × Nat :=
  (state.1, state.2.nextBundle)

/-- One audit step has exactly the same native reply, full native/private state and query count as independently counting the original source step. -/
theorem query_counter_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK) :
    (fun result => (result.1, counterState result.2)) <$>
        (handler setup codec checks serverSeed serverIndex query).run state =
      (countedSource setup codec checks serverSeed serverIndex query).run (counterState state) := by
  have same := map_eq_on_support ((handler setup codec checks serverSeed serverIndex query).run state)
    (fun result => (result.1, counterState result.2))
    (fun result => (result.1, (result.2.1, state.2.nextBundle + if IsBundle query then 1 else 0)))
    (fun result member => by
      unfold counterState
      rw [(query_audit setup codec checks serverSeed serverIndex query state result member).1])
  rw [same]
  have projected := congrArg
    (fun work => (fun result => (result.1, (result.2, state.2.nextBundle + if IsBundle query then 1 else 0))) <$> work)
    (query_source setup codec checks serverSeed serverIndex query state)
  simpa only [countedSource, counterState, StateT.run, Functor.map_map] using projected

/-- The final audit counter is exactly the independently instrumented source bundle-query count through the same adaptive continuation. -/
theorem program_counter_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    (fun result => (result.1, counterState result.2)) <$>
        (simulateQ (handler setup codec checks serverSeed serverIndex) program).run state =
      (simulateQ (countedSource setup codec checks serverSeed serverIndex) program).run (counterState state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
    simpa only [bind_map_left] using congrArg
      (fun work => work >>= fun result =>
        (simulateQ (countedSource setup codec checks serverSeed serverIndex) (next result.1)).run result.2)
      (query_counter_projection setup codec checks serverSeed serverIndex query state)

/-- Counting from an arbitrary initial position adds exactly that position to the source query count from zero. -/
theorem source_counter_offset (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (native : PqxdhRegistrationJointSchedule.State KemSK) (start offset : Nat) :
    (fun result => (result.1, (result.2.1, result.2.2 + offset))) <$>
        (simulateQ (countedSource setup codec checks serverSeed serverIndex) program).run (native, start) =
      (simulateQ (countedSource setup codec checks serverSeed serverIndex) program).run (native, start + offset) := by
  induction program using OracleComp.inductionOn generalizing native start with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    simp only [countedSource, StateT.run, bind_map_left]
    congr 1
    funext outcome
    simpa only [StateT.run, Nat.add_assoc, Nat.add_comm offset, Nat.add_left_comm offset] using
      ih outcome.1 outcome.2 (start + if IsBundle query then 1 else 0)

/-- The audit's physical-state projection includes precisely its initial position plus the actual source bundle-query count. -/
theorem program_counter_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    (fun result => (result.1, counterState result.2)) <$>
        (simulateQ (handler setup codec checks serverSeed serverIndex) program).run state =
      (fun result => (result.1, (result.2.1, state.2.nextBundle + result.2.2))) <$>
        (simulateQ (countedSource setup codec checks serverSeed serverIndex) program).run (state.1, 0) := by
  rw [program_counter_projection]
  have offset := source_counter_offset setup codec checks serverSeed serverIndex program state.1 0 state.2.nextBundle
  simpa only [counterState, Nat.zero_add, Nat.add_zero, Nat.add_comm] using offset.symm

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.valid_empty' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.valid_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.record_valid' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.record_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.trace_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.trace_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.bundle_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.bundle_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.query_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.query_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.ordinal_nodup' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.ordinal_nodup

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.program_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.program_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.compileFull_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.compileFull_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.compileFull_occurrence_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.compileFull_occurrence_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.query_counter_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.query_counter_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.program_counter_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.program_counter_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.source_counter_offset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.source_counter_offset

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.program_counter_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.program_counter_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.earliest_occurrence' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationAuditBounds.earliest_occurrence
