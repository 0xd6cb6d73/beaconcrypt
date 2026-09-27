import BeaconcryptCore.Computational.PqxdhPrivateSourceCoins

/-!
The private prefix precedes the unchanged actual optional attached-signature acceptance. Complete compiler continuations retain the candidate and source state. The actual field-origin event is transported to the existing joint-use weak-EUF reduction without an honest-selector premise.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports PqxdhPhase1AcceptanceOracle PqxdhJointPhase1AcceptanceComposition
open PqxdhPrivateSourceCoins

structure Outcome (Context : Type) where
  context : Context
  candidate : CandidateReport
  accepted : Option AcceptedInput

/-- All private setup and public selection occurs before the one unchanged actual candidate query. -/
def candidateProgram {Context : Type} (before : OracleComp PrivateSourceSpec (Option (Context × CandidateReport))) :
    OracleComp PrivateSourceSpec (Option (Outcome Context)) := do
  let selected ← before
  match selected with
  | none => pure none
  | some (context, candidate) =>
      let accepted ← publicSource (SourceSpec.query (.inr candidate))
      pure (some ⟨context, candidate, accepted⟩)

/-- Every admitted candidate receives its actual attached-verification result; early setup rejection performs no candidate request. -/
theorem candidateProgram_complete {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (before : OracleComp PrivateSourceSpec (Option (Context × CandidateReport))) (state : BareState count) :
    (simulateQ (privateImpl attachedVerify primitives count) (candidateProgram before)).run state = (do
      let prepared ← (simulateQ (privateImpl attachedVerify primitives count) before).run state
      pure ((prepared.1.map fun chosen =>
        ⟨chosen.1, chosen.2, sourceAccept attachedVerify chosen.2.candidate⟩), prepared.2)) := by
  simp only [candidateProgram, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro prepared
  cases prepared.1 with
  | none => rfl
  | some chosen =>
      simp only [simulateQ_bind, StateT.run_bind, private_public_complete, simulateQ_spec_query]
      rfl

/-- The compiler keeps original candidate bytes and optional reply, with no final public-log change. -/
theorem compiledCandidate_eq {Context : Type}
    (before : OracleComp PrivateSourceSpec (Option (Context × CandidateReport))) (transcript : List Observation) :
    (simulateQ compile (candidateProgram before)).run transcript = (do
      let prepared ← (simulateQ compile before).run transcript
      match prepared.1 with
      | none => pure (none, prepared.2)
      | some (context, candidate) =>
          let accepted ← SourceSpec.query (.inr candidate)
          pure (some ⟨context, candidate, accepted⟩, prepared.2)) := by
  simp only [candidateProgram, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro prepared
  cases prepared.1 with
  | none => rfl
  | some value =>
      simp only [publicSource_query, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rfl

/-- Under any stateful interpretation, the returned acceptance is the actual final candidate call. -/
theorem compiledCandidate_last {Context State : Type}
    (impl : QueryImpl SourceSpec (StateT State ProbComp))
    (before : OracleComp PrivateSourceSpec (Option (Context × CandidateReport))) (transcript finalTranscript : List Observation)
    (state finalState : State) (output : Outcome Context)
    (supported : ((some output, finalTranscript), finalState) ∈ support ((simulateQ impl
      ((simulateQ compile (candidateProgram before)).run transcript)).run state)) :
    ∃ previous, (output.accepted, finalState) ∈ support
      ((impl (.inr output.candidate)).run previous) := by
  rw [compiledCandidate_eq] at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, _, finished⟩ := supported
  cases chosen : prepared.1.1 with
  | none =>
      simp only [chosen, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at finished
  | some value =>
      simp only [chosen, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at finished
      obtain ⟨accepted, step, equality⟩ := finished
      cases equality
      exact ⟨prepared.2, step⟩

/-- Restoring the actual public coin log changes no public identity key, signing history or reveal freshness. -/
theorem restore_snapshot (primitives : Primitives) (count : Nat)
    (state : BareState count) (transcript : List Observation) :
    sourceSnapshot primitives (restoreState state transcript) = sourceSnapshot primitives state := rfl

/-- Actual field-origin detection is computed from the unchanged candidate and actual source histories. -/
def OriginEvent {Context : Type} {count : Nat} (primitives : Primitives)
    (result : Option (Outcome Context) × BareState count) : Prop :=
  ∃ output, result.1 = some output ∧
    candidateAccepted primitives output.candidate (sourceSnapshot primitives result.2) = true

/-- The last source candidate records any field-origin hit before later work, regardless of private coin interleavings. -/
theorem compiledCandidate_recorded {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : Nat) (before : OracleComp PrivateSourceSpec (Option (Context × CandidateReport)))
    (result : (Option (Outcome Context) × List Observation) × CompleteState count)
    (supported : result ∈ support (actualRun attachedVerify primitives count
      ((simulateQ compile (candidateProgram before)).run [])))
    (event : OriginEvent primitives (restore (erase result))) : result.2.1.occurred = true := by
  obtain ⟨output, returned, event⟩ := event
  change result.1.1 = some output at returned
  have snapshot := actualRun_snapshot attachedVerify primitives adapter count _ result supported
  have hit : candidateAccepted primitives output.candidate result.2.1.snapshot = true := by
    rw [snapshot]
    simpa only [restore, erase, restore_snapshot] using event
  have completed : ((some output, result.1.2), result.2) ∈ support
      (actualRun attachedVerify primitives count ((simulateQ compile (candidateProgram before)).run [])) := by
    simpa only [← returned] using supported
  obtain ⟨previous, last⟩ := compiledCandidate_last (acceptanceImpl attachedVerify primitives count)
    before [] result.1.2 _ result.2 output completed
  exact acceptanceCandidate_hit_recorded attachedVerify primitives count output.candidate
    previous (output.accepted, result.2) last hit

/-- All private randomness and source-state history remain on the actual side of the ordinary joint-use reduction. -/
theorem origin_advantage_bound {Context : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : Nat) (before : OracleComp PrivateSourceSpec (Option (Context × CandidateReport)))
    (fallback : DynamicForgery) (ordinaryFallback : Forgery)
    (creates : (candidateProgram before).IsQueryBoundP
      (fun query => IsSourceClass (SourceClass IsCreate) (translated query)) (count + 1)) :
    Pr[OriginEvent primitives | privateRun attachedVerify primitives (count + 1) (candidateProgram before)] ≤
      ∑ target : Fin (count + 1), advantage primitives
        (globalReduction primitives target ordinaryFallback
          (routedAdversary count ordinaryFallback
            (reportExtractor primitives (count + 1) fallback
              (routedClient primitives (count + 1) (instrumentedClient primitives
                ((simulateQ compile (candidateProgram before)).run [])))))) := by
  rw [privateRun_eq, ← actualRun_erase, probEvent_map, probEvent_map]
  have detected := probEvent_mono (fun result supported event =>
    compiledCandidate_recorded attachedVerify primitives adapter (count + 1) before result supported event)
  exact detected.trans (acceptance_advantage_le_sum attachedVerify primitives adapter count _ fallback ordinaryFallback
    (compile_bound (candidateProgram before) _ (count + 1) creates []))

end BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.candidateProgram_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.candidateProgram_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.compiledCandidate_eq' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.compiledCandidate_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.compiledCandidate_last' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.compiledCandidate_last

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.restore_snapshot' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.restore_snapshot

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.compiledCandidate_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.compiledCandidate_recorded

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.origin_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateCandidateAcceptance.origin_advantage_bound
