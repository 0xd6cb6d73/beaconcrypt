import BeaconcryptCore.Computational.RawCtxInterpretedReceive
import BeaconcryptCore.Computational.RawCtxOpeningOccurrence

/-!
Opaque selected material does not change the actual receive target or immutable context. These facts hold before every optional callback reply and across every typed private KDF response, including rejected and cached paths. They discharge the source provenance conditions of the scalar challenge opening, without inferring ownership from a key or derivation address.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedOpenScope
open RawCtxInterpretedReceive

def Scope {Material Context : Type} (target : Std.U64) (context : Context) : Effect Material Context → Prop
  | .rejected _ actual => actual = context
  | .kdfRequested pending => pending.target = target ∧ pending.context = context
  | .openRequested pending => RawCtxInterpretedOpening.sequence pending = ok target ∧ pending.context = context

/-- Every actual private response retains the original pending target and immutable context before any opening is attempted. -/
theorem resume_scope {Material Context : Type} (pending : Kdf Material Context) (reply : RatchetChain × Material) :
    Scope pending.target pending.context (normalResume pending reply) := by
  have resumed := normalResume_exact pending reply
  generalize actual : normalResume pending reply = result at resumed ⊢
  clear actual
  simp only [resume, Bind.bind, Aeneas.Std.bind] at resumed
  repeat' split at resumed
  all_goals simp_all only [Scope, RawCtxInterpretedOpening.sequence, rejected, RustM.ok.injEq, reduceCtorEq]
  all_goals subst result
  all_goals first | rfl | exact ⟨rfl, rfl⟩

/-- Actual cached or future admission keeps the decoded target and original context for arbitrary opaque material slots. -/
theorem begin_scope {Material Context : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    Scope target context (normalBegin entry target context) := by
  have begun := normalBegin_exact entry target context
  generalize actual : normalBegin entry target context = result at begun ⊢
  clear actual
  simp only [beginReceive, Bind.bind, Aeneas.Std.bind] at begun
  repeat' split at begun
  all_goals simp_all only [rejected, RustM.ok.injEq, reduceCtorEq]
  all_goals subst result
  all_goals simp only [Scope, RawCtxInterpretedOpening.sequence, RustM.ok.injEq, and_true]
  · exact (refined.prepare_cached_receive_success_inv _ _ _ (by assumption)).sequence_eq.trans
      (RawCtxOwnerProvenance.plan_target _ _ _ _ (by assumption) (by assumption))
  · exact RawCtxOwnerProvenance.plan_target _ _ _ _ (by assumption) (by assumption)

def Outside {Material Context Plaintext : Type} (target : Std.U64) (context : Context) :
    (ReceiveSpec Material Context Plaintext).Domain → Prop
  | .inl _ => False
  | .inr pending => ¬(RawCtxInterpretedOpening.sequence pending = ok target ∧ pending.context = context)

attribute [local instance] Classical.propDecidable

/-- Across every typed private reply and every optional opening outcome, the complete opaque driver makes zero out-of-scope opening calls. -/
theorem program_scoped {Material Context Plaintext : Type} (target : Std.U64) (context : Context)
    (effect : Effect Material Context) (scope : Scope target context effect) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP (Outside (Plaintext := Plaintext) target context) 0 := by
  generalize ranked : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected => simp only [program]; trivial
    | openRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun outside => outside scope), fun _ => by trivial⟩
    | kdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (fun outside => outside), ?_⟩
      intro reply
      simp only [Outside, if_false]
      apply ih _ (ranked ▸ normalResume_rank pending reply) _ _ rfl
      simpa only [scope.1, scope.2] using resume_scope pending reply

/-- Every admitted opaque receive uses only the original decoded target and context, without assumptions on state validity, KDF replies or opening success. -/
theorem receive_scoped {Material Context Plaintext : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    (receive (Plaintext := Plaintext) entry target context).IsQueryBoundP (Outside (Plaintext := Plaintext) target context) 0 :=
  program_scoped target context _ (begin_scope entry target context)

/-- Scoped callback equalities replace the complete opaque receive computation, including every rejected and failed opening branch. -/
theorem program_congr {Material Context Plaintext : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (left right : QueryImpl (ReceiveSpec Material Context Plaintext) m)
    (target : Std.U64) (context : Context)
    (kdf : ∀ request, left (.inl request) = right (.inl request))
    (opening : ∀ pending, RawCtxInterpretedOpening.sequence pending = ok target → pending.context = context →
      left (.inr pending) = right (.inr pending))
    (effect : Effect Material Context) (scope : Scope target context effect) :
    simulateQ left (program effect) = simulateQ right (program effect) := by
  generalize ranked : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected => simp only [program, simulateQ_pure]
    | openRequested pending =>
      simp only [program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [opening pending scope.1 scope.2]
    | kdfRequested pending =>
      simp only [program, simulateQ_bind, simulateQ_spec_query]
      rw [kdf pending.request]
      apply bind_congr
      intro reply
      apply ih _ (ranked ▸ normalResume_rank pending reply) _ _ rfl
      simpa only [scope.1, scope.2] using resume_scope pending reply

/-- Projecting complete callback state commutes with the whole scoped receive. Only actually reached openings need a source equation; every reply and final kernel remain unchanged. -/
theorem program_state {Material Context Plaintext LeftState RightState ι : Type} {base : OracleSpec ι}
    (left : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT LeftState (OracleComp base)))
    (right : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT RightState (OracleComp base)))
    (project : LeftState → RightState) (target : Std.U64) (context : Context)
    (kdf : ∀ request state, (fun result => (result.1, project result.2)) <$> (left (.inl request)).run state =
      (right (.inl request)).run (project state))
    (opening : ∀ pending, RawCtxInterpretedOpening.sequence pending = ok target → pending.context = context →
      ∀ state, (fun result => (result.1, project result.2)) <$> (left (.inr pending)).run state =
        (right (.inr pending)).run (project state))
    (effect : Effect Material Context) (scope : Scope target context effect) (state : LeftState) :
    (fun result => (result.1, project result.2)) <$> (simulateQ left (program effect)).run state =
      (simulateQ right (program effect)).run (project state) := by
  generalize ranked : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect state with
  | h rank ih =>
    cases effect with
    | rejected => simp only [program, simulateQ_pure, StateT.run_pure, map_pure]
    | openRequested pending =>
      simp only [program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      have mapped := congrArg (fun work => work >>= fun result => pure (normalFinish pending result.1, result.2))
        (opening pending scope.1 scope.2 state)
      simpa only [map_bind, map_pure, bind_map_left] using mapped
    | kdfRequested pending =>
      simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      have same : ∀ result : (RatchetChain × Material) × LeftState,
          (fun final => (final.1, project final.2)) <$>
            (simulateQ left (program (normalResume pending result.1))).run result.2 =
          (simulateQ right (program (normalResume pending result.1))).run (project result.2) := by
        intro result
        apply ih _ (ranked ▸ normalResume_rank pending result.1) _ _ _ rfl
        simpa only [scope.1, scope.2] using resume_scope pending result.1
      simp_rw [same]
      have mapped := congrArg (fun work => work >>= fun result =>
        (simulateQ right (program (normalResume pending result.1))).run result.2)
        (kdf pending.request state)
      simpa only [bind_map_left] using mapped

/-- The actual source admission discharges the scope premise in the complete state-projection law for arbitrary cached or future receive executions. -/
theorem receive_state {Material Context Plaintext LeftState RightState ι : Type} {base : OracleSpec ι}
    (left : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT LeftState (OracleComp base)))
    (right : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT RightState (OracleComp base)))
    (project : LeftState → RightState)
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context)
    (kdf : ∀ request state, (fun result => (result.1, project result.2)) <$> (left (.inl request)).run state =
      (right (.inl request)).run (project state))
    (opening : ∀ pending, RawCtxInterpretedOpening.sequence pending = ok target → pending.context = context →
      ∀ state, (fun result => (result.1, project result.2)) <$> (left (.inr pending)).run state =
        (right (.inr pending)).run (project state)) (state : LeftState) :
    (fun result => (result.1, project result.2)) <$> (simulateQ left (receive entry target context)).run state =
      (simulateQ right (receive entry target context)).run (project state) :=
  program_state left right project target context kdf opening _ (begin_scope entry target context) state

end BeaconcryptCore.Computational.RawCtxSelectedOpenScope

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.resume_scope
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.begin_scope
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.program_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.program_scoped
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.receive_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.receive_scoped
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.program_congr
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.program_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.program_state
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedOpenScope.receive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedOpenScope.receive_state
