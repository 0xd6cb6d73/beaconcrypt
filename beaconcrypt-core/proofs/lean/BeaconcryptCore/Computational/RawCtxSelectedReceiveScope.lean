import BeaconcryptCore.Computational.RawCtxSelectedMessageDriver
import BeaconcryptCore.Computational.RawCtxOwnerProvenance
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer

/-!
Every opening reached by the opaque-material receive driver has the original decoded target and immutable raw context. These are facts about the complete source control flow before an opening reply exists, including rejected or failed openings. They justify the selected CTX callback interface without assuming that any opening succeeds.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedReceiveScope
open RawCtxInterpretedReceive RawCtxInterpretedOpening RawCtxMaterialInterpretation
variable {Material Context Plaintext : Type}

def Scope (target : Std.U64) (context : Context) : Effect Material Context → Prop
  | .rejected _ actual => actual = context
  | .kdfRequested pending => pending.target = target ∧ pending.context = context
  | .openRequested pending => sequence pending = ok target ∧ pending.context = context

/-- Opaque material changes neither the prepared sequence nor the immutable context, even when the interpretation identifies distinct material values. -/
theorem scope_native (value : Material → RatchetMaterial) (target : Std.U64) (context : Context)
    (effect : Effect Material Context) :
    RawCtxOwnerProvenance.Scope target context (nativeEffect (mapEffect value effect)) ↔ Scope target context effect := by
  cases effect with
  | rejected => rfl
  | kdfRequested => rfl
  | openRequested pending =>
    simp only [nativeEffect, mapEffect, RawCtxOwnerProvenance.Scope, Scope, native_sequence, sequence_map]
    rfl

/-- Actual admission preserves the decoded target for every represented kernel, including malformed control and cached-slot states. -/
theorem begin_scope (value : Material → RatchetMaterial)
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    Scope target context (normalBegin kernel target context) := by
  apply (scope_native value target context _).mp
  rw [← normalBegin_map, ← normalBegin_native]
  exact RawCtxOwnerProvenance.oracle_begin_scope _ target context

/-- Every typed derivation reply preserves the prepared target and original context before the next source effect. -/
theorem resume_scope (pending : Kdf Material Context) (reply : RatchetChain × Material) :
    Scope pending.target pending.context (normalResume pending reply) := by
  have actual := normalResume_exact pending reply
  generalize normalResume pending reply = result at actual ⊢
  simp only [resume, Bind.bind, Aeneas.Std.bind] at actual
  repeat' split at actual
  all_goals simp_all only [Scope, RawCtxInterpretedOpening.sequence, rejected, RustM.ok.injEq, reduceCtorEq]
  all_goals subst result
  all_goals first | rfl | exact ⟨rfl, rfl⟩

/-- Full-state callback projection is needed only for reached openings at the original target and context; arbitrary unscoped native clients are not assumed simulatable. -/
theorem program_projection {Small Large : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (project : Large → Small)
    (original : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT Small m))
    (compiled : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT Large m))
    (target : Std.U64) (context : Context)
    (deriveMap : ∀ request state, (original (.inl request)).run (project state) =
      Prod.map id project <$> (compiled (.inl request)).run state)
    (openMap : ∀ pending state, sequence pending = ok target → pending.context = context →
      (original (.inr pending)).run (project state) = Prod.map id project <$> (compiled (.inr pending)).run state)
    (effect : Effect Material Context) (inScope : Scope target context effect) (state : Large) :
    (simulateQ original (program effect)).run (project state) =
      Prod.map id project <$> (simulateQ compiled (program effect)).run state := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
    cases effect with
    | rejected entry actual => simp only [program, simulateQ_pure, StateT.run_pure, map_pure]; rfl
    | openRequested pending =>
      simp only [program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [openMap pending state inScope.1 inScope.2]
      simp only [bind_map_left, map_bind, map_pure, Prod.map_def, id_eq]
    | kdfRequested pending =>
      simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [deriveMap pending.request state]
      simp only [bind_map_left, map_bind, Prod.map_def, id_eq]
      apply bind_congr
      intro result
      exact ih _ (hdepth ▸ normalResume_rank pending result.1) _
        (by simpa only [inScope.1, inScope.2] using resume_scope pending result.1) result.2 rfl

end BeaconcryptCore.Computational.RawCtxSelectedReceiveScope

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.scope_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.scope_native

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.begin_scope

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.resume_scope

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveScope.program_projection
