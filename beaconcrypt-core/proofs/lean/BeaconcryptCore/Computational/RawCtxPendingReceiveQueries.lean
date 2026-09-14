import BeaconcryptCore.Computational.RawCtxChainReceiveBounds

/-!
The receive driver exposes its complete pending KDF payload only to a private internal interpreter. Forwarding that query to the original pending.request erases the added context and gives the exact original recursive source program. Rejected, staged-skip and opening branches retain all fields and optional replies; the same source rank terminates every possible reply continuation. No fuel fallback or target-dependent reconstruction is introduced.

Arbitrary lawful stateful interpretations preserve the complete result and their entire state. Selective query bounds are equivalent on the actual programs, and actual source admission retains at most 51 KDF callbacks and one opening callback. The added private payload is neither a public operation nor a live secret disclosure. These operational laws enable chronological selection of the original pending source request; they do not themselves prove a reached cache miss, uniform response, hidden selected input, alias exclusion or small live exposure. Local callback work is still governed by its original interpreter. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingReceiveQueries
open RawCtxChainReceive RawCtxInterpretedOpening

abbrev Spec (Send Receive Material Context Plaintext : Type) :=
  (Kdf Send Receive Material Context →ₒ (Receive × Material)) +
    (Opening Send Receive Material Context →ₒ core.option.Option Plaintext)

noncomputable def forward {Send Receive Material Context Plaintext : Type} :
    QueryImpl (Spec Send Receive Material Context Plaintext)
      (OracleComp (ReceiveSpec Send Receive Material Context Plaintext))
  | .inl pending => (ReceiveSpec Send Receive Material Context Plaintext).query (.inl pending.request)
  | .inr pending => (ReceiveSpec Send Receive Material Context Plaintext).query (.inr pending)

noncomputable def program {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context) :
    OracleComp (Spec Send Receive Material Context Plaintext)
      (RefinedRatchet Send Receive Material × core.option.Option Plaintext) :=
  match effect with
  | .rejected entry _ => pure (entry, .None)
  | .openRequested pending => do
      let reply ← (Spec Send Receive Material Context Plaintext).query (.inr pending)
      pure (normalFinish pending reply)
  | .kdfRequested pending => do
      let reply ← (Spec Send Receive Material Context Plaintext).query (.inl pending)
      program (normalResume pending reply)
termination_by effectRank effect
decreasing_by exact normalResume_rank _ _

/-- Erasing only the private pending payload yields the same complete original receive computation. -/
theorem program_forward {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context) :
    simulateQ forward (program (Plaintext := Plaintext) effect) = RawCtxChainReceive.program effect := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      simp only [program, RawCtxChainReceive.program, simulateQ_pure]
    | openRequested pending =>
      simp only [program, RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, forward]
      rfl
    | kdfRequested pending =>
      simp only [program, RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, forward]
      exact bind_congr (fun reply => ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl)

def originalQuery {Send Receive Material Context Plaintext : Type} :
    (Spec Send Receive Material Context Plaintext).Domain →
      (ReceiveSpec Send Receive Material Context Plaintext).Domain
  | .inl pending => .inl pending.request
  | .inr pending => .inr pending

set_option backward.isDefEq.respectTransparency false in
/-- Full private query payloads change neither the original selective call class nor its possible reply continuations. -/
theorem query_bound_iff {Send Receive Material Context Plaintext Result : Type}
    (client : OracleComp (Spec Send Receive Material Context Plaintext) Result)
    (predicate : (ReceiveSpec Send Receive Material Context Plaintext).Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    (simulateQ forward client).IsQueryBoundP predicate budget ↔
      client.IsQueryBoundP (fun query => predicate (originalQuery query)) budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
    cases query <;>
      simp only [simulateQ_bind, simulateQ_spec_query, forward,
        isQueryBoundP_query_bind_iff, originalQuery, ih] <;> rfl

/-- The complete enriched source driver has exactly the original all-reply selective budget. -/
theorem program_query_bound {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context)
    (predicate : (ReceiveSpec Send Receive Material Context Plaintext).Domain → Prop)
    [DecidablePred predicate] (budget : Nat) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP (fun query => predicate (originalQuery query)) budget ↔
      (RawCtxChainReceive.program (Plaintext := Plaintext) effect).IsQueryBoundP predicate budget := by
  rw [← query_bound_iff, program_forward]

/-- Any lawful stateful source interpreter runs the same complete receive program after private pending erasure. -/
theorem program_interpreted {Send Receive Material Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (ReceiveSpec Send Receive Material Context Plaintext) m)
    (effect : Effect Send Receive Material Context) :
    simulateQ (impl ∘ₛ forward) (program effect) =
      simulateQ impl (RawCtxChainReceive.program effect) := by
  rw [QueryImpl.simulateQ_compose, program_forward]

/-- Original source admission still permits at most 51 pending KDF callbacks, counting all possible replies. -/
theorem receive_bound {Send Receive Material Context Plaintext : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    (program (Plaintext := Plaintext) (normalBegin kernel target context)).IsQueryBoundP
      (fun request => request.isLeft = true) 51 := by
  convert (program_query_bound (normalBegin kernel target context)
    (fun request => request.isLeft = true) 51).mpr
    (RawCtxChainReceiveBounds.receive_bound (Plaintext := Plaintext) kernel target context) using 1
  funext query
  cases query <;> rfl

/-- Every original effect, including malformed pending states, retains the one-opening callback bound. -/
theorem opening_bound {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isRight = true) 1 := by
  convert (program_query_bound effect (fun request => request.isRight = true) 1).mpr
    (RawCtxChainReceiveBounds.program_open_bound (Plaintext := Plaintext) effect) using 1
  funext query
  cases query <;> rfl

end BeaconcryptCore.Computational.RawCtxPendingReceiveQueries

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.program_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.program_forward

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.query_bound_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.query_bound_iff

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.program_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.program_query_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.program_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.program_interpreted

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.receive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.receive_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.opening_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingReceiveQueries.opening_bound
