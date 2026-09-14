import BeaconcryptCore.Computational.RawCtxSelectedParentPublic
import BeaconcryptCore.Computational.RawCtxSelectedParentSource
import BeaconcryptCore.Computational.RawCtxSelectedLiveCompiler
import BeaconcryptCore.Computational.StatefulGoodEvent

/-!
The live continuation retains one prior full-output lookup and the same predecessor entry through receive, send, public views and actual optional chain/material reads. Its private sticky flag marks either an unavailable current-chain read or a public second32 projection of that predecessor. Masking these direct disclosures preserves the unconditioned event restricted to the good flag, including an already exposed initial state. The source compiler supplies the private pending kernels; an arbitrary primitive client is not itself a proof of source reachability. Byte aliases, earlier disclosure freshness and the reached parent sampler remain separate obligations of the native composition.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentLive
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev View := (query : JointKdfViewQuery) → JointKdfViewSpec.Range query

noncomputable def handler {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl (.inl request) => RawCtxSelectedParentSource.labelReceive source writer prior entry
      (RawCtxKdfRequestTable.fullResponse output) request
  | .inl (.inr (.inl request)) => RawCtxSelectedParentSource.labelSend source writer prior entry
      (RawCtxKdfRequestTable.fullResponse output) request
  | .inl (.inr (.inr (.inr (.inr query)))) => pure (view query)
  | .inl (.inr (.inr (.inr (.inl hash)))) =>
      (RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) (.inr (.inl hash))
  | .inl (.inr (.inr (.inl coin))) =>
      (RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) (.inl coin)
  | .inr query => pure (reader query.1 query.2)

def direct (entry : Entry) : Spec.Domain → Bool
  | .inl (.inr (.inr (.inr (.inr query)))) => publicExposure entry query
  | .inr query => exposed query.1 query.2
  | _ => false

abbrev BaseState (Auxiliary : Type) := RawCtxSharedPrimitive.SharedState Auxiliary × List RootOutput
abbrev State (Auxiliary : Type) := BaseState Auxiliary × Bool

noncomputable def observed {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View) :
    QueryImpl Spec (StateT (State Auxiliary) ProbComp) := fun query state => do
  let result ← (handler source writer prior entry output reader view query).run state.1.1
  pure (result.1, ((result.2, state.1.2 ++ inputs query), state.2 || direct entry query))

/-- Outside either direct disclosure the complete primitive transition is unchanged, including retained prior responses and optional replies. -/
theorem query_safe {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target replacement : RootOutput)
    (query : Spec.Domain) (state : State Auxiliary) (safe : direct entry query = false) :
    (observed source writer prior entry output (nativeReader (RawCtxFreshChainCut.concreteChain target))
      (RawCtxSelectedParentPublic.reply prior entry target) query).run state =
    (observed source writer prior entry output labelRead
      (RawCtxSelectedParentPublic.reply prior entry replacement) query).run state := by
  rcases query with (receive | (send | (coin | (hash | view)))) | read
  all_goals try rfl
  all_goals simp only [observed, handler, StateT.run, nativeReader]
  case inl.inr.inr.inr.inr => rw [RawCtxSelectedParentPublic.before prior entry target replacement view safe]
  case inr => rw [before_exposure read.1 (RawCtxFreshChainCut.concreteChain target) read.2 safe]

/-- Every supported step retains the prior flag and marks exactly this query's direct exposure. -/
theorem flag_step {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (query : Spec.Domain) (state : State Auxiliary) (result : Spec.Range query × State Auxiliary)
    (supported : result ∈ support ((observed source writer prior entry output reader view query).run state)) :
    result.2.2 = (state.2 || direct entry query) := by
  simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Direct disclosure remains marked through every later callback and optional reply. -/
theorem sticky {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (query : Spec.Domain) (state : State Auxiliary) (bad : state.2 = true)
    (result : Spec.Range query × State Auxiliary)
    (supported : result ∈ support ((observed source writer prior entry output reader view query).run state)) :
    result.2.2 = true := by
  simpa only [bad, Bool.true_or] using flag_step source writer prior entry output reader view query state result supported

/-- A disclosure marks the transition even when actual and masked replies differ. -/
theorem hit_marked {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : View)
    (query : Spec.Domain) (state : State Auxiliary) (hit : direct entry query = true)
    (result : Spec.Range query × State Auxiliary)
    (supported : result ∈ support ((observed source writer prior entry output reader view query).run state)) :
    result.2.2 = true := by
  simpa only [hit, Bool.or_true] using flag_step source writer prior entry output reader view query state result supported

/-- Both complete good-output transition distributions agree before either actual direct disclosure. -/
theorem agree_good {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target replacement : RootOutput)
    (query : Spec.Domain) (state : BaseState Auxiliary) (reply : Spec.Range query) (next : BaseState Auxiliary) :
    Pr[= (reply, (next, false)) |
      (observed source writer prior entry output (nativeReader (RawCtxFreshChainCut.concreteChain target))
        (RawCtxSelectedParentPublic.reply prior entry target) query).run (state, false)] =
    Pr[= (reply, (next, false)) |
      (observed source writer prior entry output labelRead
        (RawCtxSelectedParentPublic.reply prior entry replacement) query).run (state, false)] := by
  by_cases hit : direct entry query = true
  · have zero (reader : Reader) (view : View) :
        Pr[= (reply, (next, false)) |
          (observed source writer prior entry output reader view query).run (state, false)] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      exact fun supported => Bool.false_ne_true (hit_marked source writer prior entry output reader view
        query (state, false) hit (reply, (next, false)) supported)
    rw [zero, zero]
  · rw [query_safe source writer prior entry output target replacement query (state, false) (by simpa using hit)]

/-- Masking both direct-disclosure interfaces preserves the same unconditioned good event on the complete adaptive continuation; prior exposure is never reset. -/
theorem event_good {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target replacement : RootOutput)
    (client : OracleComp Spec Result) (state : State Auxiliary) (event : Result × State Auxiliary → Prop) :
    Pr[fun result => event result ∧ result.2.2 = false |
      (simulateQ (observed source writer prior entry output (nativeReader (RawCtxFreshChainCut.concreteChain target))
        (RawCtxSelectedParentPublic.reply prior entry target)) client).run state] =
    Pr[fun result => event result ∧ result.2.2 = false |
      (simulateQ (observed source writer prior entry output labelRead
        (RawCtxSelectedParentPublic.reply prior entry replacement)) client).run state] := by
  exact StatefulGoodEvent.event_good _ _ (agree_good source writer prior entry output target replacement)
    (sticky source writer prior entry output (nativeReader (RawCtxFreshChainCut.concreteChain target))
      (RawCtxSelectedParentPublic.reply prior entry target))
    (sticky source writer prior entry output labelRead (RawCtxSelectedParentPublic.reply prior entry replacement))
    client state event

end BeaconcryptCore.Computational.RawCtxSelectedParentLive

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLive.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLive.query_safe
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLive.flag_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLive.flag_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLive.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLive.sticky
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLive.hit_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLive.hit_marked
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLive.agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLive.agree_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentLive.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentLive.event_good
