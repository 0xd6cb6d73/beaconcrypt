import BeaconcryptCore.Computational.RawCtxSelectedParentAliases
import BeaconcryptCore.Computational.RawCtxFlaggedQueryAgreement

/-!
The final-game read mask retains one common public interface on both sides, which can be the actual fixed public HKDF. Only an unavailable current-chain read sets this direct-disclosure flag. Public guesses and accidental aliases remain separate candidate events; they are not freshness exclusions. The complete continuation retains all original private primitive state, candidates and prior exposure. Source reachability and the actual permitted-reveal freshness implication are supplied by the native composition.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentReadMask
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

def direct : Spec.Domain → Bool
  | .inr query => exposed query.1 query.2
  | .inl _ => false

noncomputable def observed {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader) (view : RawCtxSelectedParentLive.View) :=
  RawCtxFlaggedQueryTrace.trace (RawCtxSelectedParentLive.handler (Auxiliary := Auxiliary)
    source writer prior entry output reader view) inputs direct

/-- Every non-exposing callback retains the exact original reply and all effects, including the common real public evaluation. -/
theorem query_safe {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target : RootOutput)
    (view : RawCtxSelectedParentLive.View) (query : Spec.Domain) (safe : direct query = false) :
    RawCtxSelectedParentLive.handler (Auxiliary := Auxiliary) source writer prior entry output
        (nativeReader (RawCtxFreshChainCut.concreteChain target)) view query =
      RawCtxSelectedParentLive.handler source writer prior entry output labelRead view query := by
  cases query with
  | inl query =>
      rcases query with receive | (send | (coin | (hash | view)))
      all_goals rfl
  | inr query =>
      simp only [RawCtxSelectedParentLive.handler, nativeReader,
        before_exposure query.1 (RawCtxFreshChainCut.concreteChain target) query.2 safe]

/-- The original adaptive event and candidate trace agree whenever no hidden current-chain value was disclosed. Public guesses remain in that event. -/
theorem event_good {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (target : RootOutput)
    (view : RawCtxSelectedParentLive.View) (client : OracleComp Spec Result)
    (state : RawCtxSelectedParentLive.State Auxiliary)
    (event : Result × RawCtxSelectedParentLive.State Auxiliary → Prop) :
    Pr{let result ← ((simulateQ (observed source writer prior entry output
        (nativeReader (RawCtxFreshChainCut.concreteChain target)) view) client).run state)}[event result ∧ result.2.2 = false] =
      Pr{let result ← (simulateQ (observed source writer prior entry output labelRead view) client).run state}[event result ∧ result.2.2 = false] := by
  exact RawCtxFlaggedQueryAgreement.event_good _ _ inputs direct
    (query_safe source writer prior entry output target view) client state event

/-- Equal-byte routing is only an intermediate comparison, charged to the original full candidate event with the read-only flag retained. -/
theorem alias_distance {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : Reader)
    (view : RawCtxSelectedParentLive.View) (target : RootOutput)
    (client : OracleComp Spec Result) (state : RawCtxSelectedParentLive.State Auxiliary) :
    tvDist ((simulateQ (observed source writer prior entry output reader view) client).run state)
      ((simulateQ (RawCtxFlaggedQueryTrace.trace
        (RawCtxSelectedParentAliases.consistent source writer prior entry output reader view target)
        inputs direct) client).run state) ≤
      Pr{let result ← (simulateQ (observed source writer prior entry output reader view) client).run state}[target ∈ result.2.1.2].toReal := by
  exact RawCtxFlaggedQueryTrace.distance
    (RawCtxSelectedParentLive.handler source writer prior entry output reader view)
    (RawCtxSelectedParentAliases.alternate source writer prior entry output reader view)
    inputs direct target client state

end BeaconcryptCore.Computational.RawCtxSelectedParentReadMask

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentReadMask.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentReadMask.query_safe
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentReadMask.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentReadMask.event_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentReadMask.alias_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentReadMask.alias_distance
