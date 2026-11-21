-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicRootFrame
import BeaconcryptCore.Computational.RegistrationNativeRetainedSource

/-! The concrete ordinary components have a proved zero-root footprint. Their local coin interpreter therefore preserves the private root-cache state exactly; its unused fallback replies carry no selected secret. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicRootCoins
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativePublicRootFrame (IsRoot)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle)
variable {Value : Type}

/-- Fallback root replies are unreachable for the ordinary components, by their structural query bounds. -/
def localImpl (hmac : HmacSha512) : QueryImpl RootSpec ProbComp
  | .inl coin => unifSpec.query coin
  | .inr (.sign _) => pure (List.Vector.replicate 64 0)
  | .inr (.publicHmac key message) => pure (hmac.eval key message)
  | .inr (.derive _) => pure none

/-- Equality on actual uniform queries suffices for a component with a proved zero-root footprint. -/
theorem uniform_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RootSpec m)
    (same : ∀ coin, left (.inl coin) = right (.inl coin))
    (work : OracleComp RootSpec Value) (free : work.IsQueryBoundP IsRoot 0) :
    simulateQ left work = simulateQ right work := by
  have allowed : work.AllQueriesSatisfy (fun query => ¬ IsRoot query) :=
    (isQueryBoundP_zero_iff work _).1 ((isQueryBoundP_congr_pred fun _ => not_not.symm).1 free)
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      cases query with
      | inl coin =>
          simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
            monadLift_self, same coin]
          exact bind_congr fun reply => ih reply (by
            simpa only [not_not] using
              ((isQueryBoundP_zero_iff (next reply) (fun query => ¬ IsRoot query)).2 (allowed.2 reply))) (allowed.2 reply)
      | inr query => exact (allowed.1 trivial).elim

/-- Actual ideal-root interpretation of ordinary work retains the entire private cache and forwards the original coins. -/
theorem root_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RootSpec Value) (free : work.IsQueryBoundP IsRoot 0)
    (cache : HmacOracle.QueryCache) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation source hmac joint dh seed scalar) work).run cache =
      (fun value => (value, cache)) <$> simulateQ (localImpl hmac) work := by
  have equal := uniform_congr
    (RegistrationNativeRootCacheProjection.implementation source hmac joint dh seed scalar)
    ((localImpl hmac).liftTarget (StateT HmacOracle.QueryCache ProbComp)) (fun _ => rfl) work free
  rw [equal]
  rw [simulateQ_liftTarget]
  change (simulateQ (localImpl hmac) work >>= fun value => pure (value, cache)) = _
  exact bind_pure_comp _ _

/-- The retained service also forwards exactly these local draws while preserving both memo and cache. -/
theorem retained_coins (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : ProbComp Value) (before : RegistrationNativeRetainedSource.State) :
    (simulateQ (RegistrationNativeRetainedSource.implementation source hmac input inside)
      (simulateQ (fun coin => (RegistrationNativeRetainedService.Spec.query (.inl coin) :
        OracleComp RegistrationNativeRetainedService.Spec _)) work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have equal : (RegistrationNativeRetainedSource.implementation source hmac input inside).compose
      (fun coin => (RegistrationNativeRetainedService.Spec.query (.inl coin) :
        OracleComp RegistrationNativeRetainedService.Spec _)) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT RegistrationNativeRetainedSource.State ProbComp) := by
    funext coin
    rfl
  rw [equal]
  rw [simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

end BeaconcryptCore.Computational.RegistrationNativePublicRootCoins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootCoins.uniform_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootCoins.uniform_congr
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootCoins.root_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootCoins.root_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRootCoins.retained_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRootCoins.retained_coins
