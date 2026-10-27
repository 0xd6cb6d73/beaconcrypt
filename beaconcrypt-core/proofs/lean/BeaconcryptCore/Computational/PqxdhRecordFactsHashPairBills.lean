-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache

/-! Joint digest-class accounting over the same complete adaptive continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills
open PqxdhRecordFactsCollision PqxdhRecordFactsCollisionOracle
variable {Input Digest X : Type}

/-- Classify an actual query before its reply; finite coins belong to neither digest class. -/
def classQuery (target : Input → Bool) (kind : Bool) : Input ⊕ unifSpec.Domain → Bool
  | .inl input => target input == kind
  | .inr _ => false

/-- Separate all-reply caps for the same adaptive client imply the paired budget used by the collision experiment. -/
theorem pair_bound (target : Input → Bool) (client : OracleComp (Spec Input Digest) X)
    (privateCap ordinaryCap : Nat)
    (privateBound : client.IsQueryBoundP (fun query => classQuery target true query) privateCap)
    (ordinaryBound : client.IsQueryBoundP (fun query => classQuery target false query) ordinaryCap) :
    client.IsQueryBound (privateCap, ordinaryCap) (fun query => enabled (drawClass target query))
      (fun query => debit (drawClass target query)) := by
  induction client using OracleComp.inductionOn generalizing privateCap ordinaryCap with
  | pure value => exact isQueryBound_pure _ _ _ _
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at privateBound ordinaryBound
      rw [isQueryBound_query_bind_iff]
      cases query with
      | inl input =>
          cases selected : target input <;>
            simp [classQuery, selected, drawClass, enabled, debit] at privateBound ordinaryBound ⊢
          · refine ⟨ordinaryBound.1, fun reply => ?_⟩
            simpa [classQuery, drawClass] using ih reply privateCap (ordinaryCap - 1)
              (by simpa [classQuery] using privateBound reply)
              (by simpa [classQuery] using ordinaryBound.2 reply)
          · refine ⟨privateBound.1, fun reply => ?_⟩
            simpa [classQuery, drawClass] using ih reply (privateCap - 1) ordinaryCap
              (by simpa [classQuery] using privateBound.2 reply)
              (by simpa [classQuery] using ordinaryBound reply)
      | inr coin =>
          exact ⟨True.intro, fun reply => ih reply privateCap ordinaryCap
            (by simpa [classQuery] using privateBound.2 reply)
            (by simpa [classQuery] using ordinaryBound.2 reply)⟩

/-- The actual memoized 512-bit digest cache obeys the two scalar source caps over the identical adaptive client. -/
theorem ctx_collision_bound [DecidableEq Input] (target : Input → Bool)
    (client : OracleComp (Spec Input CtxRomAuth.CtxDigest) X) (privateCap ordinaryCap : Nat)
    (privateBound : client.IsQueryBoundP (fun query => classQuery target true query) privateCap)
    (ordinaryBound : client.IsQueryBoundP (fun query => classQuery target false query) ordinaryCap) :
    𝒟[(fun result : X × Cache Input CtxRomAuth.CtxDigest =>
      @decide (PqxdhRecordFactsCollisionCache.Collision target result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run ∅] {true} ≤
      ((privateCap * (privateCap + ordinaryCap) : Nat) : ENNReal) / (2 : ENNReal)^512 :=
  PqxdhRecordFactsCollisionCache.ctx_cache_collision_bound target client privateCap ordinaryCap
    (pair_bound target client privateCap ordinaryCap privateBound ordinaryBound)

end BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills.pair_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills.pair_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills.ctx_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills.ctx_collision_bound

