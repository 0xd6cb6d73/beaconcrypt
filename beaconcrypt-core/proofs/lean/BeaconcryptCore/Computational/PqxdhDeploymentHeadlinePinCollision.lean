-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhCtxBirthdayPotential
import BeaconcryptCore.Computational.PqxdhTranscriptAd
import BeaconcryptCore.Computational.PqxdhDeploymentInterface
import BeaconcryptCore.Computational.AdaptiveCtxSharedModes

/-!
# Cached transcript receipts for the computational Server-pin row

An installed associated-data value names the digest of a cached registration transcript. Its response identity is the identity that this receipt certifies. Outside a BLAKE2b cache collision, equal installed associated data implies equal certified Server identities. The receipt is internal proof evidence; it is not a new deployment premise.
-/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision
open PqxdhTranscriptAd
open Pqxdh.SessionTranscript

/-- Honest transcript and record hashes, together with the adversary's public hashes. -/
def hashCap (budget : PqxdhDeploymentInterface.Budget) : ℕ :=
  budget.hash + budget.sends + budget.receives + 2 * budget.build + 2 * budget.finish

/-- The birthday term appended to each computational Server-pin target bound. -/
noncomputable def term (budget : PqxdhDeploymentInterface.Budget) : ℝ≥0∞ :=
  ((hashCap budget).choose 2 : ℝ≥0∞) / 2 ^ 512

/-- The Server identity occupies a fixed position measured from the end of the exact transcript, irrespective of the Init fields' lengths. -/
theorem transcript_response_identity (init : InitFields) (response : ResponseFields)
    (valid : response.WellFormed) :
    (((transcript init response).reverse.drop 1128).take 32).reverse = response.identityKey := by
  simp [transcript, encode, List.reverse_append, List.drop_append, valid.identityWidth,
    valid.ephemeralWidth, valid.kemWidth]

/-- A cached registration transcript with well-formed response whose response certifies the indicated Server identity and whose digest assembles to the installed AD. -/
def Receipt (cache : CtxRomAuth.CtxRO.QueryCache) (identity : Pqxdh.Bytes) (ad : AssociatedData) : Prop :=
  ∃ (init : InitFields) (response : ResponseFields) (digest : CtxRomAuth.CtxDigest),
    response.WellFormed ∧ response.identityKey = identity ∧
      cache (query init response) = some digest ∧ ad = adOf digest

/-- A receipt remains valid when the shared BLAKE2b cache grows. -/
theorem Receipt.mono {before after : CtxRomAuth.CtxRO.QueryCache} (grows : before ≤ after)
    {identity : Pqxdh.Bytes} {ad : AssociatedData} (held : Receipt before identity ad) : Receipt after identity ad := by
  obtain ⟨init, response, digest, responseWidth, identityEq, cached, assembled⟩ := held
  exact ⟨init, response, digest, responseWidth, identityEq, grows cached, assembled⟩

/-- Equal AD in one collision-free cache certifies the same Server identity. -/
theorem identity_eq_of_noCollision (cache : CtxRomAuth.CtxRO.QueryCache)
    {left right : Pqxdh.Bytes} {leftAd rightAd : AssociatedData}
    (leftReceipt : Receipt cache left leftAd) (rightReceipt : Receipt cache right rightAd)
    (same : PqxdhRefinement.absBytes leftAd = PqxdhRefinement.absBytes rightAd)
    (collisionFree : ¬ CacheHasCollision cache) : left = right := by
  obtain ⟨li, lr, dl, lrWidth, leftIdentity, leftCached, leftAssembled⟩ := leftReceipt
  obtain ⟨ri, rr, dr, rrWidth, rightIdentity, rightCached, rightAssembled⟩ := rightReceipt
  rw [leftAssembled, rightAssembled] at same
  have transcripts := transcript_eq_of_ad_eq cache leftCached rightCached same collisionFree
  have identities := congrArg (fun input : Pqxdh.Bytes => ((input.reverse.drop 1128).take 32).reverse) transcripts
  simpa only [transcript_response_identity li lr lrWidth, transcript_response_identity ri rr rrWidth,
    leftIdentity, rightIdentity] using identities

open OracleComp.ProgramLogic (wp)
open PqxdhDeploymentHeadlineDctHash (CtxColl drawPotential draw_step size_empty)

/-- One exposed BLAKE2b query spends one reserved birthday read. -/
theorem hash_read (cap : ℕ) (cache : CtxRomAuth.CtxRO.QueryCache) (input : CtxRomAuth.CtxRO.Domain) :
    wp ((CtxRomAuth.ctxRandomOracle input).run cache) (fun result => drawPotential cap 0 result.2) ≤
      drawPotential (cap + 1) 0 cache := by
  have step := draw_step (cap + 1) 0 cache input
  simpa only [PqxdhCtxBirthdayPotential.drawPotential_shift] using step

/-- Hash calls are the right summand of the shared public-coin/hash interface. -/
def isHash : ℕ ⊕ CtxRomAuth.CtxRO.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred isHash
  | .inl _ => isFalse id
  | .inr _ => isTrue True.intro

/-- Every adaptive public-coin/hash program spends only its syntactically bounded hash budget in the birthday potential. -/
theorem hashProgram_potential {X : Type} (work : OracleComp AdaptiveCtxSharedHash.HashSpec X)
    (cap : ℕ) (bounded : work.IsQueryBoundP isHash cap) (cache : CtxRomAuth.CtxRO.QueryCache) :
    wp ((simulateQ AdaptiveCtxSharedHash.hashImpl work).run cache) (fun result => drawPotential 0 0 result.2) ≤
      drawPotential cap 0 cache := by
  refine PqxdhDeploymentHeadlineDctTools.expected_run_bounded AdaptiveCtxSharedHash.hashImpl isHash
    (fun budget state => drawPotential budget 0 state)
    (fun budget state => PqxdhCtxBirthdayPotential.drawPotential_mono_cap (Nat.le_succ budget) 0 state)
    ?_ ?_ work cap bounded cache
  · rintro (coin | input) state budget hashing
    · exact False.elim hashing
    · exact hash_read budget state input
  · rintro (coin | input) state budget notHash
    · rw [AdaptiveCtxSharedModes.hash_uniform_step, OracleComp.ProgramLogic.wp_map]
      exact OracleComp.ProgramLogic.wp_le_const_of_support _ fun _ _ => le_rfl
    · exact False.elim (notHash True.intro)

open Classical in
/-- The actual lazy random-oracle cache of a bounded adaptive public-coin/hash program obeys the birthday bound, including repeated queries and failed protocol operations. -/
theorem hashProgram_collision {X : Type} (work : OracleComp AdaptiveCtxSharedHash.HashSpec X)
    (cap : ℕ) (bounded : work.IsQueryBoundP isHash cap) :
    𝒟[(fun result => decide (CacheHasCollision result.2)) <$>
      (simulateQ AdaptiveCtxSharedHash.hashImpl work).run ∅] {true} ≤
      (cap.choose 2 : ℝ≥0∞) / 2 ^ 512 := by
  refine (PqxdhDeploymentHeadlineDctTools.chance_le_expected _ _
    (fun result => drawPotential 0 0 result.2) ?_).trans ?_
  · intro result _ collision
    have collides := (PqxdhCtxBirthdayPotential.cacheHasCollision_iff_ctxColl result.2).1
      (of_decide_eq_true collision)
    simp [drawPotential, collides]
  · refine (hashProgram_potential work cap bounded ∅).trans (le_of_eq ?_)
    simp [drawPotential, CtxColl, size_empty, ENNReal.div_eq_inv_mul, mul_comm]

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.Receipt.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.Receipt.mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.identity_eq_of_noCollision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.identity_eq_of_noCollision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.hash_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.hash_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.hashProgram_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.hashProgram_potential

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.hashProgram_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.hashProgram_collision

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.transcript_response_identity' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinCollision.transcript_response_identity
