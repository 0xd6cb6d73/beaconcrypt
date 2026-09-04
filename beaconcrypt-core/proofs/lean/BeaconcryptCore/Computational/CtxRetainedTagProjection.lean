import BeaconcryptCore.Model.Pqxdh.Commit
import VCVio.OracleComp.ProbComp

/-!
# Retained-tag authenticity projection for modified CTX

This module proves the first retained-tag freshness-projection step for BeaconCrypt's modified CTX record layer.
It fixes one key, nonce, and complete record context, compares the candidate against one designated honest seal, and projects every accepted fresh raw `C || T || T*` opening to an accepted fresh retained base `C || T` opening.
The pointwise implication lifts to a factor-one probability inequality over an arbitrary attempt computation.

This is a same-view structural result, not standard nonce-AEAD authenticity.
The attempt computation is not constrained by an encryption oracle, key hiding is not modeled, and the complete `RecordAD` is fixed.
Fixing the context matters because `seq` and `sid` occur in `T*` but not in the base AEAD associated data, so whole-payload freshness across changed outer contexts does not by itself imply base-ciphertext freshness.
-/

open OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CtxRetainedTagProjection

/-- Decoding a sufficiently long raw record and re-encoding the parsed fields recovers the exact input payload. -/
theorem encode_eq_of_decodeRecord_eq_some {payload : Pqxdh.Bytes}
    {record : Pqxdh.RecordCipher} (hdecode : Pqxdh.decodeRecord payload = some record) :
    record.encode = payload := by
  rw [Pqxdh.decodeRecord] at hdecode
  split at hdecode
  · rename_i hlength
    simp only [Option.some.injEq] at hdecode
    subst record
    simp only [Pqxdh.RecordCipher.encode]
    have hindex : payload.length - 80 + 16 = payload.length - 64 := by
      omega
    rw [← hindex, ← List.drop_drop]
    rw [List.append_assoc, List.take_append_drop]
    exact List.take_append_drop (payload.length - 80) payload
  · simp at hdecode

/-- The retained base AEAD ciphertext `C || T`, represented without ambiguous variable-length concatenation. -/
def baseCipher (record : Pqxdh.RecordCipher) : Pqxdh.Bytes × Pqxdh.Bytes :=
  (record.body, record.tag)

/-- One designated honest plaintext and one candidate raw payload with its claimed opening under the fixed material and context. -/
structure FixedMaterialContextAttempt where
  /-- The sole plaintext designated for honest modified-CTX sealing. -/
  honestPlaintext : Pqxdh.Bytes
  /-- The adversary's raw protected-payload forgery. -/
  forgedPayload : Pqxdh.Bytes
  /-- The plaintext claimed for the forged payload. -/
  claimedPlaintext : Pqxdh.Bytes
deriving DecidableEq

/-- The exact honest `C || T || T*` result for the attempt's designated plaintext. -/
def honestCtxOutput (c : Pqxdh.Crypto) (material : Pqxdh.Bytes × Pqxdh.Bytes)
    (ad : Pqxdh.RecordAD) (attempt : FixedMaterialContextAttempt) : Pqxdh.Bytes :=
  (Pqxdh.sealRecord c material ad attempt.honestPlaintext).encode

/-- The retained base `C || T` result underlying the same designated honest seal. -/
def honestBaseOutput (c : Pqxdh.Crypto) (material : Pqxdh.Bytes × Pqxdh.Bytes)
    (ad : Pqxdh.RecordAD) (attempt : FixedMaterialContextAttempt) :
    Pqxdh.Bytes × Pqxdh.Bytes :=
  c.aeadSeal material.1 material.2 ad.bytes attempt.honestPlaintext

/-- An accepted fresh raw modified-CTX opening relative to one designated honest seal under the same fixed material and complete context. -/
def FixedMaterialContextCtxFreshOpening (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attempt : FixedMaterialContextAttempt) : Prop :=
  Pqxdh.openRecord c material ad attempt.forgedPayload =
      some attempt.claimedPlaintext ∧
    attempt.forgedPayload ≠ honestCtxOutput c material ad attempt

/-- The projected accepted fresh base `C || T` opening in the same augmented view.

This is intentionally not standard AEAD authenticity because the computation producing the attempt is not an enforced hidden-key encryption-oracle interaction. -/
def SameViewBaseFreshOpening (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attempt : FixedMaterialContextAttempt) : Prop :=
  ∃ record, Pqxdh.decodeRecord attempt.forgedPayload = some record ∧
    c.aeadOpen material.1 material.2 ad.bytes record.body record.tag =
      some attempt.claimedPlaintext ∧
    baseCipher record ≠ honestBaseOutput c material ad attempt

/-- Successful modified-CTX opening exposes the exact retained base ciphertext and its successful base-AEAD opening. -/
theorem openRecord_success_implies_base_success (c : Pqxdh.Crypto)
    {material : Pqxdh.Bytes × Pqxdh.Bytes} {ad : Pqxdh.RecordAD}
    {payload plaintext : Pqxdh.Bytes}
    (hopen : Pqxdh.openRecord c material ad payload = some plaintext) :
    ∃ record, Pqxdh.decodeRecord payload = some record ∧
      record.commit = Pqxdh.ctxCommit c material ad record.tag ∧
      c.aeadOpen material.1 material.2 ad.bytes record.body record.tag =
        some plaintext := by
  rcases hdecode : Pqxdh.decodeRecord payload with _ | record
  · rw [Pqxdh.openRecord, hdecode] at hopen
    simp at hopen
  · rw [Pqxdh.openRecord, hdecode] at hopen
    simp only [Option.bind_some] at hopen
    by_cases hcommit : record.commit = Pqxdh.ctxCommit c material ad record.tag
    · rw [if_pos hcommit] at hopen
      exact ⟨record, rfl, hcommit, hopen⟩
    · rw [if_neg hcommit] at hopen
      simp at hopen

/-- For fixed material and context, a commitment-valid record whose retained base ciphertext equals the honest base seal is exactly the honest modified-CTX record. -/
theorem valid_record_eq_honest_seal (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (record : Pqxdh.RecordCipher) (plaintext : Pqxdh.Bytes)
    (hcommit : record.commit = Pqxdh.ctxCommit c material ad record.tag)
    (hbase : baseCipher record =
      c.aeadSeal material.1 material.2 ad.bytes plaintext) :
    record = Pqxdh.sealRecord c material ad plaintext := by
  rcases record with ⟨body, tag, commit⟩
  rcases hseal : c.aeadSeal material.1 material.2 ad.bytes plaintext with
    ⟨honestBody, honestTag⟩
  simp only [baseCipher, hseal, Prod.mk.injEq] at hbase
  rcases hbase with ⟨rfl, rfl⟩
  simp only [Pqxdh.sealRecord, hseal]
  simp only at hcommit
  subst commit
  rfl

/-- Under fixed material and complete context, freshness of an accepted modified-CTX payload implies freshness of its retained base `C || T` projection. -/
theorem fixedMaterialContext_ctxFresh_implies_baseFresh (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attempt : FixedMaterialContextAttempt) (record : Pqxdh.RecordCipher)
    (hdecode : Pqxdh.decodeRecord attempt.forgedPayload = some record)
    (hcommit : record.commit = Pqxdh.ctxCommit c material ad record.tag)
    (hfresh : attempt.forgedPayload ≠ honestCtxOutput c material ad attempt) :
    baseCipher record ≠ honestBaseOutput c material ad attempt := by
  intro hbase
  apply hfresh
  have hrecord : record = Pqxdh.sealRecord c material ad attempt.honestPlaintext :=
    valid_record_eq_honest_seal c material ad record attempt.honestPlaintext
      hcommit hbase
  rw [← encode_eq_of_decodeRecord_eq_some hdecode, hrecord]
  rfl

/-- Every accepted fresh modified-CTX opening under fixed material and complete context is an accepted fresh base opening in the same augmented view. -/
theorem fixedMaterialContext_ctxFreshOpening_implies_baseFreshOpening
    (c : Pqxdh.Crypto) (material : Pqxdh.Bytes × Pqxdh.Bytes)
    (ad : Pqxdh.RecordAD) (attempt : FixedMaterialContextAttempt)
    (hwin : FixedMaterialContextCtxFreshOpening c material ad attempt) :
    SameViewBaseFreshOpening c material ad attempt := by
  rcases hwin with ⟨hopen, hfresh⟩
  obtain ⟨record, hdecode, hcommit, hbase⟩ :=
    openRecord_success_implies_base_success c hopen
  exact ⟨record, hdecode, hbase,
    fixedMaterialContext_ctxFresh_implies_baseFresh c material ad attempt record
      hdecode hcommit hfresh⟩

/-- Run an arbitrary same-view attempt computation once and test the fixed-material/context modified-CTX fresh-opening event. -/
noncomputable def fixedMaterialContextCtxFreshOpeningExp (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attemptComputation : ProbComp FixedMaterialContextAttempt) : ProbComp Bool := by
  classical
  exact do
    let attempt ← attemptComputation
    return decide (FixedMaterialContextCtxFreshOpening c material ad attempt)

/-- Probability of an accepted fresh modified-CTX opening relative to one designated honest seal under fixed material and complete context. -/
noncomputable def fixedMaterialContextCtxFreshOpeningProbability (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attemptComputation : ProbComp FixedMaterialContextAttempt) : ℝ≥0∞ :=
  Pr[= true | fixedMaterialContextCtxFreshOpeningExp c material ad attemptComputation]

/-- Test the projected base fresh-opening event against the same augmented attempt computation. -/
noncomputable def sameViewBaseFreshOpeningExp (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attemptComputation : ProbComp FixedMaterialContextAttempt) : ProbComp Bool := by
  classical
  exact do
    let attempt ← attemptComputation
    return decide (SameViewBaseFreshOpening c material ad attempt)

/-- Probability of the projected fresh base opening in the same augmented view, not a standard base-AEAD authenticity advantage. -/
noncomputable def sameViewBaseFreshOpeningProbability (c : Pqxdh.Crypto)
    (material : Pqxdh.Bytes × Pqxdh.Bytes) (ad : Pqxdh.RecordAD)
    (attemptComputation : ProbComp FixedMaterialContextAttempt) : ℝ≥0∞ :=
  Pr[= true | sameViewBaseFreshOpeningExp c material ad attemptComputation]

/-- **Factor-one same-view authenticity projection.** Every fixed-material/context modified-CTX fresh-opening win is a retained-base fresh-opening win pointwise, so probability does not increase under projection. This is not yet a reduction to standard base-AEAD authenticity. -/
theorem fixedMaterialContext_ctxFreshOpeningProbability_le_sameViewBaseFreshOpeningProbability
    (c : Pqxdh.Crypto) (material : Pqxdh.Bytes × Pqxdh.Bytes)
    (ad : Pqxdh.RecordAD)
    (attemptComputation : ProbComp FixedMaterialContextAttempt) :
    fixedMaterialContextCtxFreshOpeningProbability c material ad attemptComputation ≤
      sameViewBaseFreshOpeningProbability c material ad attemptComputation := by
  unfold fixedMaterialContextCtxFreshOpeningProbability
    fixedMaterialContextCtxFreshOpeningExp sameViewBaseFreshOpeningProbability
    sameViewBaseFreshOpeningExp
  refine probOutput_bind_mono fun attempt _ => ?_
  apply probOutput_pure_bool_le
  intro hwin
  simp only [decide_eq_true_eq] at hwin ⊢
  exact fixedMaterialContext_ctxFreshOpening_implies_baseFreshOpening
    c material ad attempt hwin

end BeaconcryptCore.Computational.CtxRetainedTagProjection
