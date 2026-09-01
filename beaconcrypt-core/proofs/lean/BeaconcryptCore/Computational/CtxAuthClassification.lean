import BeaconcryptCore.Computational.CtxRetainedTagProjection
import VCVio.OracleComp.ProbComp

/-!
# General retained-tag modified-CTX authenticity classification

This module generalizes the fixed-material/context projection to an arbitrary finite history of designated honest seal inputs.
Each entry may use different key and nonce material, complete `RecordAD`, and plaintext, while `RecordWf` restricts every entry and target to the protocol's field widths.
Full CTX freshness is freshness of the complete `(material, RecordAD, C || T || T*)` authentication tuple.
Base-projection freshness is freshness of `(material, RecordAD.bytes, C || T)`, exactly the context visible to the modeled base AEAD.

Because `seq` and `sid` occur in `T*` but not in the base AEAD associated data, full CTX freshness does not imply base-projection freshness for arbitrary histories.
The exhaustive pointwise theorem below exposes the only structural alternative: a prior designated honest input matches the forged base projection but differs in the complete CTX context.
The corresponding probability theorem is a same-view union bound, not a reduction to standard AEAD authenticity; the history is asserted by the attempt rather than enforced by an encryption oracle.
Per-key nonce uniqueness is not imposed here and remains a requirement for the eventual nonce-respecting oracle game.
-/

open OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CtxAuthClassification

open CtxRetainedTagProjection

/-- One well-formed designated honest modified-CTX sealing input. -/
structure CtxSealHistoryEntry where
  /-- The base AEAD key and nonce. -/
  material : Pqxdh.Bytes × Pqxdh.Bytes
  /-- The complete modified-CTX record context. -/
  ad : Pqxdh.RecordAD
  /-- The key, nonce, associated-data bytes, sequence, and sender identifier have the protocol widths. -/
  wf : Pqxdh.RecordWf material ad
  /-- The honestly sealed plaintext. -/
  plaintext : Pqxdh.Bytes
deriving DecidableEq

/-- An arbitrary designated honest history and one candidate raw forgery under its target material and context. -/
structure CtxAuthClassificationAttempt where
  /-- The designated honest sealing inputs. -/
  history : List CtxSealHistoryEntry
  /-- The target base AEAD key and nonce. -/
  targetMaterial : Pqxdh.Bytes × Pqxdh.Bytes
  /-- The target complete modified-CTX context. -/
  targetAD : Pqxdh.RecordAD
  /-- The target key, nonce, associated-data bytes, sequence, and sender identifier have the protocol widths. -/
  targetWf : Pqxdh.RecordWf targetMaterial targetAD
  /-- The candidate raw protected payload. -/
  forgedPayload : Pqxdh.Bytes
  /-- The plaintext claimed for the candidate payload. -/
  claimedPlaintext : Pqxdh.Bytes
deriving DecidableEq

/-- The exact honest `C || T || T*` wire output of one designated input. -/
def CtxSealHistoryEntry.ctxOutput (c : Pqxdh.Crypto)
    (query : CtxSealHistoryEntry) :
    Pqxdh.Bytes :=
  (Pqxdh.sealRecord c query.material query.ad query.plaintext).encode

/-- The retained honest base `C || T` output of one designated input. -/
def CtxSealHistoryEntry.baseOutput (c : Pqxdh.Crypto)
    (query : CtxSealHistoryEntry) :
    Pqxdh.Bytes × Pqxdh.Bytes :=
  c.aeadSeal query.material.1 query.material.2 query.ad.bytes query.plaintext

/-- Freshness of the complete CTX authentication tuple.

Raw wire reuse under a different complete material/context pair remains fresh here and is classified as a context-alias replay. -/
def CtxFullFresh (c : Pqxdh.Crypto) (attempt : CtxAuthClassificationAttempt) : Prop :=
  ∀ query ∈ attempt.history,
    ¬ (query.material = attempt.targetMaterial ∧
      query.ad = attempt.targetAD ∧
      query.ctxOutput c = attempt.forgedPayload)

/-- A prior designated input matches the forgery's retained base projection when it used the same base key, nonce, and associated-data bytes and returned the same `C || T`. -/
def CtxBaseProjectionMatch (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt)
    (query : CtxSealHistoryEntry) (record : Pqxdh.RecordCipher) : Prop :=
  query.material = attempt.targetMaterial ∧
    query.ad.bytes = attempt.targetAD.bytes ∧
    query.baseOutput c = baseCipher record

/-- Freshness of the parsed retained base projection against every matching designated honest input. -/
def CtxBaseProjectionFresh (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt)
    (record : Pqxdh.RecordCipher) : Prop :=
  ∀ query ∈ attempt.history,
    ¬ CtxBaseProjectionMatch c attempt query record

/-- An accepted full-fresh raw modified-CTX forgery. -/
def CtxAcceptedFullFreshForgery (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt) : Prop :=
  Pqxdh.openRecord c attempt.targetMaterial attempt.targetAD attempt.forgedPayload =
      some attempt.claimedPlaintext ∧
    CtxFullFresh c attempt

/-- An accepted fresh retained-base projection in the same augmented view. -/
def CtxFreshAcceptedBaseProjection (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt) : Prop :=
  ∃ record, Pqxdh.decodeRecord attempt.forgedPayload = some record ∧
    c.aeadOpen attempt.targetMaterial.1 attempt.targetMaterial.2
        attempt.targetAD.bytes record.body record.tag =
      some attempt.claimedPlaintext ∧
    CtxBaseProjectionFresh c attempt record

/-- An accepted CTX forgery whose retained base projection reuses a designated honest base output from a different complete CTX context.

The two base contexts agree, so any complete-context difference is confined to fields such as `seq` and `sid` that the base AEAD does not bind. -/
def CtxContextAliasReplay (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt) : Prop :=
  CtxFullFresh c attempt ∧
    ∃ query record, query ∈ attempt.history ∧
    Pqxdh.decodeRecord attempt.forgedPayload = some record ∧
    Pqxdh.openRecord c attempt.targetMaterial attempt.targetAD attempt.forgedPayload =
      some attempt.claimedPlaintext ∧
    c.aeadOpen attempt.targetMaterial.1 attempt.targetMaterial.2
        attempt.targetAD.bytes record.body record.tag =
      some attempt.claimedPlaintext ∧
    CtxBaseProjectionMatch c attempt query record ∧
    ¬ (query.material = attempt.targetMaterial ∧ query.ad = attempt.targetAD)

/-- Every accepted full-fresh modified-CTX forgery is either a fresh accepted retained-base projection or an accepted replay of a designated honest base output across distinct complete CTX contexts. -/
theorem acceptedFullFreshForgery_classification (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt)
    (hwin : CtxAcceptedFullFreshForgery c attempt) :
    CtxFreshAcceptedBaseProjection c attempt ∨
      CtxContextAliasReplay c attempt := by
  rcases hwin with ⟨hopen, hfullFresh⟩
  obtain ⟨record, hdecode, hcommit, hbaseOpen⟩ :=
    openRecord_success_implies_base_success c hopen
  classical
  by_cases hbaseFresh : CtxBaseProjectionFresh c attempt record
  · exact Or.inl ⟨record, hdecode, hbaseOpen, hbaseFresh⟩
  · right
    simp only [CtxBaseProjectionFresh, not_forall, not_not] at hbaseFresh
    obtain ⟨query, hquery, hmatch⟩ := hbaseFresh
    have hcontextDifferent :
        ¬ (query.material = attempt.targetMaterial ∧ query.ad = attempt.targetAD) := by
      intro hsame
      rcases hsame with ⟨hmaterial, had⟩
      apply hfullFresh query hquery
      refine ⟨hmaterial, had, ?_⟩
      have hbaseEq : baseCipher record =
          c.aeadSeal attempt.targetMaterial.1 attempt.targetMaterial.2
            attempt.targetAD.bytes query.plaintext := by
        simpa [CtxSealHistoryEntry.baseOutput, hmaterial, had] using
          hmatch.2.2.symm
      have hrecord : record = Pqxdh.sealRecord c attempt.targetMaterial
          attempt.targetAD query.plaintext :=
        valid_record_eq_honest_seal c attempt.targetMaterial attempt.targetAD
          record query.plaintext hcommit hbaseEq
      calc
        query.ctxOutput c =
            (Pqxdh.sealRecord c attempt.targetMaterial attempt.targetAD
              query.plaintext).encode := by
          simp [CtxSealHistoryEntry.ctxOutput, hmaterial, had]
        _ = record.encode := by rw [← hrecord]
        _ = attempt.forgedPayload := encode_eq_of_decodeRecord_eq_some hdecode
    exact ⟨hfullFresh, query, record, hquery, hdecode, hopen, hbaseOpen, hmatch,
      hcontextDifferent⟩

/-- Every accepted context-alias replay uses two genuinely distinct serialized outer-hash inputs. Protocol-width well-formedness rules out aliases caused only by `LE64` truncation. -/
theorem contextAliasReplay_has_distinct_ctxPreimages (c : Pqxdh.Crypto)
    (attempt : CtxAuthClassificationAttempt)
    (hreplay : CtxContextAliasReplay c attempt) :
    ∃ query record, query ∈ attempt.history ∧
      Pqxdh.decodeRecord attempt.forgedPayload = some record ∧
      CtxBaseProjectionMatch c attempt query record ∧
      Pqxdh.ctxPreimage query.material query.ad record.tag ≠
        Pqxdh.ctxPreimage attempt.targetMaterial attempt.targetAD record.tag := by
  rcases hreplay with
    ⟨_, query, record, hquery, hdecode, _, _, hmatch, hcontextDifferent⟩
  refine ⟨query, record, hquery, hdecode, hmatch, ?_⟩
  have htag : record.tag.length = 16 := by
    rw [Pqxdh.decodeRecord] at hdecode
    split at hdecode
    · cases hdecode
      simp
      omega
    · exact absurd hdecode (by simp)
  intro hpreimage
  obtain ⟨hmaterial, had, _⟩ := Pqxdh.ctxPreimage_inj query.wf
    attempt.targetWf htag htag hpreimage
  exact hcontextDifferent ⟨hmaterial, had⟩

/-- Probability of an accepted full-fresh modified-CTX forgery in an arbitrary same-view attempt computation. -/
noncomputable def ctxAcceptedFullFreshForgeryProbability (c : Pqxdh.Crypto)
    (attemptComputation : ProbComp CtxAuthClassificationAttempt) : ℝ≥0∞ :=
  Pr[fun attempt => CtxAcceptedFullFreshForgery c attempt | attemptComputation]

/-- Probability of a fresh accepted retained-base projection in the same view. -/
noncomputable def ctxFreshAcceptedBaseProjectionProbability (c : Pqxdh.Crypto)
    (attemptComputation : ProbComp CtxAuthClassificationAttempt) : ℝ≥0∞ :=
  Pr[fun attempt => CtxFreshAcceptedBaseProjection c attempt | attemptComputation]

/-- Probability of an accepted context-alias replay in the same view. -/
noncomputable def ctxContextAliasReplayProbability (c : Pqxdh.Crypto)
    (attemptComputation : ProbComp CtxAuthClassificationAttempt) : ℝ≥0∞ :=
  Pr[fun attempt => CtxContextAliasReplay c attempt | attemptComputation]

/-- **Same-view exhaustive union bound.** The probability of an accepted full-fresh modified-CTX forgery is at most the probability of a fresh accepted base projection plus the probability of a context-alias replay. This is a structural classification, not yet a standard AEAD-authenticity or random-oracle bound. -/
theorem ctxAcceptedFullFreshForgeryProbability_le_projection_add_alias
    (c : Pqxdh.Crypto)
    (attemptComputation : ProbComp CtxAuthClassificationAttempt) :
    ctxAcceptedFullFreshForgeryProbability c attemptComputation ≤
      ctxFreshAcceptedBaseProjectionProbability c attemptComputation +
        ctxContextAliasReplayProbability c attemptComputation := by
  unfold ctxAcceptedFullFreshForgeryProbability
    ctxFreshAcceptedBaseProjectionProbability ctxContextAliasReplayProbability
  refine (probEvent_mono'' (mx := attemptComputation)
    (fun attempt hwin => acceptedFullFreshForgery_classification c attempt hwin)).trans ?_
  exact probEvent_or_le attemptComputation
    (fun attempt => CtxFreshAcceptedBaseProjection c attempt)
    (fun attempt => CtxContextAliasReplay c attempt)

end BeaconcryptCore.Computational.CtxAuthClassification
