import BeaconcryptCore.Model.Pqxdh.Commit
import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance

/-!
# Computational reduction for the modified CTX record layer

This module defines the concrete misattribution game for the ideal PQXDH record model and reduces every winning attempt to a collision in that model's `Crypto.blake2b` function.

The adversary returns one raw wire payload and two well-formed explanations consisting of message material, associated data, and plaintext.
It wins when the real `Pqxdh.openRecord` parser and verifier accept both distinct explanations.
The reduction decodes the shared payload and returns the two exact CTX preimages containing its parsed Poly1305 tag.
The reduction is lossless: every CTX win is a collision-resistance win, with no additive term and no AEAD-security assumption.

This is a standard-model reduction to collision resistance, not a proof that deployed BLAKE2b-512 is collision resistant and not a random-oracle replacement of the pure hash in `Pqxdh.Crypto`.
-/

open OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CtxReduction

/-- One well-formed explanation of a record payload. -/
structure CtxExplanation where
  /-- The ChaCha20-Poly1305 key and nonce. -/
  material : Pqxdh.Bytes × Pqxdh.Bytes
  /-- The session bytes, sequence number, and sender identifier. -/
  ad : Pqxdh.RecordAD
  /-- The plaintext claimed by this explanation. -/
  plaintext : Pqxdh.Bytes
  /-- The record context has every protocol-mandated field width. -/
  wf : Pqxdh.RecordWf material ad

/-- An adversarial raw record payload together with two claimed explanations. -/
structure CtxAttempt where
  /-- An arbitrary wire payload, including payloads outside the canonical encoder image. -/
  payload : Pqxdh.Bytes
  /-- The first claimed explanation. -/
  left : CtxExplanation
  /-- The second claimed explanation. -/
  right : CtxExplanation

/-- The modified CTX layer fails to bind when one raw payload opens under two distinct explanations. -/
def CtxMisattribution (c : Pqxdh.Crypto) (attempt : CtxAttempt) : Prop :=
  Pqxdh.openRecord c attempt.left.material attempt.left.ad attempt.payload =
      some attempt.left.plaintext ∧
    Pqxdh.openRecord c attempt.right.material attempt.right.ad attempt.payload =
      some attempt.right.plaintext ∧
    ¬ (attempt.left.material = attempt.right.material ∧
      attempt.left.ad = attempt.right.ad ∧
      attempt.left.plaintext = attempt.right.plaintext)

/-- Extract the candidate CTX collision, returning an equal fallback pair when parsing fails. -/
def ctxCollisionInputs (attempt : CtxAttempt) : Pqxdh.Bytes × Pqxdh.Bytes :=
  match Pqxdh.decodeRecord attempt.payload with
  | none => ([], [])
  | some record =>
      (Pqxdh.ctxPreimage attempt.left.material attempt.left.ad record.tag,
        Pqxdh.ctxPreimage attempt.right.material attempt.right.ad record.tag)

/-- Every accepted pair of distinct explanations maps pointwise to a BLAKE2b collision on the exact parsed CTX transcripts. -/
theorem ctxMisattribution_implies_blake2b_collision (c : Pqxdh.Crypto)
    (attempt : CtxAttempt) (hwin : CtxMisattribution c attempt) :
    let inputs := ctxCollisionInputs attempt
    inputs.1 ≠ inputs.2 ∧ c.blake2b inputs.1 = c.blake2b inputs.2 := by
  rcases hwin with ⟨hleft, hright, hdistinct⟩
  obtain ⟨record, hdecode, hne, heq⟩ :=
    Pqxdh.openRecord_double_opening_yields_ctx_collision c
      attempt.left.wf attempt.right.wf hleft hright hdistinct
  simpa only [ctxCollisionInputs, hdecode] using And.intro hne heq

/-- The CTX misattribution experiment runs the adversary once and tests the ideal model's concrete win event. -/
noncomputable def ctxMisattributionExp (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxAttempt) : ProbComp Bool := by
  classical
  exact do
    let attempt ← adversary
    return decide (CtxMisattribution c attempt)

/-- Probability that an adversary finds one raw payload with two distinct accepted explanations. -/
noncomputable def ctxMisattributionAdvantage (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxAttempt) : ℝ≥0∞ :=
  Pr[= true | ctxMisattributionExp c adversary]

/-- Black-box reduction from a CTX misattribution adversary to a BLAKE2b collision adversary. -/
def ctxCollisionReduction (adversary : ProbComp CtxAttempt) :
    CollisionResistance.CRAdversary Pqxdh.Bytes :=
  show ProbComp (Pqxdh.Bytes × Pqxdh.Bytes) from do
    let attempt ← adversary
    return ctxCollisionInputs attempt

/-- **Modified CTX misattribution is no easier than BLAKE2b collision finding.** The reduction has factor one and loses no probability mass. -/
theorem ctxMisattributionAdvantage_le_blake2b_cr (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxAttempt) :
    ctxMisattributionAdvantage c adversary ≤
      CollisionResistance.crAdvantage c.blake2b (ctxCollisionReduction adversary) := by
  unfold ctxMisattributionAdvantage ctxMisattributionExp
    CollisionResistance.crAdvantage CollisionResistance.crExp ctxCollisionReduction
  simp only [monad_norm]
  refine probOutput_bind_mono fun attempt _ => ?_
  apply probOutput_pure_bool_le
  intro hwin
  simp only [decide_eq_true_eq] at hwin ⊢
  exact ctxMisattribution_implies_blake2b_collision c attempt hwin

/-! ## Relabelling an honestly sealed record -/

/-- Turn two explanations into the relabelling attempt whose payload is an honest seal under the first explanation. -/
def ctxRelabelAttempt (c : Pqxdh.Crypto) (source target : CtxExplanation) : CtxAttempt :=
  { payload :=
      (Pqxdh.sealRecord c source.material source.ad source.plaintext).encode
    left := source
    right := target }

/-- A successful opening under a distinct target context is a win in the general misattribution game. -/
theorem ctxRelabelAttempt_win_of_open (c : Pqxdh.Crypto)
    (source target : CtxExplanation)
    (hcontext : ¬ (source.material = target.material ∧ source.ad = target.ad))
    (hopen : Pqxdh.openRecord c target.material target.ad
      (Pqxdh.sealRecord c source.material source.ad source.plaintext).encode =
        some target.plaintext) :
    CtxMisattribution c (ctxRelabelAttempt c source target) := by
  refine ⟨?_, hopen, ?_⟩
  · exact Pqxdh.openRecord_sealRecord c source.material source.ad source.plaintext
  · rintro ⟨hmaterial, had, _⟩
    apply hcontext
    exact ⟨hmaterial, had⟩

/-- A successful opening of an honestly sealed record under a distinct context exposes an explicit BLAKE2b collision. -/
theorem successful_relabel_yields_blake2b_collision (c : Pqxdh.Crypto)
    (source target : CtxExplanation)
    (hcontext : ¬ (source.material = target.material ∧ source.ad = target.ad))
    (hopen : Pqxdh.openRecord c target.material target.ad
      (Pqxdh.sealRecord c source.material source.ad source.plaintext).encode =
        some target.plaintext) :
    Pqxdh.ctxPreimage source.material source.ad
          (Pqxdh.sealRecord c source.material source.ad source.plaintext).tag ≠
        Pqxdh.ctxPreimage target.material target.ad
          (Pqxdh.sealRecord c source.material source.ad source.plaintext).tag ∧
      c.blake2b (Pqxdh.ctxPreimage source.material source.ad
          (Pqxdh.sealRecord c source.material source.ad source.plaintext).tag) =
        c.blake2b (Pqxdh.ctxPreimage target.material target.ad
          (Pqxdh.sealRecord c source.material source.ad source.plaintext).tag) := by
  have hcollision := ctxMisattribution_implies_blake2b_collision c
    (ctxRelabelAttempt c source target)
    (ctxRelabelAttempt_win_of_open c source target hcontext hopen)
  have htag : (Pqxdh.sealRecord c source.material source.ad source.plaintext).tag.length = 16 :=
    c.aeadSeal_tag_length _ _ _ _
  have hcommit :
      (Pqxdh.sealRecord c source.material source.ad source.plaintext).commit.length = 64 :=
    c.blake2b_length _
  have hdecode := Pqxdh.decodeRecord_encode
    (Pqxdh.sealRecord c source.material source.ad source.plaintext) htag hcommit
  simpa only [ctxCollisionInputs, ctxRelabelAttempt, hdecode] using hcollision

/-- Accepting an honest seal at a different sequence number exposes a concrete collision. -/
theorem successful_wrong_sequence_open_yields_blake2b_collision (c : Pqxdh.Crypto)
    {sourceMaterial targetMaterial : Pqxdh.Bytes × Pqxdh.Bytes} {ad : Pqxdh.RecordAD}
    {plaintext forgedPlaintext : Pqxdh.Bytes} {sequence : ℕ}
    (hw : Pqxdh.RecordWf sourceMaterial ad)
    (hw' : Pqxdh.RecordWf targetMaterial { ad with seq := sequence })
    (hne : sequence ≠ ad.seq)
    (hopen : Pqxdh.openRecord c targetMaterial { ad with seq := sequence }
      (Pqxdh.sealRecord c sourceMaterial ad plaintext).encode = some forgedPlaintext) :
    Pqxdh.ctxPreimage sourceMaterial ad
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag ≠
        Pqxdh.ctxPreimage targetMaterial { ad with seq := sequence }
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag ∧
      c.blake2b
          (Pqxdh.ctxPreimage sourceMaterial ad
            (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag) =
        c.blake2b (Pqxdh.ctxPreimage targetMaterial { ad with seq := sequence }
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag) := by
  let source : CtxExplanation :=
    { material := sourceMaterial, ad := ad, plaintext := plaintext, wf := hw }
  let target : CtxExplanation :=
    { material := targetMaterial
      ad := { ad with seq := sequence }
      plaintext := forgedPlaintext
      wf := hw' }
  have hcontext : ¬ (source.material = target.material ∧ source.ad = target.ad) := by
    rintro ⟨_, had⟩
    apply hne
    exact (congrArg Pqxdh.RecordAD.seq had).symm
  simpa only [source, target] using
    successful_relabel_yields_blake2b_collision c source target hcontext hopen

/-- Accepting an honest seal under a different sender identifier exposes a concrete collision. -/
theorem successful_wrong_sender_open_yields_blake2b_collision (c : Pqxdh.Crypto)
    {sourceMaterial targetMaterial : Pqxdh.Bytes × Pqxdh.Bytes} {ad : Pqxdh.RecordAD}
    {plaintext forgedPlaintext : Pqxdh.Bytes} {sender : ℕ}
    (hw : Pqxdh.RecordWf sourceMaterial ad)
    (hw' : Pqxdh.RecordWf targetMaterial { ad with sid := sender })
    (hne : sender ≠ ad.sid)
    (hopen : Pqxdh.openRecord c targetMaterial { ad with sid := sender }
      (Pqxdh.sealRecord c sourceMaterial ad plaintext).encode = some forgedPlaintext) :
    Pqxdh.ctxPreimage sourceMaterial ad
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag ≠
        Pqxdh.ctxPreimage targetMaterial { ad with sid := sender }
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag ∧
      c.blake2b
          (Pqxdh.ctxPreimage sourceMaterial ad
            (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag) =
        c.blake2b (Pqxdh.ctxPreimage targetMaterial { ad with sid := sender }
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag) := by
  let source : CtxExplanation :=
    { material := sourceMaterial, ad := ad, plaintext := plaintext, wf := hw }
  let target : CtxExplanation :=
    { material := targetMaterial
      ad := { ad with sid := sender }
      plaintext := forgedPlaintext
      wf := hw' }
  have hcontext : ¬ (source.material = target.material ∧ source.ad = target.ad) := by
    rintro ⟨_, had⟩
    apply hne
    exact (congrArg Pqxdh.RecordAD.sid had).symm
  simpa only [source, target] using
    successful_relabel_yields_blake2b_collision c source target hcontext hopen

/-- Accepting an honest seal under different session associated data exposes a concrete collision. -/
theorem successful_cross_session_open_yields_blake2b_collision (c : Pqxdh.Crypto)
    {sourceMaterial targetMaterial : Pqxdh.Bytes × Pqxdh.Bytes} {ad : Pqxdh.RecordAD}
    {plaintext forgedPlaintext sessionBytes : Pqxdh.Bytes}
    (hw : Pqxdh.RecordWf sourceMaterial ad)
    (hw' : Pqxdh.RecordWf targetMaterial { ad with bytes := sessionBytes })
    (hne : sessionBytes ≠ ad.bytes)
    (hopen : Pqxdh.openRecord c targetMaterial { ad with bytes := sessionBytes }
      (Pqxdh.sealRecord c sourceMaterial ad plaintext).encode = some forgedPlaintext) :
    Pqxdh.ctxPreimage sourceMaterial ad
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag ≠
        Pqxdh.ctxPreimage targetMaterial { ad with bytes := sessionBytes }
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag ∧
      c.blake2b
          (Pqxdh.ctxPreimage sourceMaterial ad
            (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag) =
        c.blake2b (Pqxdh.ctxPreimage targetMaterial { ad with bytes := sessionBytes }
          (Pqxdh.sealRecord c sourceMaterial ad plaintext).tag) := by
  let source : CtxExplanation :=
    { material := sourceMaterial, ad := ad, plaintext := plaintext, wf := hw }
  let target : CtxExplanation :=
    { material := targetMaterial
      ad := { ad with bytes := sessionBytes }
      plaintext := forgedPlaintext
      wf := hw' }
  have hcontext : ¬ (source.material = target.material ∧ source.ad = target.ad) := by
    rintro ⟨_, had⟩
    apply hne
    exact (congrArg Pqxdh.RecordAD.bytes had).symm
  simpa only [source, target] using
    successful_relabel_yields_blake2b_collision c source target hcontext hopen

/-- A relabelling claim selects an honest source explanation and a distinct target context. -/
structure CtxRelabelClaim where
  /-- The explanation used to seal the record. -/
  source : CtxExplanation
  /-- The distinct explanation under which acceptance is attempted. -/
  target : CtxExplanation
  /-- The target changes the message material or record associated data. -/
  context_ne : ¬ (source.material = target.material ∧ source.ad = target.ad)

/-- Interpret a relabelling claim as a general raw-payload misattribution attempt. -/
def CtxRelabelClaim.toAttempt (c : Pqxdh.Crypto) (claim : CtxRelabelClaim) : CtxAttempt :=
  ctxRelabelAttempt c claim.source claim.target

/-- A relabelling claim succeeds when the target explanation opens the honest source seal. -/
def CtxRelabelSuccess (c : Pqxdh.Crypto) (claim : CtxRelabelClaim) : Prop :=
  Pqxdh.openRecord c claim.target.material claim.target.ad
      (Pqxdh.sealRecord c claim.source.material claim.source.ad claim.source.plaintext).encode =
    some claim.target.plaintext

/-- The ideal-model relabelling experiment. -/
noncomputable def ctxRelabelExp (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxRelabelClaim) : ProbComp Bool := by
  classical
  exact do
    let claim ← adversary
    return decide (CtxRelabelSuccess c claim)

/-- Probability that an honest source seal opens under a distinct target context. -/
noncomputable def ctxRelabelAdvantage (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxRelabelClaim) : ℝ≥0∞ :=
  Pr[= true | ctxRelabelExp c adversary]

/-- **Relabelling an honest seal is no easier than BLAKE2b collision finding.** This specialization also has factor one. -/
theorem ctxRelabelAdvantage_le_blake2b_cr (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxRelabelClaim) :
    ctxRelabelAdvantage c adversary ≤
      CollisionResistance.crAdvantage c.blake2b
        (ctxCollisionReduction (CtxRelabelClaim.toAttempt c <$> adversary)) := by
  unfold ctxRelabelAdvantage ctxRelabelExp
  refine le_trans ?_
    (ctxMisattributionAdvantage_le_blake2b_cr c
      (CtxRelabelClaim.toAttempt c <$> adversary))
  unfold ctxMisattributionAdvantage ctxMisattributionExp
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine probOutput_bind_mono fun claim _ => ?_
  apply probOutput_pure_bool_le
  intro hsuccess
  simp only [decide_eq_true_eq] at hsuccess ⊢
  exact ctxRelabelAttempt_win_of_open c claim.source claim.target claim.context_ne hsuccess

/-! ## Sequence-number relabelling -/

/-- A sequence-number relabelling claim honestly seals one source explanation and attempts to open it at a different sequence number. -/
structure CtxWrongSequenceClaim where
  /-- The explanation used to seal the record. -/
  source : CtxExplanation
  /-- The message material used for the target opening. -/
  targetMaterial : Pqxdh.Bytes × Pqxdh.Bytes
  /-- The plaintext claimed by the target opening. -/
  targetPlaintext : Pqxdh.Bytes
  /-- The sequence number supplied to the target opening. -/
  sequence : ℕ
  /-- The target context has every protocol-mandated field width. -/
  targetWf : Pqxdh.RecordWf targetMaterial { source.ad with seq := sequence }
  /-- The target sequence differs from the honestly sealed sequence. -/
  sequence_ne : sequence ≠ source.ad.seq

/-- Interpret a wrong-sequence claim as a generic relabelling claim. -/
def CtxWrongSequenceClaim.toRelabelClaim (claim : CtxWrongSequenceClaim) :
    CtxRelabelClaim :=
  { source := claim.source
    target :=
      { material := claim.targetMaterial
        ad := { claim.source.ad with seq := claim.sequence }
        plaintext := claim.targetPlaintext
        wf := claim.targetWf }
    context_ne := by
      rintro ⟨_, had⟩
      apply claim.sequence_ne
      exact (congrArg Pqxdh.RecordAD.seq had).symm }

/-- A wrong-sequence claim succeeds when the target opening accepts the honest source seal. -/
def CtxWrongSequenceSuccess (c : Pqxdh.Crypto) (claim : CtxWrongSequenceClaim) : Prop :=
  CtxRelabelSuccess c claim.toRelabelClaim

/-- Every successful wrong-sequence claim exposes the exact BLAKE2b collision used by its relabelling reduction. -/
theorem ctxWrongSequenceSuccess_implies_blake2b_collision (c : Pqxdh.Crypto)
    (claim : CtxWrongSequenceClaim) (hwin : CtxWrongSequenceSuccess c claim) :
    let sealedRecord := Pqxdh.sealRecord c claim.source.material claim.source.ad
      claim.source.plaintext
    Pqxdh.ctxPreimage claim.source.material claim.source.ad sealedRecord.tag ≠
        Pqxdh.ctxPreimage claim.targetMaterial
          { claim.source.ad with seq := claim.sequence } sealedRecord.tag ∧
      c.blake2b (Pqxdh.ctxPreimage claim.source.material claim.source.ad sealedRecord.tag) =
        c.blake2b (Pqxdh.ctxPreimage claim.targetMaterial
          { claim.source.ad with seq := claim.sequence } sealedRecord.tag) := by
  exact successful_wrong_sequence_open_yields_blake2b_collision c
    claim.source.wf claim.targetWf claim.sequence_ne hwin

/-- The ideal-model wrong-sequence experiment. -/
noncomputable def ctxWrongSequenceExp (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSequenceClaim) : ProbComp Bool :=
  ctxRelabelExp c (CtxWrongSequenceClaim.toRelabelClaim <$> adversary)

/-- Probability that an honest source seal opens at a different sequence number. -/
noncomputable def ctxWrongSequenceAdvantage (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSequenceClaim) : ℝ≥0∞ :=
  Pr[= true | ctxWrongSequenceExp c adversary]

/-- The collision adversary induced by a wrong-sequence adversary. -/
def ctxWrongSequenceCollisionReduction (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSequenceClaim) :
    CollisionResistance.CRAdversary Pqxdh.Bytes :=
  ctxCollisionReduction
    (CtxRelabelClaim.toAttempt c <$> (CtxWrongSequenceClaim.toRelabelClaim <$> adversary))

/-- **Opening an honest seal at a different sequence number is no easier than BLAKE2b collision finding.** This specialization preserves the generic reduction's factor-one bound. -/
theorem ctxWrongSequenceAdvantage_le_blake2b_cr (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSequenceClaim) :
    ctxWrongSequenceAdvantage c adversary ≤
      CollisionResistance.crAdvantage c.blake2b
        (ctxWrongSequenceCollisionReduction c adversary) := by
  simpa only [ctxWrongSequenceAdvantage, ctxWrongSequenceExp,
    ctxWrongSequenceCollisionReduction, ctxRelabelAdvantage] using
    ctxRelabelAdvantage_le_blake2b_cr c
      (CtxWrongSequenceClaim.toRelabelClaim <$> adversary)

/-! ## Sender-identifier relabelling -/

/-- A sender-identifier relabelling claim honestly seals one source explanation and attempts to open it under a different sender identifier. -/
structure CtxWrongSenderClaim where
  /-- The explanation used to seal the record. -/
  source : CtxExplanation
  /-- The message material used for the target opening. -/
  targetMaterial : Pqxdh.Bytes × Pqxdh.Bytes
  /-- The plaintext claimed by the target opening. -/
  targetPlaintext : Pqxdh.Bytes
  /-- The sender identifier supplied to the target opening. -/
  sender : ℕ
  /-- The target context has every protocol-mandated field width. -/
  targetWf : Pqxdh.RecordWf targetMaterial { source.ad with sid := sender }
  /-- The target sender identifier differs from the honestly sealed sender identifier. -/
  sender_ne : sender ≠ source.ad.sid

/-- Interpret a wrong-sender claim as a generic relabelling claim. -/
def CtxWrongSenderClaim.toRelabelClaim (claim : CtxWrongSenderClaim) :
    CtxRelabelClaim :=
  { source := claim.source
    target :=
      { material := claim.targetMaterial
        ad := { claim.source.ad with sid := claim.sender }
        plaintext := claim.targetPlaintext
        wf := claim.targetWf }
    context_ne := by
      rintro ⟨_, had⟩
      apply claim.sender_ne
      exact (congrArg Pqxdh.RecordAD.sid had).symm }

/-- A wrong-sender claim succeeds when the target opening accepts the honest source seal. -/
def CtxWrongSenderSuccess (c : Pqxdh.Crypto) (claim : CtxWrongSenderClaim) : Prop :=
  CtxRelabelSuccess c claim.toRelabelClaim

/-- Every successful wrong-sender claim exposes the exact BLAKE2b collision used by its relabelling reduction. -/
theorem ctxWrongSenderSuccess_implies_blake2b_collision (c : Pqxdh.Crypto)
    (claim : CtxWrongSenderClaim) (hwin : CtxWrongSenderSuccess c claim) :
    let sealedRecord := Pqxdh.sealRecord c claim.source.material claim.source.ad
      claim.source.plaintext
    Pqxdh.ctxPreimage claim.source.material claim.source.ad sealedRecord.tag ≠
        Pqxdh.ctxPreimage claim.targetMaterial
          { claim.source.ad with sid := claim.sender } sealedRecord.tag ∧
      c.blake2b (Pqxdh.ctxPreimage claim.source.material claim.source.ad sealedRecord.tag) =
        c.blake2b (Pqxdh.ctxPreimage claim.targetMaterial
          { claim.source.ad with sid := claim.sender } sealedRecord.tag) := by
  exact successful_wrong_sender_open_yields_blake2b_collision c
    claim.source.wf claim.targetWf claim.sender_ne hwin

/-- The ideal-model wrong-sender record-opening experiment. The protocol-level `beaconFinish` path separately rejects sender mismatches before it invokes CTX. -/
noncomputable def ctxWrongSenderExp (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSenderClaim) : ProbComp Bool :=
  ctxRelabelExp c (CtxWrongSenderClaim.toRelabelClaim <$> adversary)

/-- Probability that an honest source seal opens under a different sender identifier at the record layer. -/
noncomputable def ctxWrongSenderAdvantage (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSenderClaim) : ℝ≥0∞ :=
  Pr[= true | ctxWrongSenderExp c adversary]

/-- The collision adversary induced by a wrong-sender record-opening adversary. -/
def ctxWrongSenderCollisionReduction (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSenderClaim) :
    CollisionResistance.CRAdversary Pqxdh.Bytes :=
  ctxCollisionReduction
    (CtxRelabelClaim.toAttempt c <$> (CtxWrongSenderClaim.toRelabelClaim <$> adversary))

/-- **Opening an honest seal under a different sender identifier at the record layer is no easier than BLAKE2b collision finding.** This specialization preserves the generic reduction's factor-one bound. -/
theorem ctxWrongSenderAdvantage_le_blake2b_cr (c : Pqxdh.Crypto)
    (adversary : ProbComp CtxWrongSenderClaim) :
    ctxWrongSenderAdvantage c adversary ≤
      CollisionResistance.crAdvantage c.blake2b
        (ctxWrongSenderCollisionReduction c adversary) := by
  simpa only [ctxWrongSenderAdvantage, ctxWrongSenderExp,
    ctxWrongSenderCollisionReduction, ctxRelabelAdvantage] using
    ctxRelabelAdvantage_le_blake2b_cr c
      (CtxWrongSenderClaim.toRelabelClaim <$> adversary)

end BeaconcryptCore.Computational.CtxReduction
