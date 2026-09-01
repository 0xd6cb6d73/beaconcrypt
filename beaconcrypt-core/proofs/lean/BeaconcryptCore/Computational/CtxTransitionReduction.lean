import BeaconcryptCore.Model.Pqxdh.Acceptance
import BeaconcryptCore.Computational.CtxReduction

/-!
# Computational CTX reductions at the ideal beacon transition

This module lifts record-opening collision reductions to the actual `Pqxdh.beaconFinish` transition. The win event observes that processing reached a result available only after CTX and AEAD verification, including the two later plaintext-format failures, so it neither misses an admitted record nor counts an earlier protocol error.
-/

open OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CtxTransitionReduction

/-- A bounded sequence number distinct from the honest first record's sequence. -/
structure BeaconWrongSequenceClaim where
  /-- The sequence number substituted into the honest response frame. -/
  sequence : ℕ
  /-- The target differs from the honest first-record sequence. -/
  sequence_ne : sequence ≠ 1
  /-- The target sequence fits in the protocol's 64-bit field. -/
  sequence_lt : sequence < 2 ^ 64

/-- The honest first record, presented to the beacon at the claimed sequence, reaches a post-record outcome. -/
def BeaconWrongSequenceSuccess (h : Pqxdh.HonestRun)
    (claim : BeaconWrongSequenceClaim) : Prop :=
  Pqxdh.BeaconRecordAdmitted
      (Pqxdh.beaconFinish h.c h.beaconInitSent
        { h.response with
          appFrame := { h.response.appFrame with seq := claim.sequence } }).1 = true

/-- The two exact CTX transcripts exposed by a successful reordered-record admission. -/
def beaconWrongSequenceCollisionInputs (h : Pqxdh.HonestRun)
    (claim : BeaconWrongSequenceClaim) : Pqxdh.Bytes × Pqxdh.Bytes :=
  let sourceMaterial := Pqxdh.msgMaterial h.c h.chains.1
  let targetMaterial :=
    Ratchet.msgKeyAt (Pqxdh.ratchetCrypto h.c) h.chains.1 (claim.sequence - 1)
  let tag := (Pqxdh.sealRecord h.c sourceMaterial h.recordAD h.plaintext).tag
  (Pqxdh.ctxPreimage sourceMaterial h.recordAD tag,
    Pqxdh.ctxPreimage targetMaterial ⟨h.ad, claim.sequence, h.sid⟩ tag)

/-- Every admitted reordering of the honest first record yields a BLAKE2b collision. -/
theorem beaconWrongSequenceSuccess_implies_blake2b_collision
    (h : Pqxdh.HonestRun) (hok : h.Ok) (hsid : h.sid < 2 ^ 64)
    (claim : BeaconWrongSequenceClaim)
    (hwin : BeaconWrongSequenceSuccess h claim) :
    let inputs := beaconWrongSequenceCollisionInputs h claim
    inputs.1 ≠ inputs.2 ∧ h.c.blake2b inputs.1 = h.c.blake2b inputs.2 := by
  have hadmitted := h.beaconRecordAdmitted_elim hok
    { h.response.appFrame with seq := claim.sequence } hwin
  rcases hadmitted with ⟨hkey, hnonzero, pt, hopen⟩
  simp only [Pqxdh.HonestRun.response, Pqxdh.HonestRun.frame] at hkey hnonzero hopen
  have hadLength : h.ad.length = 153 :=
    Pqxdh.assocData_length (h.c.edPub_length h.ikSkS) (h.c.edPub_length h.ikSkB)
  have hsourceWf : Pqxdh.RecordWf (Pqxdh.msgMaterial h.c h.chains.1) h.recordAD := by
    apply Pqxdh.recordWf_msgMaterial
    · simpa [Pqxdh.HonestRun.recordAD] using hadLength
    · change 1 < 2 ^ 64
      decide
    · simpa [Pqxdh.HonestRun.recordAD] using hsid
  have htargetWf : Pqxdh.RecordWf
      (Ratchet.msgKeyAt (Pqxdh.ratchetCrypto h.c) h.chains.1 (claim.sequence - 1))
      ⟨h.ad, claim.sequence, h.sid⟩ := by
    apply Pqxdh.recordWf_msgKeyAt
    · exact hadLength
    · exact claim.sequence_lt
    · exact hsid
  have hct : h.sent.1.ct =
      (Pqxdh.sealRecord h.c (Pqxdh.msgMaterial h.c h.chains.1) h.recordAD
        h.plaintext).encode := rfl
  rw [hct] at hopen
  have hcollision :=
    CtxReduction.successful_wrong_sequence_open_yields_blake2b_collision h.c
      hsourceWf htargetWf
      (by simpa [Pqxdh.HonestRun.recordAD] using claim.sequence_ne) hopen
  simpa only [beaconWrongSequenceCollisionInputs, Pqxdh.HonestRun.recordAD] using hcollision

/-- The ideal-model reordered-record admission experiment for one fixed honest run. -/
noncomputable def beaconWrongSequenceExp (h : Pqxdh.HonestRun)
    (adversary : ProbComp BeaconWrongSequenceClaim) : ProbComp Bool := by
  classical
  exact do
    let claim ← adversary
    return decide (BeaconWrongSequenceSuccess h claim)

/-- Probability that the honest first record reaches a post-record outcome at a different sequence. -/
noncomputable def beaconWrongSequenceAdvantage (h : Pqxdh.HonestRun)
    (adversary : ProbComp BeaconWrongSequenceClaim) : ℝ≥0∞ :=
  Pr[= true | beaconWrongSequenceExp h adversary]

/-- The BLAKE2b collision adversary induced by a reordered-record admission adversary. -/
def beaconWrongSequenceCollisionReduction (h : Pqxdh.HonestRun)
    (adversary : ProbComp BeaconWrongSequenceClaim) :
    CollisionResistance.CRAdversary Pqxdh.Bytes :=
  show ProbComp (Pqxdh.Bytes × Pqxdh.Bytes) from do
    let claim ← adversary
    return beaconWrongSequenceCollisionInputs h claim

/-- **Admitting the honest first record at a different sequence is no easier than BLAKE2b collision finding.** The reduction is factor one for a fixed well-formed honest run. -/
theorem beaconWrongSequenceAdvantage_le_blake2b_cr
    (h : Pqxdh.HonestRun) (hok : h.Ok) (hsid : h.sid < 2 ^ 64)
    (adversary : ProbComp BeaconWrongSequenceClaim) :
    beaconWrongSequenceAdvantage h adversary ≤
      CollisionResistance.crAdvantage h.c.blake2b
        (beaconWrongSequenceCollisionReduction h adversary) := by
  unfold beaconWrongSequenceAdvantage beaconWrongSequenceExp
    CollisionResistance.crAdvantage CollisionResistance.crExp
    beaconWrongSequenceCollisionReduction
  simp only [monad_norm]
  refine probOutput_bind_mono fun claim _ => ?_
  apply probOutput_pure_bool_le
  intro hwin
  simp only [decide_eq_true_eq] at hwin ⊢
  exact beaconWrongSequenceSuccess_implies_blake2b_collision h hok hsid claim hwin

/-! ## Pinned-sender precheck -/

/-- A frame whose sender identifier differs from the server identifier pinned in one fixed honest run. -/
structure BeaconWrongSenderClaim (h : Pqxdh.HonestRun) where
  /-- The frame substituted into the otherwise honest response. -/
  frame : Pqxdh.CryptoFrame
  /-- The substituted frame does not name the pinned server. -/
  sender_ne : frame.keyId ≠ h.sid

/-- A wrong-sender frame reaches a post-record outcome in the ideal beacon transition. -/
def BeaconWrongSenderSuccess (h : Pqxdh.HonestRun)
    (claim : BeaconWrongSenderClaim h) : Prop :=
  Pqxdh.BeaconRecordAdmitted
      (Pqxdh.beaconFinish h.c h.beaconInitSent
        { h.response with appFrame := claim.frame }).1 = true

/-- A wrong-sender frame cannot reach CTX: the ideal beacon rejects it at the pinned-sender precheck. -/
theorem beaconWrongSenderSuccess_false (h : Pqxdh.HonestRun) (hok : h.Ok)
    (claim : BeaconWrongSenderClaim h) :
    ¬ BeaconWrongSenderSuccess h claim := by
  intro hwin
  have hadmitted := h.beaconRecordAdmitted_elim hok claim.frame hwin
  exact claim.sender_ne hadmitted.1

/-- The ideal-model wrong-sender admission experiment for one fixed honest run. -/
noncomputable def beaconWrongSenderExp (h : Pqxdh.HonestRun)
    (adversary : ProbComp (BeaconWrongSenderClaim h)) : ProbComp Bool := by
  classical
  exact do
    let claim ← adversary
    return decide (BeaconWrongSenderSuccess h claim)

/-- Probability that a wrong-sender frame reaches a post-record beacon outcome. -/
noncomputable def beaconWrongSenderAdvantage (h : Pqxdh.HonestRun)
    (adversary : ProbComp (BeaconWrongSenderClaim h)) : ℝ≥0∞ :=
  Pr[= true | beaconWrongSenderExp h adversary]

/-- **Wrong-sender admission has exactly zero advantage.** This is an unconditional control-flow result for an honest run, not a reduction to BLAKE2b collision resistance. -/
theorem beaconWrongSenderAdvantage_eq_zero (h : Pqxdh.HonestRun) (hok : h.Ok)
    (adversary : ProbComp (BeaconWrongSenderClaim h)) :
    beaconWrongSenderAdvantage h adversary = 0 := by
  classical
  unfold beaconWrongSenderAdvantage beaconWrongSenderExp
  refine (probOutput_eq_zero_iff _ _).mpr ?_
  intro hmem
  rw [mem_support_bind_iff] at hmem
  rcases hmem with ⟨claim, _, hclaim⟩
  have hdecide : decide (BeaconWrongSenderSuccess h claim) = true := by
    simpa only [support_pure, Set.mem_singleton_iff, eq_comm] using hclaim
  simp only [decide_eq_true_eq] at hdecide
  exact beaconWrongSenderSuccess_false h hok claim hdecide

end BeaconcryptCore.Computational.CtxTransitionReduction
