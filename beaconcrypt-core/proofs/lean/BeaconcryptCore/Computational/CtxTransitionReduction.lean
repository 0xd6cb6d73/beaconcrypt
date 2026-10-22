import BeaconcryptCore.Model.Pqxdh.Acceptance
import BeaconcryptCore.Computational.CtxReduction

/-!
# Computational CTX reductions at the ideal beacon transition

This module lifts record-opening collision reductions to the actual `Pqxdh.beaconFinish` transition. The win event observes record admission after CTX/AEAD opening and the sequence-one policy, including the two subsequent plaintext-format failures. It does not count a successful raw opening rejected by that policy. Wrong-sequence registration advantage is exactly zero; the earlier collision reductions remain valid weaker bounds.
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
  Pr{let x ← beaconWrongSequenceExp h adversary}[x = true]

/-- Registration admission at a non-one sequence has zero advantage by the post-opening policy, even if a raw opening succeeds. -/
theorem beaconWrongSequenceAdvantage_eq_zero (h : Pqxdh.HonestRun)
    (adversary : ProbComp BeaconWrongSequenceClaim) :
    beaconWrongSequenceAdvantage h adversary = 0 := by
  classical
  have noWin : ∀ claim, ¬ BeaconWrongSequenceSuccess h claim :=
    fun claim admitted => claim.sequence_ne (Pqxdh.beaconRecordAdmitted_sequence h.c _ _ admitted)
  have hexp : beaconWrongSequenceExp h adversary =
      (fun claim => decide (BeaconWrongSequenceSuccess h claim)) <$> adversary := by
    simp only [beaconWrongSequenceExp, bind_pure_comp]
  unfold beaconWrongSequenceAdvantage
  rw [hexp, prEvent_map]
  exact prEvent_eq_zero_of_forall_not adversary _ fun claim hwin =>
    noWin claim (of_decide_eq_true hwin)

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
  classical
  have hexp : beaconWrongSequenceExp h adversary =
      (fun claim => decide (BeaconWrongSequenceSuccess h claim)) <$> adversary := by
    simp only [beaconWrongSequenceExp, bind_pure_comp]
  have hcr : CollisionResistance.crExperiment h.c.blake2b
        (beaconWrongSequenceCollisionReduction h adversary) =
      (fun claim => decide ((beaconWrongSequenceCollisionInputs h claim).1 ≠
          (beaconWrongSequenceCollisionInputs h claim).2 ∧
        h.c.blake2b (beaconWrongSequenceCollisionInputs h claim).1 =
          h.c.blake2b (beaconWrongSequenceCollisionInputs h claim).2)) <$> adversary := by
    simp only [CollisionResistance.crExperiment, beaconWrongSequenceCollisionReduction, bind_pure_comp,
      Functor.map_map]
  unfold beaconWrongSequenceAdvantage CollisionResistance.crAdvantage
  rw [← prEvent_eq_evalDist_singleton _ true, hexp, hcr, prEvent_map, prEvent_map]
  refine prEvent_mono adversary _ _ fun claim hwin => ?_
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
  Pr{let x ← beaconWrongSenderExp h adversary}[x = true]

/-- **Wrong-sender admission has exactly zero advantage.** This is an unconditional control-flow result for an honest run, not a reduction to BLAKE2b collision resistance. -/
theorem beaconWrongSenderAdvantage_eq_zero (h : Pqxdh.HonestRun) (hok : h.Ok)
    (adversary : ProbComp (BeaconWrongSenderClaim h)) :
    beaconWrongSenderAdvantage h adversary = 0 := by
  classical
  have hexp : beaconWrongSenderExp h adversary =
      (fun claim => decide (BeaconWrongSenderSuccess h claim)) <$> adversary := by
    simp only [beaconWrongSenderExp, bind_pure_comp]
  unfold beaconWrongSenderAdvantage
  rw [hexp, prEvent_map]
  exact prEvent_eq_zero_of_forall_not adversary _ fun claim hwin =>
    beaconWrongSenderSuccess_false h hok claim (of_decide_eq_true hwin)

/-! ## Foreign-session ciphertext admission -/

/-- A well-formed record sealed under session bytes different from one fixed honest run. -/
structure BeaconCrossSessionClaim (h : Pqxdh.HonestRun) where
  /-- The message key and nonce used for the foreign seal. -/
  material : Pqxdh.Bytes × Pqxdh.Bytes
  /-- The foreign session associated-data bytes. -/
  sessionBytes : Pqxdh.Bytes
  /-- The plaintext placed in the foreign record. -/
  plaintext : Pqxdh.Bytes
  /-- The foreign record context has every protocol-mandated field width. -/
  wf : Pqxdh.RecordWf material ⟨sessionBytes, 1, h.sid⟩
  /-- The honest session bytes differ from the foreign session bytes. -/
  session_ne : h.ad ≠ sessionBytes

/-- The foreign record substituted into an otherwise honest response frame. -/
def BeaconCrossSessionClaim.frame (h : Pqxdh.HonestRun)
    (claim : BeaconCrossSessionClaim h) : Pqxdh.CryptoFrame :=
  { h.response.appFrame with
    cipherText :=
      (Pqxdh.sealRecord h.c claim.material ⟨claim.sessionBytes, 1, h.sid⟩
        claim.plaintext).encode }

/-- A foreign-session ciphertext reaches a post-record outcome in the ideal beacon transition. -/
def BeaconCrossSessionSuccess (h : Pqxdh.HonestRun)
    (claim : BeaconCrossSessionClaim h) : Prop :=
  Pqxdh.BeaconRecordAdmitted
      (Pqxdh.beaconFinish h.c h.beaconInitSent
        { h.response with appFrame := claim.frame h }).1 = true

/-- The exact foreign and honest CTX transcripts exposed by an admitted foreign-session record. -/
def beaconCrossSessionCollisionInputs (h : Pqxdh.HonestRun)
    (claim : BeaconCrossSessionClaim h) : Pqxdh.Bytes × Pqxdh.Bytes :=
  let sourceAd : Pqxdh.RecordAD := ⟨claim.sessionBytes, 1, h.sid⟩
  let targetMaterial := Ratchet.msgKeyAt (Pqxdh.ratchetCrypto h.c) h.chains.1 0
  let tag := (Pqxdh.sealRecord h.c claim.material sourceAd claim.plaintext).tag
  (Pqxdh.ctxPreimage claim.material sourceAd tag,
    Pqxdh.ctxPreimage targetMaterial h.recordAD tag)

/-- Every admitted foreign-session ciphertext yields a BLAKE2b collision. -/
theorem beaconCrossSessionSuccess_implies_blake2b_collision
    (h : Pqxdh.HonestRun) (hok : h.Ok) (claim : BeaconCrossSessionClaim h)
    (hwin : BeaconCrossSessionSuccess h claim) :
    let inputs := beaconCrossSessionCollisionInputs h claim
    inputs.1 ≠ inputs.2 ∧ h.c.blake2b inputs.1 = h.c.blake2b inputs.2 := by
  have hadmitted := h.beaconRecordAdmitted_elim hok (claim.frame h) hwin
  rcases hadmitted with ⟨hkey, hnonzero, pt, hopen⟩
  simp only [BeaconCrossSessionClaim.frame, Pqxdh.HonestRun.response,
    Pqxdh.HonestRun.frame, Nat.reduceSub] at hkey hnonzero hopen
  have hadLength : h.ad.length = 153 :=
    Pqxdh.assocData_length (h.c.edPub_length h.ikSkS) (h.c.edPub_length h.ikSkB)
  have htargetWf : Pqxdh.RecordWf
      (Ratchet.msgKeyAt (Pqxdh.ratchetCrypto h.c) h.chains.1 0) h.recordAD := by
    apply Pqxdh.recordWf_msgKeyAt
    · simpa [Pqxdh.HonestRun.recordAD] using hadLength
    · change 1 < 2 ^ 64
      decide
    · simpa [Pqxdh.HonestRun.recordAD] using claim.wf.sid
  have hcollision :=
    CtxReduction.successful_cross_session_open_yields_blake2b_collision h.c
      claim.wf htargetWf claim.session_ne hopen
  simpa only [beaconCrossSessionCollisionInputs, Pqxdh.HonestRun.recordAD] using hcollision

/-- The ideal-model foreign-session admission experiment for one fixed honest run. -/
noncomputable def beaconCrossSessionExp (h : Pqxdh.HonestRun)
    (adversary : ProbComp (BeaconCrossSessionClaim h)) : ProbComp Bool := by
  classical
  exact do
    let claim ← adversary
    return decide (BeaconCrossSessionSuccess h claim)

/-- Probability that a foreign-session ciphertext reaches a post-record beacon outcome. -/
noncomputable def beaconCrossSessionAdvantage (h : Pqxdh.HonestRun)
    (adversary : ProbComp (BeaconCrossSessionClaim h)) : ℝ≥0∞ :=
  Pr{let x ← beaconCrossSessionExp h adversary}[x = true]

/-- The BLAKE2b collision adversary induced by a foreign-session admission adversary. -/
def beaconCrossSessionCollisionReduction (h : Pqxdh.HonestRun)
    (adversary : ProbComp (BeaconCrossSessionClaim h)) :
    CollisionResistance.CRAdversary Pqxdh.Bytes :=
  show ProbComp (Pqxdh.Bytes × Pqxdh.Bytes) from do
    let claim ← adversary
    return beaconCrossSessionCollisionInputs h claim

/-- **Admitting a record sealed under different session bytes is no easier than BLAKE2b collision finding.** The reduction is factor one for a fixed honest run. -/
theorem beaconCrossSessionAdvantage_le_blake2b_cr
    (h : Pqxdh.HonestRun) (hok : h.Ok)
    (adversary : ProbComp (BeaconCrossSessionClaim h)) :
    beaconCrossSessionAdvantage h adversary ≤
      CollisionResistance.crAdvantage h.c.blake2b
        (beaconCrossSessionCollisionReduction h adversary) := by
  classical
  have hexp : beaconCrossSessionExp h adversary =
      (fun claim => decide (BeaconCrossSessionSuccess h claim)) <$> adversary := by
    simp only [beaconCrossSessionExp, bind_pure_comp]
  have hcr : CollisionResistance.crExperiment h.c.blake2b
        (beaconCrossSessionCollisionReduction h adversary) =
      (fun claim => decide ((beaconCrossSessionCollisionInputs h claim).1 ≠
          (beaconCrossSessionCollisionInputs h claim).2 ∧
        h.c.blake2b (beaconCrossSessionCollisionInputs h claim).1 =
          h.c.blake2b (beaconCrossSessionCollisionInputs h claim).2)) <$> adversary := by
    simp only [CollisionResistance.crExperiment, beaconCrossSessionCollisionReduction, bind_pure_comp,
      Functor.map_map]
  unfold beaconCrossSessionAdvantage CollisionResistance.crAdvantage
  rw [← prEvent_eq_evalDist_singleton _ true, hexp, hcr, prEvent_map, prEvent_map]
  refine prEvent_mono adversary _ _ fun claim hwin => ?_
  simp only [decide_eq_true_eq] at hwin ⊢
  exact beaconCrossSessionSuccess_implies_blake2b_collision h hok claim hwin

end BeaconcryptCore.Computational.CtxTransitionReduction

/--
info: 'BeaconcryptCore.Computational.CtxTransitionReduction.beaconWrongSequenceAdvantage_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxTransitionReduction.beaconWrongSequenceAdvantage_eq_zero
