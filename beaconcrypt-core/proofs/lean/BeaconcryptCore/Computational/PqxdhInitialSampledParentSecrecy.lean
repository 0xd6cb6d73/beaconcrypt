import BeaconcryptCore.Computational.PqxdhInitialSampledParent

/-!
The concrete dependent source carrier supplies one main and one input-candidate reduction. Each includes the same complete preparation and stopped-source distribution. The ordinary reduction observer receives the parent material and full child output without the hidden next-chain input; the actual byte-level freshness test is connected by its proved three-times candidate bound.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhInitialSampledParent PqxdhInitialSourceInitialSecrecy
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth remaining : Nat)
variable {prior : ProbComp (Context extra M P I D K X Response A N S B)}

noncomputable def aliasTester : FullObserver (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) :=
  RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source)
    (observed source writer sender route decode depth remaining) PqxdhInitialCommonSecrecy.candidates

noncomputable def actual (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior))
    (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  native source writer sender route decode depth remaining pair.1 pair.2
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))

noncomputable def random (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior))
    (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  let output ← $ᵗ FullOutput
  native source writer sender route decode depth remaining pair.1 pair.2 output

/-- Averaging the real-child freshness comparison retains the exact full predecessor sampler and charges three copies of its actual input-candidate event. -/
theorem actual_route (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior))
    (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) :
    (actual source writer sender route decode depth remaining sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (observer source writer sender route decode depth remaining)) ≤
      3 * Pr[fun pair => pair.1 ∈ PqxdhInitialCommonSecrecy.candidates pair.2 |
        RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address)
          (observed source writer sender route decode depth remaining)].toReal := by
  simpa only [actual, RawCtxSelectedParentSecrecy.actual, RawCtxSelectedParentCandidates.sample,
    RawCtxFullPreimageTester.actual, RawCtxFullPreimageTester.production, bad,
    Nat.cast_ofNat, bind_assoc, pure_bind, ← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum,
    probEvent_map, Function.comp_def, decide_eq_true_eq, probEvent_pure, mul_ite, mul_one, mul_zero] using
      RawCtxScaledBadEventMixture.bind_bound (RawCtxSelectedParentCandidates.sample sample address)
        (fun pair => native source writer sender route decode depth remaining pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => observer source writer sender route decode depth remaining pair.1
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => bad source writer sender route decode depth remaining pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))) 3
        (fun pair => local_bound source writer sender route decode depth remaining pair.1 pair.2 _)



set_option maxRecDepth 2048 in
/-- The independent-child freshness comparison retains the full delayed-coordinate candidate experiment with the same explicit factor three. -/
theorem random_route (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior))
    (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) :
    (random source writer sender route decode depth remaining sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (observer source writer sender route decode depth remaining)) ≤
      3 * Pr[fun pair => pair.1 ∈ PqxdhInitialCommonSecrecy.candidates pair.2 |
        RawCtxSelectedParentCandidates.uniform sample address
          (observed source writer sender route decode depth remaining)].toReal := by
  have bound := RawCtxScaledBadEventMixture.bind_bound
    (do let pair ← RawCtxSelectedParentCandidates.sample sample address
        let output ← $ᵗ FullOutput
        pure (pair, output))
    (fun value => native source writer sender route decode depth remaining value.1.1 value.1.2 value.2)
    (fun value => observer source writer sender route decode depth remaining value.1.1 value.2)
    (fun value => bad source writer sender route decode depth remaining value.1.1 value.1.2 value.2) 3
    (fun value => local_bound source writer sender route decode depth remaining value.1.1 value.1.2 value.2)
  simp only [random, RawCtxSelectedParentSecrecy.random, independentFullGame,
    RawCtxSelectedParentSecrecy.joint, RawCtxSelectedParentCandidates.sample,
    RawCtxSelectedParentCandidates.uniform, RawCtxSelectedParentSampler.original, bad,
    Nat.cast_ofNat, bind_assoc, pure_bind] at bound ⊢
  simp only [bind_pure_comp] at bound ⊢
  simpa only [← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, decide_eq_true_eq] using bound



/-- Real-child recovery is charged to the separately constructed full-output tester, with the freshness coefficient applied explicitly to its Extract/HMAC and finite-image terms. -/
theorem actual_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior)) (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) :
    (actual source writer sender route decode depth remaining sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (observer source writer sender route decode depth remaining)) ≤
      3 * ((2 ^ 352 : ℝ)⁻¹ +
        RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer sender route decode depth remaining) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer sender route decode depth remaining)) := by
  have bound := ENNReal.toReal_mono
    (show ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
      RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer sender route decode depth remaining) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer sender route decode depth remaining))) ≠ ⊤ by simp)
    (RawCtxSelectedParentCandidates.real_bound source hmac correct sample address
      (observed source writer sender route decode depth remaining) PqxdhInitialCommonSecrecy.candidates)
  have nonnegative : 0 ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer sender route decode depth remaining) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer sender route decode depth remaining) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal nonnegative, add_assoc] using
    (actual_route source writer sender route decode depth remaining sample address).trans (mul_le_mul_of_nonneg_left bound (by norm_num))



/-- Only the independent-child branch uses the delayed uniform-input guess bound, retaining every prior and repeated candidate and the explicit freshness coefficient. -/
theorem random_bound (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior))
    (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) output result,
      result ∈ support (observed source writer sender route decode depth remaining context output) →
        (PqxdhInitialCommonSecrecy.candidates result).length ≤ qCandidates) :
    (random source writer sender route decode depth remaining sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (observer source writer sender route decode depth remaining)) ≤
      3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  simpa using (random_route source writer sender route decode depth remaining sample address).trans
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
        (RawCtxSelectedParentCandidates.uniform_bound sample address
          (observed source writer sender route decode depth remaining)
          PqxdhInitialCommonSecrecy.candidates qCandidates bounded)) (by norm_num))



private theorem loss_sum {adv first middle last mainExtract mainHmac testExtract testHmac image guess : ℝ}
    (triangle : adv ≤ first + (middle + last))
    (front : first ≤ 3 * (image + testExtract + testHmac))
    (center : middle ≤ mainExtract + mainHmac) (back : last ≤ 3 * guess) :
    adv ≤ mainExtract + mainHmac + 3 * (testExtract + testHmac + image + guess) := by
  linarith


/-- One full parent-to-child secrecy hop with the actual family freshness decision pays its constructed main Extract/HMAC pair and three copies of the tester, image and independent-input terms. -/
theorem bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior)) (address : (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior) → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) output result,
      result ∈ support (observed source writer sender route decode depth remaining context output) →
        (PqxdhInitialCommonSecrecy.candidates result).length ≤ qCandidates) :
    (actual source writer sender route decode depth remaining sample address).boolDistAdvantage
      (random source writer sender route decode depth remaining sample address) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (observer source writer sender route decode depth remaining) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (observer source writer sender route decode depth remaining) +
        3 * (RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer sender route decode depth remaining) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer sender route decode depth remaining) +
          (2 ^ 352 : ℝ)⁻¹ + (qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  have triangle := (ProbComp.boolDistAdvantage_triangle
    (actual source writer sender route decode depth remaining sample address)
    (RawCtxSelectedParentSecrecy.actual source sample address
      (observer source writer sender route decode depth remaining))
    (random source writer sender route decode depth remaining sample address)).trans
      (add_le_add le_rfl (ProbComp.boolDistAdvantage_triangle _
        (RawCtxSelectedParentSecrecy.random sample address
          (observer source writer sender route decode depth remaining)) _))
  have main : (RawCtxSelectedParentSecrecy.actual source sample address
      (observer source writer sender route decode depth remaining)).boolDistAdvantage
        (RawCtxSelectedParentSecrecy.random sample address
          (observer source writer sender route decode depth remaining)) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address
        (observer source writer sender route decode depth remaining) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address
            (observer source writer sender route decode depth remaining) :=
    RawCtxSelectedParentSecrecy.primitive_bound source hmac correct sample address
      (observer source writer sender route decode depth remaining)
  have back : (RawCtxSelectedParentSecrecy.random sample address
      (observer source writer sender route decode depth remaining)).boolDistAdvantage
        (random source writer sender route decode depth remaining sample address) ≤ 3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using
      random_bound source writer sender route decode depth remaining sample address qCandidates bounded
  exact loss_sum triangle (actual_bound source writer sender route decode depth remaining hmac correct sample address) main back



end BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.actual_route

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.random_route

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.actual_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy.random_bound
