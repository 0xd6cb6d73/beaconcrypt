-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorPriorSecurity
import BeaconcryptCore.Computational.RegistrationNativeLorCoverage

/-! The unchanged native LR experiment retains its original private test bit and both centered probability inequalities. Each target pays separate source, repeat and record losses; disjoint public canonical shares return to the same broad real experiment. One actual changed-prekey origin event is charged once in each direction. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
  (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
local notation "worldCount" => budget.cap 4 + budget.cap 5
attribute [local irreducible] RegistrationNativeLorRecordSecurity.observer
  RegistrationNativeObservablePriorSource.full
local notation "observe" => RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target

variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
noncomputable def real (winning : Bool) : ProbComp Bool :=
  RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
    (fun result => observe winning (result.1, result.2.1))

noncomputable def sourceLoss (winning : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (RegistrationNativeObservableHybrid.keyLoss (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    bounds .P adversary budget target.2 target.1.val (observe winning) +
    RegistrationNativeObservableHybrid.kemLoss (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
      bounds .P adversary budget target.2 target.1.val (observe winning))

variable (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
noncomputable def delta (winning : Bool) : ℝ≥0∞ :=
  sourceLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess winning +
  RegistrationNativeLorPriorSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback winning

set_option maxHeartbeats 1200000 in
theorem target_bound
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ context ∈ support (prior setup budget target.2), RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup target.2.val context) target.2.val target.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (sourceCorrect : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    (𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation true] {true} ≤
      2⁻¹ * 𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation false] {true} +
      delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true +
      2⁻¹ * delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false) ∧
    (2⁻¹ * 𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation false] {true} ≤
      𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation true] {true} +
      delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback true +
      2⁻¹ * delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess allowance constructorCoins mlCoins hmac fallback false) := by
  let sourceGame (winning : Bool) := RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary
    budget target.2 target.1.val (observe winning)
  have sourceBound (winning : Bool) :
      ENNReal.ofReal ((real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation winning).boolDistance
        (sourceGame winning)) ≤ sourceLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess winning :=
    ENNReal.ofReal_le_ofReal (RegistrationNativeObservablePriorSource.source_distance setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary
      budget target.2 target.1.val (observe winning) representation sourceCorrect functional bounded)
  have into (winning : Bool) := (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation winning) (sourceGame winning)).trans
      (add_le_add le_rfl (sourceBound winning))
  have back (winning : Bool) : 𝒟[sourceGame winning] {true} ≤
      𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation winning] {true} +
      sourceLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess winning := by
    have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (sourceGame winning)
      (real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess representation winning)
    rw [ProbComp.boolDistance_comm] at compared
    exact compared.trans (add_le_add le_rfl (sourceBound winning))
  have centered := RegistrationNativeLorPriorSecurity.bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct readback responseReadback
  constructor
  · have combined := (into true).trans (add_le_add (centered.1.trans
      (add_le_add (add_le_add (mul_le_mul' le_rfl (back false)) le_rfl) le_rfl)) le_rfl)
    simpa only [delta, mul_add, add_assoc, add_comm, add_left_comm] using combined
  · have scaled := mul_le_mul' (le_refl (2⁻¹ : ℝ≥0∞)) (into false)
    rw [mul_add] at scaled
    have combined := scaled.trans
      (add_le_add (centered.2.trans (add_le_add (add_le_add (back true) le_rfl) le_rfl)) le_rfl)
    simpa only [delta, mul_add, add_assoc, add_comm, add_left_comm] using combined

noncomputable def broadGame (winning : Bool) : ProbComp Bool :=
  RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
    (fun result => RegistrationNativeLorCoverage.broad setup.source.crypto wire serverKeyId budget filter guess winning (result.1, result.2.1))

noncomputable def originLoss (count : Nat) (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) : ℝ≥0∞ :=
  ∑ owner : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
    (RegistrationNativeIdentityOriginBound.reduction (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (fun _ => false) count identityFallback ordinaryFallback owner)

set_option maxHeartbeats 2400000 in
/-- The original centered LR event has both probability directions, one origin loss and separate observer-specific target loss sums. -/
theorem centered
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ chosen : Fin budget.accept × Fin budget.capacity, ∀ context ∈ support (prior setup budget chosen.2), RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
      context.seed context.scalar context.candidate (provider setup chosen.2.val context) chosen.2.val chosen.1.val allowance)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (sourceCorrect : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (count : Nat) (room : budget.create ≤ count + 1)
    (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (𝒟[broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation true] {true} ≤
      2⁻¹ * 𝒟[broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation false] {true} +
      originLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget representation count identityFallback ordinaryFallback +
      (∑ chosen : Fin budget.accept × Fin budget.capacity, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess allowance constructorCoins mlCoins hmac fallback true) +
      2⁻¹ * (∑ chosen : Fin budget.accept × Fin budget.capacity, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess allowance constructorCoins mlCoins hmac fallback false)) ∧
    (2⁻¹ * 𝒟[broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation false] {true} ≤
      𝒟[broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation true] {true} +
      originLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget representation count identityFallback ordinaryFallback +
      (∑ chosen : Fin budget.accept × Fin budget.capacity, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess allowance constructorCoins mlCoins hmac fallback true) +
      2⁻¹ * (∑ chosen : Fin budget.accept × Fin budget.capacity, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess allowance constructorCoins mlCoins hmac fallback false)) := by
  have split (winning : Bool) := RegistrationNativeLorCoverage.broad_probability (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary
    budget filter guess bounded readback shortRejects winning
  have masses (winning : Bool) := RegistrationNativeLorCoverage.share_mass (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary budget filter guess winning
  have origin := RegistrationNativeIdentityOriginProbability.changed_prekey_bound (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds .P adversary budget bounded count room identityFallback ordinaryFallback
  simp only [prEvent_eq_evalDist_singleton] at split masses origin
  have targetBounds (chosen : Fin budget.accept × Fin budget.capacity) := target_bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen filter guess representation
    allowance constructorCoins mlCoins hmac fallback bounded (framed chosen) constructorBound mlBound correct sourceCorrect functional readback responseReadback
  have forward := Finset.sum_le_sum (s := Finset.univ) (fun chosen _member => (targetBounds chosen).1)
  have backward := Finset.sum_le_sum (s := Finset.univ) (fun chosen _member => (targetBounds chosen).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at forward backward
  have sharesForward := forward.trans (add_le_add (add_le_add (mul_le_mul' le_rfl (masses false)) le_rfl) le_rfl)
  have sharesBackward := backward.trans (add_le_add (add_le_add (masses true) le_rfl) le_rfl)
  have halfOrigin := mul_le_mul' (by norm_num : (2⁻¹ : ℝ≥0∞) ≤ 1) origin
  rw [one_mul] at halfOrigin
  constructor
  · have combined := (split true).trans (add_le_add origin sharesForward)
    simpa only [real, broadGame, originLoss, add_assoc, add_comm, add_left_comm] using combined
  · have scaled := mul_le_mul' (le_refl (2⁻¹ : ℝ≥0∞)) (split false)
    rw [mul_add] at scaled
    have combined := scaled.trans (add_le_add halfOrigin sharesBackward)
    simpa only [real, broadGame, originLoss, add_assoc, add_comm, add_left_comm] using combined

end BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity.target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity.target_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity.centered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorWeightedSecurity.centered
