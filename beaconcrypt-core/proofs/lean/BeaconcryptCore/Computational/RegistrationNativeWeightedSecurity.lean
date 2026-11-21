-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWeightedPriorSecurity
import BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage

/-! The original broad native APP target shares pay separate source, KDF, KEM, repeat and record losses for guessing and selection. Selector probabilities are returned to one real experiment before summing targets. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeCanonicalSelector (Target selected)
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget) (target : Target budget)
  (claim : Value → Option (Nat × Pqxdh.Bytes))
local notation "targetSelect" => (fun result : Value × RegistrationNativeLedger.State =>
  selected setup.source.crypto wire serverKeyId budget claim target (Prod.fst result) (Prod.snd result))
local notation "worldCount" => (budget.cap 4 + budget.cap 5)

noncomputable def observer (winning : Bool) : Value × RegistrationNativeLedger.State → Bool :=
  match winning with
  | true => RegistrationNativeObservablePriorSource.selectedGood setup wire serverKeyId budget target claim targetSelect
  | false => targetSelect

variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
noncomputable def real (winning : Bool) : ProbComp Bool :=
  RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
    (fun result => observer setup wire serverKeyId budget target claim winning (result.1, result.2.1))

noncomputable def sourceLoss (winning : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (RegistrationNativeObservableHybrid.keyLoss (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
    bounds .P adversary budget target.2 target.1.val (observer setup wire serverKeyId budget target claim winning) +
    RegistrationNativeObservableHybrid.kemLoss (n := worldCount) setup checks wire route source ensureInit identityIndex serverKeyId
      bounds .P adversary budget target.2 target.1.val (observer setup wire serverKeyId budget target claim winning))

variable (allowance : Fin 14 → EffectKind → Nat) (constructorCoins mlCoins : Nat)
  (hmac : PqxdhSecretInputKdf.HmacSha512) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
noncomputable def delta (winning : Bool) : ℝ≥0∞ :=
  sourceLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim winning +
  RegistrationNativeWeightedPriorSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
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
    𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim representation true] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim representation false] {true} +
      delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback true +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim allowance constructorCoins mlCoins hmac fallback false := by
  let sourceGame (winning : Bool) := RegistrationNativeObservablePriorSource.full setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary
    budget target.2 target.1.val (observer setup wire serverKeyId budget target claim winning)
  have sourceBound (winning : Bool) :
      ENNReal.ofReal ((real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim representation winning).boolDistance
        (sourceGame winning)) ≤ sourceLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim winning :=
    ENNReal.ofReal_le_ofReal (RegistrationNativeObservablePriorSource.source_distance setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary
      budget target.2 target.1.val (observer setup wire serverKeyId budget target claim winning) representation sourceCorrect functional bounded)
  have first := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim representation true) (sourceGame true)
  have last := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (sourceGame false)
    (real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim representation false)
  rw [ProbComp.boolDistance_comm] at last
  have selected := RegistrationNativeObservablePriorSource.good_probability setup checks wire route source ensureInit identityIndex serverKeyId bounds .P adversary
    budget target claim targetSelect bounded readback responseReadback
  rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton] at selected
  have entropy := RegistrationNativeWeightedPriorSecurity.bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
    allowance constructorCoins mlCoins hmac fallback bounded framed constructorBound mlBound correct
  have firstBound := first.trans (add_le_add le_rfl (sourceBound true))
  have lastBound := last.trans (add_le_add le_rfl (sourceBound false))
  have good := selected.trans entropy
  have combined := firstBound.trans (add_le_add (good.trans
    (add_le_add (add_le_add (mul_le_mul' le_rfl lastBound) le_rfl) le_rfl)) le_rfl)
  simpa only [delta, mul_add, add_assoc, add_comm, add_left_comm] using combined

set_option maxHeartbeats 1200000 in
theorem selector_mass :
    (∑ chosen : Target budget, 𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim representation false] {true}) ≤ 1 := by
  have masses := sum_prEvent_eq_some_le_one
    (RegistrationNativeStartupTargets.outcome (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary)
    (fun outcome => outcome.bind fun observed => RegistrationNativeCanonicalSelector.chooseLedger setup.source.crypto wire serverKeyId budget
      ((claim observed.1).map Prod.fst) observed.2.1)
  convert masses using 1
  apply Finset.sum_congr rfl
  intro chosen _member
  simp only [real, ← prEvent_eq_evalDist_singleton _ true, RegistrationNativeStartupTargets.profile_outcome, prEvent_map]
  apply prEvent_congr
  intro outcome
  cases outcome with
  | none => simp only [Option.elim_none, Option.bind_none, reduceCtorEq, Bool.false_eq_true]
  | some observed => simp only [Option.elim_some, Option.bind_some, observer, selected, decide_eq_true_eq]

set_option maxHeartbeats 2400000 in
theorem single_baseline
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (framed : ∀ chosen : Target budget, ∀ context ∈ support (prior setup budget chosen.2), RegistrationNativeSelectiveRecordFrame.Frame (n := worldCount) setup checks wire source
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
    Pr{let won ← (RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      (∑ owner : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityOriginBound.reduction (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (fun _ => false) count identityFallback ordinaryFallback owner)) +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
      (∑ chosen : Target budget, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim allowance constructorCoins mlCoins hmac fallback true) +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        (∑ chosen : Target budget, delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim allowance constructorCoins mlCoins hmac fallback false) := by
  have broad := RegistrationNativeCanonicalCoverage.broad_bound (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId
    readback shortRejects bounds budget adversary bounded claim count room identityFallback ordinaryFallback
  have targetBounds (chosen : Target budget) :
      Pr{let won ← (RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
        (RegistrationNativeCanonicalCoverage.event setup.source.crypto wire serverKeyId budget claim chosen))}[won = true] ≤
        ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
          𝒟[real setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim representation false] {true} +
        delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim allowance constructorCoins mlCoins hmac fallback true +
        ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
          delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim allowance constructorCoins mlCoins hmac fallback false := by
    have eventEq : (fun observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State worldCount KemSK source) =>
        observer setup wire serverKeyId budget chosen claim true (observed.1, observed.2.1)) =
          RegistrationNativeCanonicalCoverage.event setup.source.crypto wire serverKeyId budget claim chosen := rfl
    have result := target_bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget chosen claim representation allowance constructorCoins mlCoins hmac fallback
      bounded (framed chosen) constructorBound mlBound correct sourceCorrect functional readback responseReadback
    unfold real at result
    rw [eventEq] at result
    simpa only [real, observer, ← prEvent_eq_evalDist_singleton _ true] using result
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun chosen _member => targetBounds chosen)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at summed
  have masses := selector_mass setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget claim representation
  have baseline := mul_le_mul' (le_refl (((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹)) masses
  rw [mul_one] at baseline
  have shares := summed.trans (add_le_add (add_le_add baseline le_rfl) le_rfl)
  simpa only [add_assoc] using broad.trans (add_le_add le_rfl shares)

end BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity.target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity.target_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity.selector_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity.selector_mass

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity.single_baseline' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity.single_baseline
