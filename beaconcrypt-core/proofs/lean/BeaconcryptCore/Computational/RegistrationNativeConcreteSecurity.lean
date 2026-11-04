-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts
import BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity
import BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity

/-! Whole-prior native APP and centered absolute LR bounds instantiate every callback and startup bill from the actual native interpreter. Premises provide only ordinary interface budgets, codec/representation and primitive functional contracts, primitive execution receipts and source correctness. No callback frame, provider cost or protocol security conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open RegistrationNativeConcretePriorCosts (Receipts allowance)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (receipts : Receipts setup source ensureInit)
  (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
  (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
  (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
  (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
  (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
  (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
    bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
  (count : Nat) (room : budget.create ≤ count + 1)
  (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
local notation "worldCount" => budget.cap 4 + budget.cap 5
local notation "callbackBill" => allowance setup source ensureInit receipts
local notation "constructorBill" => receipts.initCoins + 32
local notation "origin" => RegistrationNativeLorWeightedSecurity.originLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget representation count identityFallback ordinaryFallback

include bounded correct functional readback responseReadback shortRejects room in
set_option maxHeartbeats 1200000 in
/-- One fresh-entropy baseline for the unchanged broad native APP event, with all protocol callback costs proved from the actual source. -/
theorem app (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
    origin + ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
      (∑ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeWeightedSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
          callbackBill constructorBill receipts.generateCoins setup.hmac fallback true) +
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        (∑ target : Fin budget.accept × Fin budget.capacity,
          RegistrationNativeWeightedSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
            callbackBill constructorBill receipts.generateCoins setup.hmac fallback false) := by
  exact RegistrationNativeWeightedSecurity.single_baseline setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget claim representation
    callbackBill constructorBill receipts.generateCoins setup.hmac fallback bounded
    (fun target context _supported => RegistrationNativeConcretePriorCosts.frame setup checks wire source ensureInit receipts target.2.val target.1.val context)
    (RegistrationNativeConcretePriorCosts.constructor_bound setup source ensureInit receipts identityIndex serverKeyId)
    (RegistrationNativeConcretePriorCosts.generation_bound setup source ensureInit receipts)
    correct correct functional readback responseReadback shortRejects count room identityFallback ordinaryFallback

include bounded correct functional readback responseReadback shortRejects room in
set_option maxHeartbeats 1200000 in
/-- The original centered absolute native LR expression has only primitive-derived execution bills. -/
theorem lr (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool) :
    ENNReal.ofReal |(𝒟[RegistrationNativeLorWeightedSecurity.broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation true] {true}).toReal -
      (1 / 2 : ℝ) * (𝒟[RegistrationNativeLorWeightedSecurity.broadGame setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation false] {true}).toReal| ≤
    origin +
      (∑ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeLorWeightedSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess
          callbackBill constructorBill receipts.generateCoins setup.hmac fallback true) +
      2⁻¹ * (∑ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeLorWeightedSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target filter guess
          callbackBill constructorBill receipts.generateCoins setup.hmac fallback false) := by
  exact RegistrationNativeLorAbsoluteSecurity.centered_absolute setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget filter guess representation
    callbackBill constructorBill receipts.generateCoins setup.hmac fallback bounded
    (fun target context _supported => RegistrationNativeConcretePriorCosts.frame setup checks wire source ensureInit receipts target.2.val target.1.val context)
    (RegistrationNativeConcretePriorCosts.constructor_bound setup source ensureInit receipts identityIndex serverKeyId)
    (RegistrationNativeConcretePriorCosts.generation_bound setup source ensureInit receipts)
    correct correct functional readback responseReadback shortRejects count room identityFallback ordinaryFallback

end BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity.app' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity.app

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity.lr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity.lr
