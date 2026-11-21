-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts
import BeaconcryptCore.Computational.RegistrationNativeWeightedSecurity
import BeaconcryptCore.Computational.RegistrationNativeLorAbsoluteSecurity

import BeaconcryptCore.Computational.RegistrationNativeConcreteSecurity
import BeaconcryptCore.Computational.RegistrationNativeProductionSecurity

/-! Both APP bounds remain available for one unchanged native experiment. This endpoint takes their minimum with the same source-derived primitive bills; no comparison between target-specific ideal experiments is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeQuantitativeSecurity
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
  (identityFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
local notation "worldCount" => budget.cap 4 + budget.cap 5
local notation "callbackBill" => allowance setup source ensureInit receipts
local notation "constructorBill" => receipts.initCoins + 32
include bounded correct functional readback responseReadback shortRejects in
set_option maxHeartbeats 1200000 in
/-- Take the tighter of the original target sum and the proved single-baseline selector bound. -/
theorem app_min (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := worldCount) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
    min
      (RegistrationNativeProductionSecurity.originLoss setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary budget identityFallback ordinaryFallback +
        ∑ target : Fin budget.accept × Fin budget.capacity,
          RegistrationNativeProductionTargetBound.loss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
            callbackBill constructorBill receipts.generateCoins fallback)
      (RegistrationNativeLorWeightedSecurity.originLoss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget representation budget.create identityFallback ordinaryFallback +
        ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
        (∑ target : Fin budget.accept × Fin budget.capacity,
          RegistrationNativeWeightedSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
            callbackBill constructorBill receipts.generateCoins setup.hmac fallback true) +
        ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
          (∑ target : Fin budget.accept × Fin budget.capacity,
            RegistrationNativeWeightedSecurity.delta setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
              callbackBill constructorBill receipts.generateCoins setup.hmac fallback false)) := by
  apply le_min
  · exact RegistrationNativeProductionSecurity.ceapp_bound setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary budget claim identityFallback ordinaryFallback
      correct functional bounded readback responseReadback shortRejects callbackBill
      (fun target context _supported => RegistrationNativeConcretePriorCosts.frame setup checks wire source ensureInit receipts target.2.val target.1.val context)
      constructorBill receipts.generateCoins
      (RegistrationNativeConcretePriorCosts.constructor_bound setup source ensureInit receipts identityIndex serverKeyId)
      (RegistrationNativeConcretePriorCosts.generation_bound setup source ensureInit receipts) fallback
  · exact RegistrationNativeConcreteSecurity.app setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget representation receipts fallback bounded correct functional readback responseReadback shortRejects
      budget.create (by omega) identityFallback ordinaryFallback claim

end BeaconcryptCore.Computational.RegistrationNativeQuantitativeSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeQuantitativeSecurity.app_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeQuantitativeSecurity.app_min
