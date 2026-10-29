-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProductionTargetBound

/-! Quantitative original native CE-APP composition. The real changed-prekey event pays one global Ed-origin reduction sum. Its complementary public equality stays in the sole canonical parsed-accept by owner target product, whose actual source, KDF, one KEM, repeated-role recovery, selected physical origin, record and byte-entropy comparisons are all discharged by concrete theorems. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProductionSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhRecordLiftInterface (EffectKind)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
  (originFallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)

noncomputable def originLoss : ℝ≥0∞ :=
  ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
    (RegistrationNativeIdentityOriginBound.reduction (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds .P adversary (fun _ => false) budget.create originFallback ordinaryFallback target)

attribute [local irreducible] RegistrationNativeOpenKeyKemGame.normal RegistrationNativeExperiment.profile
  RegistrationNativeRelatedFamily.advantage RegistrationBoundKeySchedule.keyLoss
  RegistrationNativeKemEarlyObservedGame.branch

/-- The actual generated native ML profile's broad original CE-APP event has one real origin charge and one canonical target sum of explicit primitive, recovery, record and byte-entropy losses. -/
theorem ceapp_bound
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,
      bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (allowance : Fin 14 → EffectKind → Nat)
    (framed : ∀ (target : Fin budget.accept × Fin budget.capacity),
      ∀ context ∈ support (RegistrationNativeSelectiveRecordTraceUniformSecurity.prior setup budget target.2),
      RegistrationNativeSelectiveRecordFrame.Frame (n := budget.cap 4 + budget.cap 5) setup checks wire source
        context.seed context.scalar context.candidate (RegistrationNativeSelectiveRecordTraceUniformSecurity.provider setup target.2.val context)
        target.2.val target.1.val allowance)
    (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (recordFallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds .P adversary (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      originLoss setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary budget originFallback ordinaryFallback +
      ∑ target : Fin budget.accept × Fin budget.capacity,
        RegistrationNativeProductionTargetBound.loss setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
          allowance constructorCoins mlCoins recordFallback := by
  have split := RegistrationNativePrekeyProbability.broad_bound (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
    readback shortRejects bounds budget adversary bounded claim budget.create (by omega) originFallback ordinaryFallback
  unfold originLoss
  apply split.trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro target _member
  exact RegistrationNativeProductionTargetBound.bound setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim
    allowance constructorCoins mlCoins recordFallback representation correct functional bounded readback responseReadback (framed target) constructorBound mlBound

end BeaconcryptCore.Computational.RegistrationNativeProductionSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProductionSecurity.ceapp_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProductionSecurity.ceapp_bound
