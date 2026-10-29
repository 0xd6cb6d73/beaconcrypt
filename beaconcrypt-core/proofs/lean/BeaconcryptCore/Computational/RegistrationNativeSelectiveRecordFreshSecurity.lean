-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity
import BeaconcryptCore.Computational.RegistrationNativeRecordViewFresh

/-! The actual real permitted hidden-fresh observation is bounded by the exact all-random native fresh-byte term plus the ordered record cryptographic losses. The original native startup, callback frame and original classwise resource bills are consumed unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFreshSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeSelectiveRecordStartup (program)
open RegistrationNativeSelectiveRecordBills (programBill)
open RegistrationNativeRecordViewCrypto (chainLoss authLoss privacyLoss)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (providerState : ProviderState) (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : PqxdhDeploymentInterface.Budget)
  (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
  (allowance : Fin 14 → EffectKind → Nat)
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorCoins mlCoins : Nat)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
  (claim : Value → Option (Nat × Pqxdh.Bytes))
local notation "actualWork" => program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
  selectedOwner selectedAccept bounds PqxdhDeploymentInterface.Mode.P adversary
local notation "observation" => RegistrationNativeRecordViewFresh.event claim

include bounded framed constructorBound mlBound in
/-- The same real hidden-handle fresh hit has one byte term and the explicit HMAC/Extract, CTX integrity and CTX privacy losses. -/
theorem bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[observation <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route actualWork] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ +
      chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route actualWork budget observation hmac +
      authLoss setup (RegistrationNativeWire.ledgerCodec wire) route actualWork budget observation fallback
        (programBill budget bounds allowance constructorCoins mlCoins .hash) (programBill budget bounds allowance constructorCoins mlCoins .raw) +
      privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route actualWork budget observation := by
  have records := RegistrationNativeSelectiveRecordViewSecurity.random_bound setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary budget bounded allowance framed
    constructorCoins mlCoins constructorBound mlBound observation hmac correct fallback
  have fresh := RegistrationNativeRecordViewFresh.fresh_bytes (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds adversary claim
  rw [RegistrationNativeSelectiveRecordViewSource.ideal_source, Functor.map_map] at fresh
  have compared := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (observation <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route actualWork)
    ((fun result => observation (RegistrationNativeRecordPackage.nativeView (n := n) result.1 result.2.base.produced)) <$>
      RegistrationNativeSelectiveEntropyStartup.run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds .P adversary PqxdhRecordLiftIdeal.CtxPrivate.initial)
  exact compared.trans (by simpa only [add_assoc] using add_le_add fresh records)

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFreshSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFreshSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordFreshSecurity.bound
