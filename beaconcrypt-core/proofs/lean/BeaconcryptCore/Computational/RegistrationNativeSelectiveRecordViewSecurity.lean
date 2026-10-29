-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordBills
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSource

/-! The complete real annotated selective native program carries its permitted hidden-origin observation through the ordered HMAC/Extract and CTX integrity/privacy reductions to the actual all-random entropy endpoint. Native startup, original ledger, actual query bills and the literal origin map are retained. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveRecordStartup (program)
open RegistrationNativeSelectiveRecordBills (programBill programCoins)
open RegistrationNativeRecordViewCrypto (chainLoss authLoss privacyLoss decision)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (providerState : ProviderState)
  (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : PqxdhDeploymentInterface.Budget)
  (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
  (allowance : Fin 14 → EffectKind → Nat)
  (framed : RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept allowance)
  (constructorCoins mlCoins : Nat)
  (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
  (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
  (observe : RegistrationNativeRecordPackage.View n (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value → Bool)

include bounded framed constructorBound mlBound in
/-- The complete actual guarded native source is within the three explicit record losses of the actual all-random native entropy execution. -/
theorem random_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((observe <$> RegistrationNativeRecordViewCrypto.real setup (RegistrationNativeWire.ledgerCodec wire) route
        (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
          selectedOwner selectedAccept bounds mode adversary)).boolDistance
        ((fun result => observe (RegistrationNativeRecordPackage.nativeView result.1 result.2.base.produced)) <$>
          RegistrationNativeSelectiveEntropyStartup.run (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId
            seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary PqxdhRecordLiftIdeal.CtxPrivate.initial)) ≤
      chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
        budget observe hmac +
      authLoss setup (RegistrationNativeWire.ledgerCodec wire) route
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
        budget observe fallback (programBill budget bounds allowance constructorCoins mlCoins .hash)
          (programBill budget bounds allowance constructorCoins mlCoins .raw) +
      privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
        budget observe := by
  have compared := RegistrationNativeRecordViewCrypto.random_bound setup (RegistrationNativeWire.ledgerCodec wire) route
    (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
    budget observe
    (RegistrationNativeSelectiveRecordBills.record_bounded setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded)
    (programBill budget bounds allowance constructorCoins mlCoins)
    (RegistrationNativeSelectiveRecordBills.program_categories setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound route)
    hmac correct fallback
  have endpoint := congrArg (Functor.map observe)
    (RegistrationNativeSelectiveRecordViewSource.ideal_source setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary (fun _ => .random))
  simp only [Functor.map_map] at endpoint
  rw [endpoint] at compared
  exact compared

include bounded framed constructorBound mlBound in
/-- Every exact HMAC/Extract observer used in the native loss sum has the derived actual byte-draw bill. -/
theorem chain_observer_billed (step : Fin (PqxdhRecordLiftIdeal.hops n budget))
    (context : Unit) (output : PqxdhFullSecretInputKdf.FullOutput) :
    (PqxdhRecordLiftLaterChain.observerOf setup (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeRecordPackage.client
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary))
      (fun old _ => decision observe old) budget step context output).IsTotalQueryBound
        (2 * programCoins budget bounds allowance constructorCoins mlCoins + 44) := by
  simpa only [Nat.add_zero] using PqxdhRecordLiftLaterChain.observerOf_total setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeRecordPackage.client
      (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary))
    (programCoins budget bounds allowance constructorCoins mlCoins)
    (RegistrationNativeSelectiveRecordBills.chain_coins setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound route)
    (fun old _ => decision observe old) 0 (fun old _ => RegistrationNativeRecordViewCrypto.decision_coins observe old)
    budget step context output

include bounded framed constructorBound mlBound in
/-- The actual per-key CTX integrity clients retain the derived shared-hash/raw caps and seal at most once. -/
theorem ctx_step_billed (step : Fin (PqxdhRecordLiftIdeal.hops n budget)) :
    let stepClient := PqxdhRecordLiftLaterCtx.stepClientOf setup (RegistrationNativeWire.ledgerCodec wire) route
      (RegistrationNativeRecordPackage.client
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary))
      (decision observe) budget step
    stepClient.IsQueryBoundP PqxdhRecordLiftCtxModeBounds.HashRoute
      (programBill budget bounds allowance constructorCoins mlCoins .hash) ∧
    stepClient.IsQueryBoundP (PqxdhRecordLiftCtxModeBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    stepClient.IsQueryBoundP (PqxdhRecordLiftCtxModeBounds.TargetClass AdaptiveCtxReceive.IsRawQuery)
      (programBill budget bounds allowance constructorCoins mlCoins .raw) := by
  exact (PqxdhRecordLiftLaterCtx.step_bills_of setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeRecordPackage.client
      (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary))
    (programBill budget bounds allowance constructorCoins mlCoins)
    (RegistrationNativeSelectiveRecordBills.program_categories setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound route)
    (decision observe) 0 (RegistrationNativeRecordViewCrypto.decision_coins observe) budget step).2

include bounded framed constructorBound mlBound in
/-- Every exact IND-dollar adversary in the native privacy loss has the derived actual uniform, shared-hash, one-seal and raw caps. -/
theorem privacy_step_billed (step : Fin (PqxdhRecordLiftIdeal.hops n budget)) :
    let client := PqxdhRecordLiftCtxPrivModes.decisionClient PqxdhRecordLiftCtxPrivModes.bytesSample setup.source.crypto
      (PqxdhRecordLiftLaterPriv.stepClientOf setup (RegistrationNativeWire.ledgerCodec wire) route
        (RegistrationNativeRecordPackage.client
          (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary))
        (decision observe) budget step)
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform
      (programBill budget bounds allowance constructorCoins mlCoins .uniform + 66 * programBill budget bounds allowance constructorCoins mlCoins .hash) ∧
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash (programBill budget bounds allowance constructorCoins mlCoins .hash) ∧
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 ∧
    client.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery (programBill budget bounds allowance constructorCoins mlCoins .raw) := by
  simpa only [Nat.add_zero] using PqxdhRecordLiftLaterPriv.priv_step_bills_of setup (RegistrationNativeWire.ledgerCodec wire) route
    (RegistrationNativeRecordPackage.client
      (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary))
    (programBill budget bounds allowance constructorCoins mlCoins)
    (RegistrationNativeSelectiveRecordBills.program_categories setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState
      selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed constructorCoins mlCoins constructorBound mlBound route)
    (decision observe) 0 (RegistrationNativeRecordViewCrypto.decision_coins observe) budget step

end BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.random_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.chain_observer_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.chain_observer_billed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.ctx_step_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.ctx_step_billed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.privacy_step_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordViewSecurity.privacy_step_billed
