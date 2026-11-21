-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordSecurity
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedStartupBound

/-! The actual selective guarded native program, including effectful startup and the literal original ledger, consumes the ordered HMAC/Extract and CTX INT/IND-dollar record reductions. The record-ideal endpoint is exactly the already-proved native selective entropy execution. Every reduction bill is derived from the native callback Frame, actual constructor/ML coin caps and the original command budget. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRecordSecurity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveRecordStartup (program)
open RegistrationNativeSelectiveRecordBills (programBill programCoins)
open RegistrationNativeRecordCrypto (chainLoss authLoss privacyLoss decision)
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
  (observe : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source) Value → Bool)

local notation "nativeObserver" => (fun result : RegistrationNativeEntropyRun.Outcome
  (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source) Value =>
    observe (RegistrationNativeG3MaterializedStartup.publicOutcome result))

include bounded framed constructorBound mlBound in
/-- The complete cold known108 native game reaches all-random native entropy with its actual repeat audit and the three exactly billed record losses. -/
theorem random_bound (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal
      ((observe <$> RegistrationNativeG3MaterializedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary).boolDistance
        ((fun result => nativeObserver result.1.1) <$>
          RegistrationNativeSelectiveEntropyStartup.run (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId
            seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary PqxdhRecordLiftIdeal.CtxPrivate.initial)) ≤
      Pr{let bad ← (RegistrationNativeG3MaterializedStartup.audit (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)}[bad = true] +
      chainLoss setup (RegistrationNativeWire.ledgerCodec wire) route
        (program (n := n) setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
        budget nativeObserver hmac +
      authLoss setup (RegistrationNativeWire.ledgerCodec wire) route
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
        budget nativeObserver fallback (programBill budget bounds allowance constructorCoins mlCoins .hash)
          (programBill budget bounds allowance constructorCoins mlCoins .raw) +
      privacyLoss setup (RegistrationNativeWire.ledgerCodec wire) route
        (program setup checks wire source ensureInit identityIndex serverKeyId seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
        budget nativeObserver := by
  have repeatedBound := RegistrationNativeG3MaterializedStartupBound.bound (n := n) setup checks wire route source serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary ensureInit identityIndex
  have projected := (ENNReal.ofReal_le_ofReal ((boolDistance_le_discreteDistance _ _).trans
    (discreteDistance_map_le observe _ _))).trans repeatedBound
  have records := RegistrationNativeSelectiveRecordSecurity.random_bound setup checks wire route source ensureInit identityIndex serverKeyId
    seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary budget bounded allowance framed
    constructorCoins mlCoins constructorBound mlBound nativeObserver hmac correct fallback
  have sourceEq := congrArg (Functor.map observe)
    (RegistrationNativeG3MaterializedStartup.actual_source (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
  simp only [Functor.map_map] at sourceEq
  rw [← sourceEq] at records
  have triangle := ProbComp.boolDistance_triangle
    (observe <$> RegistrationNativeG3MaterializedStartup.fullGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
    (observe <$> RegistrationNativeG3MaterializedStartup.actual (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
      seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary)
    ((fun result => nativeObserver result.1.1) <$>
      RegistrationNativeSelectiveEntropyStartup.run (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId
        seed scalar candidate provider providerState selectedOwner selectedAccept bounds mode adversary PqxdhRecordLiftIdeal.CtxPrivate.initial)
  have combined := (ENNReal.ofReal_le_ofReal triangle).trans
    ((ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).le.trans (add_le_add projected records))
  simpa only [add_assoc] using combined

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRecordSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRecordSecurity.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRecordSecurity.random_bound
