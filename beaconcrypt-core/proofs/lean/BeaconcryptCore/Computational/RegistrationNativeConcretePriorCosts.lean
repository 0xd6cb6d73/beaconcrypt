-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeConcreteFrame
import BeaconcryptCore.Computational.RegistrationNativeCandidateProviderCosts
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceUniformSecurity

/-! Whole-prior callback frames and startup costs are derived from the actual interpreter and narrow primitive execution receipts. Every selected handle, prior context and failure prefix uses the same literal class allowance; no provider or protocol callback bound is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context provider)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- Execution costs constrain only initialization, generation, signing and the three original KEM primitive programs. -/
structure Receipts (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool) where
  initCoins : Nat
  generateCoins : Nat
  signCoins : Nat
  keygenCoins : Nat
  encapsCoins : Nat
  decapsCoins : Nat
  initialization : (ensureInit.run ()).IsTotalQueryBound initCoins
  generation : source.generate.IsTotalQueryBound generateCoins
  signing : ∀ key request, (source.sign key request).IsTotalQueryBound signCoins
  keygen : (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound keygenCoins
  encaps : ∀ key, (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)).IsTotalQueryBound encapsCoins
  decaps : ∀ key ciphertext, (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.decaps key ciphertext)).IsTotalQueryBound decapsCoins

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (receipts : Receipts setup source ensureInit)

def kemCoins : Nat := RegistrationNativeCandidateProviderCosts.providerBill receipts.keygenCoins receipts.encapsCoins receipts.decapsCoins

def allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat :=
  RegistrationNativeConcreteFrame.allowance receipts.generateCoins receipts.signCoins (kemCoins setup source ensureInit receipts)

theorem provider_bound (selected : Nat) (context : Context KemSK)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain)
    (before : PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase) :
    ((provider setup selected context query).run before).IsTotalQueryBound (kemCoins setup source ensureInit receipts) :=
  RegistrationNativeCandidateProviderCosts.provider_bound setup.baseImpl setup.kem receipts.keygenCoins receipts.encapsCoins receipts.decapsCoins
    receipts.keygen receipts.encaps receipts.decaps selected context.profile.pairs context.profile.publicKey context.profile.challenge context.candidate query before

theorem frame {n : Nat} (selectedOwner selectedAccept : Nat) (context : Context KemSK) :
    RegistrationNativeSelectiveRecordFrame.Frame (n := n) setup checks wire source context.seed context.scalar context.candidate
      (provider setup selectedOwner context) selectedOwner selectedAccept (allowance setup source ensureInit receipts) :=
  RegistrationNativeConcreteFrame.frame setup checks wire source context.seed context.scalar context.candidate
    (provider setup selectedOwner context) selectedOwner selectedAccept receipts.generateCoins receipts.signCoins (kemCoins setup source ensureInit receipts)
    receipts.generation receipts.signing (provider_bound setup source ensureInit receipts selectedOwner context)

theorem constructor_bound (identityIndex : Nat) (serverKeyId : U64) :
    ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound
      (receipts.initCoins + 32) :=
  RegistrationNativePrimitiveCosts.constructor_bound setup.joint ensureInit receipts.initCoins receipts.initialization identityIndex serverKeyId

theorem generation_bound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound receipts.generateCoins :=
  RegistrationNativePrimitiveCosts.generation_bound source receipts.generateCoins receipts.generation

end BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.provider_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.provider_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.constructor_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.constructor_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.generation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcretePriorCosts.generation_bound
