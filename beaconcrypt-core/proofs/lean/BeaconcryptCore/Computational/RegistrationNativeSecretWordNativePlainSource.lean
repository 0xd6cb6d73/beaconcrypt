-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainProvider

/-! The initialized native full-ledger chronological execution uses the actual early candidate provider and derives preparation safety internally. Exact finite closure and provider state maps retain the original result, ledger, frontend, chronological events, ordinary World and complete concrete indexed pool/phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeSecretWordNativePlain (NativeFrame native)
open RegistrationNativeSecretWordNativePlainProvider (embed)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Result (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK Value : Type) :=
  ((((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State) ×
    NativeFrame n KemSK (PqxdhLiveKemBirth.Pool KemSK × RegistrationNativeKemSwitchSource.Phase))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (target : Option PqxdhJointIdentity.DhOutput) (selected : Nat)
  (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (before : RegistrationNativeSecretWordMessage.State source)
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

noncomputable def run : OracleComp RegistrationNativeKeyCompiler.KeySpec (Result source n KemSK Value) :=
  (simulateQ (native setup wire route sign seed scalar target
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate))
    (RegistrationNativeG2Trace.program
      (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
        bounds mode work (before.eval candidate)))).run
    (embed candidate (RegistrationNativeSecretWordCheckedClosure.drop (RegistrationNativeSecretWordInterpreter.initial ordinary kem)))

/-- The same actual initialized native chronology is the exact finite source map of the combined alias client. -/
theorem run_source :
    run setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
      target selected pairs publicKey challenge candidate work before ordinary kem =
      Prod.map id (embed candidate) <$>
        RegistrationNativeSecretWordAliasReadiness.nativeRun setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
          bounds mode (RegistrationNativeSecretWordProtection.inside target)
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
          candidate seed scalar work before ordinary kem := by
  simp only [run]
  rw [← RegistrationNativeSecretWordNativePlainProvider.program_source]
  rw [← RegistrationNativeSecretWordNativePlain.program_source]
  rfl

/-- Every outcome of the actual initialized native early-provider execution has no valid demand without its original successful preparation. -/
theorem no_bad (empty : before.server.sessions = []) (result : Result source n KemSK Value)
    (supported : result ∈ support
      (run setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
        target selected pairs publicKey challenge candidate work before ordinary kem)) :
    (RegistrationNativeSecretWordNativeReadinessTrace.readNative setup seed scalar result.1.2.events).bad = false := by
  rw [run_source] at supported
  rw [support_map] at supported
  obtain ⟨actual, reached, equal⟩ := supported
  cases equal
  change (RegistrationNativeSecretWordNativeReadinessTrace.readNative setup seed scalar actual.1.2.events).bad = false
  exact RegistrationNativeSecretWordAliasReadiness.native_no_bad setup checks wire source route sign
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode (RegistrationNativeSecretWordProtection.inside target)
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
    candidate seed scalar work before empty ordinary kem actual reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource.run_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource.no_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource.no_bad
