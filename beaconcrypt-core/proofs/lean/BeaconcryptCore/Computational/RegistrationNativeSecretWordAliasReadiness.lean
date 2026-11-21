-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTraceSource

/-! Native preparation safety follows from the actual initialized symbolic frontend and its same-run chronology. The real suffix interpretation can only shrink open-program support, so the property survives its literal full-state source equality. No caller readiness certificate is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordInterpreter (Provider initial)
open RegistrationNativeSecretWordNativeReadinessTrace (read readNative)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (before : RegistrationNativeSecretWordMessage.State source) (empty : before.server.sessions = [])
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

include empty

/-- Every actual alias-client outcome has a native chronological certificate derived internally from the initialized full frontend. -/
theorem client_no_bad
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign
      (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode work before ordinary kem)) :
    (read setup seed scalar candidate result.1.2).bad = false := by
  simp only [RegistrationNativeSecretWordAliasClient.client, RegistrationNativeSecretWordInterpreter.execute] at supported
  rw [← RegistrationNativeSecretWordLiveFrontendSource.traced_source setup checks wire source route sign
    (input setup.joint setup.dh seed scalar) inside provider selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode work before empty ordinary kem] at supported
  exact RegistrationNativeSecretWordNativeReadinessTraceSource.initialized_no_bad setup wire route sign inside provider seed scalar candidate
    checks source selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before empty ordinary kem result supported

abbrev NativeResult (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK Value : Type) :=
  ((((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) ×
    RegistrationNativeG2Trace.State) × RegistrationNativeSecretWordCheckedClosure.Frame n KemSK)

omit empty in
noncomputable def nativeRun : OracleComp RegistrationNativeKeyCompiler.KeySpec (NativeResult source n KemSK Value) :=
  (simulateQ (RegistrationNativeSecretWordCheckedClosure.plain setup wire route sign
    (input setup.joint setup.dh seed scalar) inside provider candidate)
      (simulateQ (RegistrationNativeSecretWordCheckedFrontend.erase ∘ₛ
        RegistrationNativeSecretWordCheckedFrontend.native setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (RegistrationNativeG2Trace.program
          (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
            bounds mode work (before.eval candidate))))).run
    (RegistrationNativeSecretWordCheckedClosure.drop (initial ordinary kem))

/-- The literal native chronological source has no unprepared valid demand, even after interpreting the same alias client at its real suffix and full byte-table addresses. -/
theorem native_no_bad (result : NativeResult source n KemSK Value)
    (supported : result ∈ support (nativeRun setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode inside provider candidate seed scalar work before ordinary kem)) :
    (readNative setup seed scalar result.1.2.events).bad = false := by
  simp only [nativeRun] at supported
  rw [RegistrationNativeSecretWordAliasSource.run_source setup checks wire source route sign
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode inside provider candidate seed scalar work before empty ordinary kem] at supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  rw [support_map] at original
  obtain ⟨actual, reached, equal⟩ := original
  cases equal
  change (readNative setup seed scalar (RegistrationNativeSecretWordCheckedTrace.state candidate actual.1.2).events).bad = false
  rw [RegistrationNativeSecretWordNativeReadinessTrace.evaluated_read]
  exact client_no_bad setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode inside provider candidate seed scalar work before empty ordinary kem actual reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness.client_no_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness.client_no_bad
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness.native_no_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness.native_no_bad
