-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClient
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyClosure
/-! The genuine open-retained key compiler closes on any actual new public query tree at the same private ordinary/provider state. The finite key-source comparison uses only that very tree's clean preparation trace, leaving the corrected frontend source receipt to discharge cleanliness separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3OpenClosure
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordNativePlain (NativeFrame NativeProvider)
variable {n : Nat} {I KemSK ProviderState A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : RegistrationNativeProviderInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (previous : PqxdhLiveKemBirth.Pool KemSK × ProviderState)

private theorem client_map {A B : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (map : A → B) (work : OracleComp RegistrationNativeRetainedService.Spec A) :
    RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client (map <$> work)) RegistrationNativeKeyPhases.emptyMeta =
      map <$> RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work) RegistrationNativeKeyPhases.emptyMeta := by
  simp only [RegistrationNativeKeyCompiler.client, RegistrationNativeRetainedService.client,
    simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]


noncomputable def client :=
  (simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
    (RegistrationNativeOpenKey.client setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside target)
      (RegistrationNativeOpenRetained.client setup wire route sign
        (RegistrationNativeG2Trace.program work) ordinary))).run' previous

noncomputable def plain :=
  RegistrationNativeG3NativeCheckedClient.plain setup wire route sign seed scalar target provider work
    (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear ordinary)) previous

/-- The genuine open-retained execution equals the same native finite-key execution, retaining its complete returned value and chronology. -/
theorem client_source
    (clean : ∀ result ∈ support (plain setup wire route sign seed scalar target provider work ordinary previous),
      (RegistrationNativeG3NativeCheckedTrace.read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) result.1.2.events).2 = false) :
    client setup wire route sign seed scalar target provider work ordinary previous =
      Prod.fst <$> plain setup wire route sign seed scalar target provider work ordinary previous := by
  rw [client, RegistrationNativeOpenKeyClosure.key_close]
  have actual := RegistrationNativeG3NativeCheckedClient.client_source setup wire route sign seed scalar target provider work
    (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear ordinary)) previous clean
  let full := RegistrationNativeG3NativeCheckedClient.retained setup wire route sign provider work
    (RegistrationNativeOpenRetained.mask (RegistrationNativePublicRetained.clear ordinary)) previous
  have wrapped : (simulateQ (RegistrationNativeOpenRetainedSource.close provider)
      (RegistrationNativeOpenRetained.client setup wire route sign (RegistrationNativeG2Trace.program work) ordinary)).run' previous =
      (fun result => result.1.1) <$> full := by
    simp only [full, RegistrationNativeG3NativeCheckedClient.retained, RegistrationNativeOpenRetained.client,
      StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  rw [wrapped, client_map]
  change (fun result => result.1.1) <$>
    RegistrationNativeKeyCompiler.client setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside target) (RegistrationNativeRetainedService.client full)
      RegistrationNativeKeyPhases.emptyMeta = _
  rw [actual]
  simp only [Functor.map_map, plain]

end BeaconcryptCore.Computational.RegistrationNativePlatformG3OpenClosure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3OpenClosure.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3OpenClosure.client_source
