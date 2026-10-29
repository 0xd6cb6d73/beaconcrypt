-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainSource

/-! The initialized original full-ledger frontend discharges the native unchecked audit from its own retained chronological trace. The resulting two-pass native key client is exactly the actual concrete early-provider execution, retaining the full result, trace, ordinary World, pool and phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedActual
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open RegistrationNativeSecretWordNativePlain (NativeFrame)
open RegistrationNativeSecretWordNativePlainProvider (embed)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
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

noncomputable def client :=
  let frame := embed candidate (RegistrationNativeSecretWordCheckedClosure.drop (RegistrationNativeSecretWordInterpreter.initial ordinary kem))
  RegistrationNativeKeyCompiler.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside target)
    (RegistrationNativeRetainedService.client
      (RegistrationNativeG3NativeCheckedClient.retained setup wire route sign
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
          bounds mode work (before.eval candidate)) frame.1 frame.2)) RegistrationNativeKeyPhases.emptyMeta

/-- Original cold-session initialization derives the clean native audit internally and preserves the complete actual two-pass client output. -/
theorem client_source (empty : before.server.sessions = []) :
    client setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
      target selected pairs publicKey challenge candidate work before ordinary kem =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        RegistrationNativeSecretWordNativePlainSource.run setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
          bounds mode seed scalar target selected pairs publicKey challenge candidate work before ordinary kem := by
  apply RegistrationNativeG3NativeCheckedClient.client_source
  intro result reached
  have clean := RegistrationNativeSecretWordNativePlainSource.no_bad setup checks wire source route sign
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target selected pairs publicKey challenge candidate
    work before ordinary kem empty result reached
  have same := congrArg Prod.snd (RegistrationNativeG3NativeCheckedTrace.read_native setup seed scalar result.1.2.events)
  exact same.symm.trans clean

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedActual
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedActual.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedActual.client_source
