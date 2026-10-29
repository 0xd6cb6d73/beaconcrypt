-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSafety
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveTrace

/-! The actual initialized symbolic frontend derives every preparation certificate internally. The checked and flag-enforcing interpreters consequently agree on the entire original raw/secrecy ledger, with or without the complete chronological observer. No caller certificate or whole-game equality is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider State handler)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source) (empty : before.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

include empty

/-- The actual complete chronological observer retains derived preparation at every supported demand in the initialized original native game. -/
theorem traced_prepared :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program
        (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before))
      (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  RegistrationNativeSecretWordLiveTrace.program setup wire route sign input inside provider _ _ _
    (RegistrationNativeSecretWordLiveFlags.initial input ordinary kem)
    (RegistrationNativeSecretWordLiveFrontendSafety.run setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before empty ordinary kem)

/-- Enforcing actual preparation flags leaves the complete initialized native ledger and every reached protocol/private state literal. -/
theorem run_source :
    (simulateQ (handlerChecked setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before)).run
        (RegistrationNativeSecretWordInterpreter.initial ordinary kem) =
    (simulateQ (handler setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before)).run
        (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  RegistrationNativeSecretWordInterpreterChecked.program_source setup wire route sign input inside provider _ _
    (RegistrationNativeSecretWordLiveFrontendSafety.run setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before empty ordinary kem)

/-- The exact same flag substitution preserves the complete ordered preparation, demand, getter and installation trace, including all failed attempts. -/
theorem traced_source :
    (simulateQ (handlerChecked setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program
        (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before))).run
          (RegistrationNativeSecretWordInterpreter.initial ordinary kem) =
    (simulateQ (handler setup wire route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program
        (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before))).run
          (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  RegistrationNativeSecretWordInterpreterChecked.program_source setup wire route sign input inside provider _ _
    (traced_prepared setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before empty ordinary kem)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource.traced_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource.traced_prepared
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource.run_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource.traced_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendSource.traced_source
