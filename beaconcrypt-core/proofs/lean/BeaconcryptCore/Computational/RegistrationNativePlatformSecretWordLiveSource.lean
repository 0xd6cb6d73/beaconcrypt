-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveTrace
/-! The literal corrected initialized Word frontend derives preparation internally. Enforcing the reached flags preserves the entire current raw ledger and chronological observer, including mutable platform, provider and source failure states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider handler)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativePlatformSecretWordOrdinary (State)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : State source Platform) (empty : before.1.server.sessions = [])
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "game" => RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  serverKeyId bounds mode work before
local notation "initial" => RegistrationNativeSecretWordInterpreter.initial ordinary kem
include empty

/-- Every material request of the actual initialized chronological source tree is prepared at its reached cut. -/
theorem traced_prepared :
    AllPrepared input (handlerChecked setup canonical route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program game) initial :=
  RegistrationNativeSecretWordLiveTrace.program setup canonical route sign input inside provider _ _ _
    (RegistrationNativeSecretWordLiveFlags.initial input ordinary kem)
    (RegistrationNativePlatformSecretWordLiveSafety.run setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty ordinary kem)

/-- Flag enforcement preserves the full actual initialized source ledger, roster, provider and common platform result. -/
theorem run_source :
    (simulateQ (handlerChecked setup canonical route sign input inside provider) game).run initial =
      (simulateQ (handler setup canonical route sign input inside provider) game).run initial :=
  RegistrationNativeSecretWordInterpreterChecked.program_source setup canonical route sign input inside provider _ _
    (RegistrationNativePlatformSecretWordLiveSafety.run setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty ordinary kem)

/-- The same derived flags preserve every ordered prepare, demand and install observation of that exact source execution. -/
theorem traced_source :
    (simulateQ (handlerChecked setup canonical route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program game)).run initial =
    (simulateQ (handler setup canonical route sign input inside provider)
      (RegistrationNativeSecretWordFrontendTrace.program game)).run initial :=
  RegistrationNativeSecretWordInterpreterChecked.program_source setup canonical route sign input inside provider _ _
    (traced_prepared setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty ordinary kem)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource.traced_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource.traced_prepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource.traced_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSource.traced_source
