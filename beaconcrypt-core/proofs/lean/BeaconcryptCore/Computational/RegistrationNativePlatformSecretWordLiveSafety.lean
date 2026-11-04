-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLivePost
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBeacon
/-! Preparation safety follows from the actual corrected material controllers and their reached live-reference receipts. Adaptive continuations retain the same platform and checked provider states through the literal raw compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveSessions (Live)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativePlatformSecretWordLiveState (Good)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
local notation "impl" => handlerChecked setup wire route sign input inside provider

private theorem finish_prepared (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform)
    (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (valid : RegistrationNativeSecretWordLiveFlags.Valid input context) :
    AllPrepared input impl ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK)
      setup wire source index packet).run before) context := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run]
  cases found : before.1.beacons[index]? with
  | none => exact RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider _ context valid (by trivial)
  | some owner =>
    apply RegistrationNativeSecretWordLiveFrontendSafety.mapped setup wire route sign input inside provider _ _ context valid
    have prepared := RegistrationNativePlatformSecretWordLiveBeacon.finish setup wire route sign input inside provider
      owner.scalar source packet owner.view before.1.environment context valid
    cases own : owner.scalar with
    | none => simpa only [RegistrationNativeSecretWordLiveBeaconSafety.close,
        RegistrationNativeSecretWordLiveBeaconPreparation.routing, own, StateT.run] using prepared
    | some scalar => simpa only [RegistrationNativeSecretWordLiveBeaconSafety.close,
        RegistrationNativeSecretWordLiveBeaconPreparation.routing, own, StateT.run, QueryImpl.simulateQ_compose] using prepared

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "typed" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

private theorem quiet (current : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (ordinary : ¬RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial current)
    (before : State source Platform) (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (good : Good input before context) : AllPrepared input impl ((typed current).run before) context := by
  apply RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider _ context good.1
  have bounded := RegistrationNativePlatformSecretWordFrontendCaps.handler_bound (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer current before
  simpa only [ite_eq_right ordinary] using bounded

/-- Every actual corrected callback demands only a name prepared in its own reached checked execution. -/
theorem query (current : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform) (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (good : Good input before context) : AllPrepared input impl ((typed current).run before) context := by
  cases current with
  | inl coin =>
    exact quiet setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer _ (by simp only [RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial, RegistrationNativeSecretWordFrontendCaps.IsMaterial, not_false_eq_true]) before context good
  | inr command => cases command with
    | build handle application =>
      exact RegistrationNativePlatformSecretWordLiveBuild.prepared setup wire route sign input inside provider view failure allocation
        erased helper writer reservePeer source handle application before context good.1 good.2
    | finish index packet => exact finish_prepared setup wire route sign input inside provider source index packet before context good.1
    | _ =>
      exact quiet setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer _ (by simp only [RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial, RegistrationNativeSecretWordFrontendCaps.IsMaterial, not_false_eq_true]) before context good

/-- Every supported adaptive continuation retains internally derived preparation before its next material query. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State source Platform) (context : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (good : Good input before context) :
    AllPrepared input impl ((simulateQ typed work).run before) context := by
  induction work using OracleComp.inductionOn generalizing before context with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact RegistrationNativeSecretWordLiveCaps.no_demand setup wire route sign input inside provider _ context good.1 (by trivial)
  | query_bind current next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply RegistrationNativeSecretWordLivePrefix.bind input impl _ _ context
      (query setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer current before context good)
    intro reached called
    have nextGood := RegistrationNativePlatformSecretWordLivePost.query setup wire route sign input inside provider checks source selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer current before context good reached called
    exact ih reached.1.1 reached.1.2 reached.2 nextGood

/-- Empty actual initial sessions derive preparation safety for every mode of the complete new raw Word frontend. -/
theorem run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform)
    (empty : before.1.server.sessions = []) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    AllPrepared input (handlerChecked setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider)
      (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)
      (RegistrationNativeSecretWordInterpreter.initial ordinary kem) :=
  program setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider checks source
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    before _ ⟨RegistrationNativeSecretWordLiveFlags.initial input ordinary kem,
      RegistrationNativeSecretWordLiveSessions.initial before.1.server _ empty⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveSafety.run
