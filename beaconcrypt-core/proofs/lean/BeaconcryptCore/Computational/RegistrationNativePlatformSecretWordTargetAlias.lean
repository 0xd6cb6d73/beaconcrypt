-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The actual current alias client closes to the same traced full-ledger kernel. Its ordered source path is derived from the complete result, retaining the persistent platform state and actual private provider. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (route : RawCtxServerRouting.SenderDecoder) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)


variable (outer : QueryImpl Combined ProbComp)
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "traced" => RegistrationNativePlatformSecretWordExecution.traced setup
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller
local notation "actual" => RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  route input inside provider serverKeyId bounds mode work before ordinary kem

/-- Reassociate the actual complete alias result without dropping any native or private coordinate. -/
def observed (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform) :
    RegistrationNativeEvents.Observed A (RegistrationNativePlatformSecretWordExecution.TracedState
      (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK) :=
  (result.1.1.1.1, (result.1.1.1.2, (result.1.1.2, (result.1.2, result.2))))

/-- The exact current dynamic client and full original raw compiler have one joint result, including its original ledger and trace. -/
theorem closed_source :
    observed source <$> simulateQ outer actual =
      RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds traced mode work
        (before, (RegistrationNativeSecretWordFrontendTrace.initial, RegistrationNativeSecretWordInterpreter.initial ordinary kem)) := by
  have actualRun := RegistrationNativePlatformSecretWordExecution.run_trace setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller
    serverKeyId bounds mode work
    (before, (RegistrationNativeSecretWordFrontendTrace.initial, RegistrationNativeSecretWordInterpreter.initial ordinary kem))
  have inverse := congrArg (Functor.map (observed (source := source) (Platform := Platform))) actualRun
  simp only [Functor.map_map, observed] at inverse
  simp only [RegistrationNativePlatformSecretWordAliasClient.client, RegistrationNativeSecretWordInterpreter.execute,
    RegistrationNativeSecretWordFrontendTrace.program, RegistrationNativePlatformSecretWordFrontend.run]
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  simpa only [RegistrationNativeSecretWordTargetSource.implementation, Prod.eta, id_map'] using inverse.symm

/-- The current complete alias result supplies its own exact original transcript path, with all intermediate source and platform states. -/
theorem actual_path (result : RegistrationNativePlatformSecretWordAliasClient.Result source n KemSK A Platform)
    (supported : result ∈ support (simulateQ outer actual)) :
    RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds traced)
      (RegistrationNativeLedger.empty,
        (before, (RegistrationNativeSecretWordFrontendTrace.initial, RegistrationNativeSecretWordInterpreter.initial ordinary kem)))
      result.1.1.1.2.transcript (observed source result).2 := by
  have actualSupport := Set.mem_image_of_mem (observed source) supported
  rw [← support_map, closed_source setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    route input inside provider serverKeyId bounds mode work before ordinary kem outer] at actualSupport
  exact (RegistrationNativePlatformSecretWordTargetPath.run setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller
    serverKeyId bounds mode work
    (before, (RegistrationNativeSecretWordFrontendTrace.initial, RegistrationNativeSecretWordInterpreter.initial ordinary kem))
    (observed source result) actualSupport).1

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias.closed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias.closed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias.actual_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetAlias.actual_path
