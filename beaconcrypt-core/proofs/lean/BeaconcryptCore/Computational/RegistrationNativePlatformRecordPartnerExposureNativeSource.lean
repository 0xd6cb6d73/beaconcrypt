-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarmPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution
/-! The exposure runner and the literal complete source compiler differ only by product association. The same original value, ledger, frontend/platform, Word trace, symbolic private state and reached physical state remain joint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNativeSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativePlatformRecordPartnerExposureAveraged (Context)
variable {n : Nat} {I KemSK Physical Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (selected selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "Ctx"=>Context source n KemSK Physical Platform A mode
local notation "Trace"=>RegistrationNativeSecretWordFrontendTrace.State
local notation "FrontResult"=>((A ×RegistrationNativeLedger.State) ×RegistrationNativePlatformSecretWordOrdinary.State source Platform)
local notation "ClientResult"=>((FrontResult ×Trace) ×RegistrationNativePlatformRecordPartnerExposureClient.Private n KemSK Physical)


/-- The actual whole source result is the exact association of the same exposure run, with no existential choice of a Word lift. -/
theorem full (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (candidate : Secret) (context : Ctx) :
    RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      serverKeyId bounds
      (RegistrationNativePlatformLorStatefulSupport.traced
        (RegistrationNativePlatformLorCtxClosed.implementation setup wire context.sign context.seed context.scalar candidate (unused candidate)
          selected context.profile.pairs context.profile.publicKey context.profile.challenge physical)
        (RegistrationNativePlatformSecretWordFrontend.handler (n:=n) setup checks
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source context.sign selectedOwner selectedAccept
          (setup.dh.publicKey context.scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer))
      mode context.work (context.front,(RegistrationNativeSecretWordFrontendTrace.initial,
        ((context.word,({RegistrationNativeHiddenService.initial with materials:=context.materials},context.known)),context.physical)))=
    (fun result=>(result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      RegistrationNativePlatformRecordPartnerExposureAveraged.native setup checks wire source selected selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical unused candidate context := by
  exact RegistrationNativePlatformLorSourceExecution.full_run
    (RegistrationNativePlatformLorStatefulSupport.trace
      (RegistrationNativePlatformLorCtxClosed.implementation setup wire context.sign context.seed context.scalar candidate (unused candidate)
        selected context.profile.pairs context.profile.publicKey context.profile.challenge physical))
    setup checks wire source context.sign selectedOwner selectedAccept (setup.dh.publicKey context.scalar) view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode context.work
    (context.front,(RegistrationNativeSecretWordFrontendTrace.initial,
      ((context.word,({RegistrationNativeHiddenService.initial with materials:=context.materials},context.known)),context.physical)))
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNativeSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNativeSource.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNativeSource.full
