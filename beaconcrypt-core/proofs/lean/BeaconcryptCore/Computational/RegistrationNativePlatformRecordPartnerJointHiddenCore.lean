import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointG2Source
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenInitial
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The genuine effectful constructor, generated credential, shared pin hash and complete corrected dynamic source run have the gated native environment interpretation. Physical allocation is derived from the actual interpreted startup, and all original value, ledger, private/provider, cursor, Protocol, service and persistent platform poststates are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenCore
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



open RegistrationNativeHiddenEnvironmentWorld (lower)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeEntropyRun (Outcome)



local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
local notation "physical(" route ")" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route


/-- The selected-message hidden-handle invariant belongs to this exact joint source result, after dropping only its private slot observer. -/
theorem body (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : PqxdhRecordLiftIdeal.CtxPrivate n)
    (prior : RegistrationNativePlatformInstallKernelStorage.Valid
      (RegistrationNativeG2Trace.initial,((((front,privateBefore),shell),control),secret)))
    (result : _) (supported : result∈support
      ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (physical(route)))
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
            serverKeyId bounds mode work front))).run
          (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,(shell,control,secret))))) :
    RegistrationNativeInstallOrdinals.Hidden result.2.2.1.events result.1.1.2.transcript
      (PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.2.1)
      (RegistrationNativePlatformInstallKernelStorage.Selected setup seed scalar candidate) := by
  have projected := RegistrationNativePlatformRecordPartnerJointG2Source.source setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider (physical(route))
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
        selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds mode work front)) privateBefore (shell,control,secret)
    RegistrationNativePlatformPublicRecordSlots.initial RegistrationNativeG2Trace.initial
  rw [RegistrationNativePlatformLorIdealPhysical.program_source] at projected
  have reached := Set.mem_image_of_mem (fun current=>(((current.1,current.2.2.1),current.2.2.2.1),current.2.2.2.2)) supported
  rw [←support_map,projected,support_map] at reached
  obtain ⟨actual,called,equal⟩ := reached
  have named : actual=(((((result.1,result.2.2.1),result.2.2.2.1),result.2.2.2.2.1),result.2.2.2.2.2.1),result.2.2.2.2.2.2) := by
    exact congrArg (fun current=>(((((current.1.1.1,current.1.1.2),current.1.2),current.2.1),current.2.2.1),current.2.2.2)) equal
  rw [named] at called
  have kept := RegistrationNativePlatformInstallKernelTraceInvariant.run setup checks wire credential seed scalar candidate provider
    selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route
    serverKeyId bounds mode work
    (RegistrationNativeG2Trace.initial,((((front,privateBefore),shell),control),secret)) prior rfl _ called
  exact kept.2.2
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenCore.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenCore.body
