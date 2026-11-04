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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots
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

/-- The actual startup and joint source body derive their physical slot projection, transporting only the prior origins relation. -/
theorem startup (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (physicalBefore : RegistrationNativePlatformLorIdealPhysical.State n (PqxdhRecordLiftIdeal.CtxPrivate n))
    (prior : RegistrationNativePlatformRecordSlotGhost.initial.origins=RegistrationNativePlatformRecordSlotControl.origins physicalBefore.2.1)
    (result : _) (supported : result∈support
      (RegistrationNativePlatformRecordPartnerJointStartup.joint setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (physical(route)) ensureInit identityIndex serverKeyId previous
        privateBefore bounds mode adversary physicalBefore)) :
    RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot=PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.1 := by
  unfold RegistrationNativePlatformRecordPartnerJointStartup.joint at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨started,called,continued⟩ := supported
  have kept := RegistrationNativePlatformRecordPartnerJointInitial.startup service codec route setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) physicalBefore started called
  have initial := prior.trans kept.symm
  cases built : started.1 with
  | none=>
    simp only [built,mem_support_pure_iff] at continued
    cases continued
    exact RegistrationNativePlatformRecordSlotGhost.slots_of_origins _ _ initial
  | some born=>
    simp only [built,support_map] at continued
    obtain ⟨body,bodyCalled,rfl⟩ := continued
    exact RegistrationNativePlatformRecordPartnerJointPhysical.run service codec route setup wire
      (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider checks source selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) (born.native.frontend,previous)
      (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,started.2)) initial body bodyCalled

/-- The complete original uniform-source sampler/startup lift derives its physical slot map internally, with no source-state or slot-map premise. -/
theorem initialized (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1)) (previous : Platform)
    (result : _) (supported : result∈support
      (RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)) :
    RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot=PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.1 := by
  unfold RegistrationNativePlatformRecordPartnerJointUniform.joint at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨parameters,sampled,continued⟩ := supported
  have frame := RegistrationNativePlatformRecordPartnerSampler.frame
    (PqxdhRecordLiftIdeal.ctxInterpreter (fun _ => .random) id setup codec) codec route
    (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget selected)
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial) parameters sampled
  have prior : RegistrationNativePlatformRecordSlotGhost.initial.origins=
      RegistrationNativePlatformRecordSlotControl.origins parameters.2.2.1 := by
    rw [frame.2]
    exact RegistrationNativePlatformRecordSlotCursor.cold
  exact startup setup checks wire source parameters.1.seed parameters.1.scalar parameters.1.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.1.profile.pairs parameters.1.profile.publicKey parameters.1.profile.challenge parameters.1.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route ensureInit identityIndex serverKeyId previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.1.materials)
    bounds mode adversary parameters.2 prior result continued
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots.startup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointSlots.initialized
