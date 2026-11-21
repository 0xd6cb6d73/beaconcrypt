import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHiddenCore
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHidden
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


def Holds (result : Outcome (State n KemSK ProviderState Platform source) Value ×
    (RegistrationNativePlatformPublicRecordSlots.State n × RegistrationNativeG2Trace.State ×
      RegistrationNativePlatformLorIdealPhysical.State n (PqxdhRecordLiftIdeal.CtxPrivate n))) : Prop :=
  match result.1 with
  | none=>True
  | some observed=>RegistrationNativeInstallOrdinals.Hidden result.2.2.1.events observed.2.1.2.transcript
      (PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.1)
      (RegistrationNativePlatformInstallKernelStorage.Selected setup seed scalar candidate)

/-- Actual startup derives the selected-message invariant in the same full joint source result, retaining its warm private state. -/
theorem startup (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (secret : PqxdhRecordLiftIdeal.CtxPrivate n)
    (result : _) (supported : result∈support
      (RegistrationNativePlatformRecordPartnerJointStartup.joint setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (physical(route)) ensureInit identityIndex serverKeyId previous
        privateBefore bounds mode adversary (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,secret))) :
    Holds setup source seed scalar candidate result := by
  unfold RegistrationNativePlatformRecordPartnerJointStartup.joint at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨started,called,continued⟩ := supported
  cases built : started.1 with
  | none=>
      simp only [built,mem_support_pure_iff] at continued
      cases continued
      trivial
  | some born=>
      simp only [built,support_map] at continued
      obtain ⟨body,bodyCalled,rfl⟩ := continued
      have startupCalled : (some born,started.2)∈support ((simulateQ (physical(route))
          (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run
            (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,secret)) := by
        simpa only [←built,Prod.mk.eta] using called
      have prior := RegistrationNativePlatformRecordPartnerJointHiddenInitial.startup setup service codec route
        ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) previous privateBefore secret born started.2 startupCalled
      exact RegistrationNativePlatformRecordPartnerJointHiddenCore.body setup checks wire source seed scalar candidate provider
        selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route born.native.credential
        serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
        (born.native.frontend,previous) privateBefore started.2.1 started.2.2.1 started.2.2.2 prior body bodyCalled
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHidden.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointHidden.startup
