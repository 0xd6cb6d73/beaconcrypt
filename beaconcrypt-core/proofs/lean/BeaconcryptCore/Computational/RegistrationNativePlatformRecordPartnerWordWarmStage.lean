-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordMarginal
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNativeSource
/-! The same actual warmed startup supplies every structural receipt for the public same-slot mismatch comparison. Its exposure event is the identical reached Word source execution used by the complete-prefix recovery bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmStage
open PqxdhServerAuthExperiment (Setup Checks Codec)
open PqxdhKemIndCca
open RegistrationNativePlatformG3UniformRecordProgram (Sample)
variable {I KemSK Platform E Secret Reader Response A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public →OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1)) (previous : Platform)
local notation "cap"=>budget.cap 4+budget.cap 5
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer reservePackets
variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec (budget.cap 4+budget.cap 5)) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "physical"=>RegistrationNativePlatformLorIdealPhysical.implementation service codec route
local notation "unused"=>RegistrationNativePlatformLorIdealSelected.unused (n:=cap)
local notation "privateState"=>RegistrationNativePlatformG3UniformOpaqueNative.privateState
  (KemSK:=KemSK) (ProviderState:=RegistrationNativeKemSwitchSource.Phase) none budget

/-- The literal initialized body mismatch reaches Exposure on that same actual source result, with all warm structural receipts derived internally. -/
theorem bound (parameters : Sample KemSK cap) (chosen : MlKem768PublicKey ×KemSK)
    (chosenPublic : chosen.1=parameters.profile.publicKey)
    (warm : Secret) (born : RegistrationNativeHiddenStartup.Started source)
    (after : RegistrationNativePlatformLorIdealPhysical.State cap Secret)
    (startup : (some born,after)∈support ((simulateQ physical
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys parameters.seed))).run
        (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,warm))))
    (owner : Fin budget.capacity) (selectedEq : selected.val=owner.val) :
    Pr{let result←(simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire
      (RegistrationNativeMldsa.owned source born.native.credential) parameters.seed parameters.scalar parameters.candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.profile.pairs parameters.profile.publicKey parameters.profile.challenge parameters.candidate)
      physical) (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source
          (RegistrationNativeMldsa.owned source born.native.credential) selected.val selectedAccept (setup.dh.publicKey parameters.scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
          (adversary ⟨setup.joint.publicKeys parameters.seed,born.native.credential.publicKey,serverKeyId⟩)
          (born.native.frontend,previous)))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateState parameters.materials,after))}[
      RegistrationNativePlatformRecordPartnerWordMarginal.MismatchAt (source:=source) selectedAccept budget owner
        (RegistrationNativePlatformRecordPartnerSnapshotSource.project result)]≤
    Pr{let flag←(RegistrationNativePlatformRecordPartnerExposureAveraged.after setup checks wire source selected.val selected.val selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical
      (fun _=>unused) parameters.candidate
      (some (RegistrationNativePlatformRecordPartnerExposureWarmPrefix.context setup source serverKeyId mode adversary budget previous parameters born after)))}[
        flag=true] := by
  have free : some born∈support (RegistrationNativeHiddenStartup.start (n:=cap) setup source ensureInit identityIndex serverKeyId
      (setup.joint.publicKeys parameters.seed)) := by
    apply OracleComp.support_simulateQ_run'_subset physical _ (CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,warm))
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst startup
  have cold:=RegistrationNativeG3NativeStartupFields.start_cold setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys parameters.seed) born free
  have initial:=RegistrationNativePlatformRecordPartnerWordWarmInitial.startup setup service codec route
    ensureInit identityIndex serverKeyId (setup.joint.publicKeys parameters.seed) previous (privateState parameters.materials) warm born after startup
  have lower:=RegistrationNativePlatformRecordPartnerWordMarginal.mismatch_bound setup checks source
    parameters.seed parameters.scalar parameters.profile.pairs chosen parameters.profile.challenge selected.val selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys parameters.seed,born.native.credential.publicKey,serverKeyId⟩) parameters.candidate
    born.native.credential service codec route (born.native.frontend,previous) cold.1 cold.2.2 cold.2.1
    (privateState parameters.materials) after (RegistrationNativePlatformRecordPartnerWordWarmInitial.cold_private budget parameters.materials)
    initial.1 rfl rfl initial.2 budget owner selectedEq
  rw [chosenPublic] at lower
  have exactSource:=RegistrationNativePlatformRecordPartnerExposureNativeSource.full setup checks wire source selected.val selected.val selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical
    (fun _=>unused) parameters.candidate
    (RegistrationNativePlatformRecordPartnerExposureWarmPrefix.context setup source serverKeyId mode adversary budget previous parameters born after)
  have canonicalId : RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire=wire := rfl
  rw [canonicalId] at exactSource
  simp only [RegistrationNativePlatformRecordPartnerExposureWarmPrefix.context] at exactSource
  have roots :
      (RegistrationNativePlatformLorIdealInitial.symbolicPrivate (privateState parameters.materials)).2=
        ({RegistrationNativeHiddenService.initial with materials:=RegistrationNativeG3LocalMaterialCompletedSource.cache parameters.materials},∅) := rfl
  simp only [←roots,Prod.mk.eta] at exactSource
  simp only [RegistrationNativePlatformLorIdealSelected.sourceBefore] at lower
  rw [exactSource,prEvent_map] at lower
  simpa only [RegistrationNativePlatformRecordPartnerExposureAveraged.after,RegistrationNativePlatformRecordPartnerExposureWarmPrefix.context,prEvent_map,decide_eq_true_eq] using lower
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmStage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmStage.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWordWarmStage.bound
