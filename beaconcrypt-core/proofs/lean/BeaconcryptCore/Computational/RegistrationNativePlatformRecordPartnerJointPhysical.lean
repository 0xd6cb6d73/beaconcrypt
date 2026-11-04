-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursorSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotCursor
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {I KemSK ProviderState Reader Response Secret A V : Type} {base : OracleSpec I}
variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

private theorem cursor_source (work : OracleComp (WorldSpec n) V)
    (ghost : RegistrationNativePlatformRecordSlotGhost.State n) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    (fun result => ((result.1.1.1.1,result.1.1.2),(result.1.1.1.2,(result.1.2,result.2)))) <$>
      RegistrationNativePlatformRecordSlotCursor.interpret service codec route work ghost shell control secret =
    (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      CborRawRecordOriginFlatten.interpret service codec route (RegistrationNativePlatformRecordSlotGhost.program work ghost) shell control secret := by
  unfold RegistrationNativePlatformRecordSlotCursor.interpret
  rw [RegistrationNativePlatformRecordSlotCursorSource.program]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,CborRawRecordOriginFlatten.interpret]
  rfl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route
local notation "backend" => RegistrationNativePlatformRecordPartnerSlotInput.closed setup wire sign seed scalar candidate provider physical
local notation "native" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider

/-- The source raw-demand snapshot is the cursor's same actual installation ghost, jointly with the complete private backend and reached physical state. -/
theorem source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (safe : RegistrationNativePlatformPublicSlotKind.Safe work)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    (fun result => (((result.1.1,result.2.1),result.1.2.snapshot),result.2.2)) <$>
      (simulateQ backend (RegistrationNativePlatformPublicRecordSlots.program work ghost)).run (before,(shell,(control,secret))) =
    (fun result => ((result.1.1.1.1,result.1.1.2),(result.1.1.1.2,(result.1.2,result.2)))) <$>
      RegistrationNativePlatformRecordSlotCursor.interpret service codec route ((simulateQ native work).run before)
        ghost.snapshot shell control secret := by
  rw [cursor_source]
  have actual := RegistrationNativePlatformPublicRecordSlotSource.source setup wire sign seed scalar candidate provider work safe ghost before
  have closed := congrArg (fun tree => CborRawRecordOriginFlatten.interpret service codec route tree shell control secret) actual
  simp only [CborRawRecordOriginFlatten.interpret,simulateQ_map,StateT.run_map] at closed ⊢
  rw [closed]
  rw [RegistrationNativePlatformRecordPartnerSlotInput.closed,OracleComp.simulateQ_flattenStateT_run,
    ←QueryImpl.simulateQ_mapStateTBase_run,bind_pure_comp,RegistrationNativePlatformLorIdealPhysical.program_source]
  simp only [Functor.map_map,CborRawRecordOriginFlatten.interpret]

/-- Every supported raw-demand observer result derives its physical slot map from the same cursor execution, without a final slot-map premise. -/
theorem slots (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (safe : RegistrationNativePlatformPublicSlotKind.Safe work)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (prior : ghost.snapshot.origins=RegistrationNativePlatformRecordSlotControl.origins control)
    (result : (A × RegistrationNativePlatformPublicRecordSlots.State n) ×
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState × RegistrationNativePlatformLorIdealPhysical.State n Secret))
    (supported : result∈support ((simulateQ backend (RegistrationNativePlatformPublicRecordSlots.program work ghost)).run
      (before,(shell,(control,secret))))) :
    RegistrationNativePlatformRecordSlotGhost.slots result.1.2.snapshot=PqxdhRecordLiftIdeal.handleSlot result.2.2.2.1 := by
  have reached : (((result.1.1,result.2.1),result.1.2.snapshot),result.2.2) ∈ support
      ((fun current => ((current.1.1.1.1,current.1.1.2),(current.1.1.1.2,(current.1.2,current.2)))) <$>
        RegistrationNativePlatformRecordSlotCursor.interpret service codec route ((simulateQ native work).run before)
          ghost.snapshot shell control secret) := by
    rw [← source service codec route setup wire sign seed scalar candidate provider work safe ghost before shell control secret,support_map]
    exact ⟨result,supported,rfl⟩
  rw [support_map] at reached
  obtain ⟨current,called,equal⟩ := reached
  have ghostEq := congrArg (fun value => value.1.2) equal
  have controlEq := congrArg (fun value => value.2.2.1) equal
  change current.1.1.2=result.1.2.snapshot at ghostEq
  change current.1.2=result.2.2.2.1 at controlEq
  rw [←ghostEq,←controlEq]
  exact RegistrationNativePlatformRecordSlotCursor.projection service codec route ((simulateQ native work).run before)
    ghost.snapshot shell control prior secret current called

private theorem trace_safe (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (safe : RegistrationNativePlatformPublicSlotKind.Safe work) (trace : RegistrationNativeG2Trace.State) :
    RegistrationNativePlatformPublicSlotKind.Safe ((simulateQ RegistrationNativeG2Trace.handler work).run trace) := by
  intro before result clean supported
  have erased := congrArg (fun tree => (simulateQ RegistrationNativePlatformPublicSlotKind.handler tree).run before)
    (RegistrationNativeG2Trace.program_erase work trace)
  simp only [simulateQ_map,StateT.run_map] at erased
  apply safe before (result.1.1,result.2) clean
  rw [←erased,support_map]
  exact ⟨result,supported,rfl⟩

/-- The joint source descriptor/slot observer has the same derived physical slot map throughout any safe source program, with its original G2 chronology retained. -/
theorem program (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (safe : RegistrationNativePlatformPublicSlotKind.Safe work)
    (before : RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState (RegistrationNativePlatformLorIdealPhysical.State n Secret))
    (prior : before.1.snapshot.origins=RegistrationNativePlatformRecordSlotControl.origins before.2.2.2.2.1)
    (result : A × RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState (RegistrationNativePlatformLorIdealPhysical.State n Secret))
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate provider physical) work).run before)) :
    RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot=PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.2.1 := by
  rw [RegistrationNativePlatformRecordPartnerSlotTrace.program_source setup wire sign seed scalar candidate provider physical,support_map] at supported
  obtain ⟨current,called,rfl⟩ := supported
  exact slots service codec route setup wire sign seed scalar candidate provider
    ((simulateQ RegistrationNativeG2Trace.handler work).run before.2.1) (trace_safe work safe before.2.1)
    before.1 before.2.2.1 before.2.2.2.1 before.2.2.2.2.1 before.2.2.2.2.2 prior current called

variable {Platform E : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (checks : PqxdhServerAuthExperiment.Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


/-- The literal current raw frontend derives its safe source observer internally. Only the initial ghost/control relation is transported; the final slot-map equation is a conclusion. -/
theorem run (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (before : RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState (RegistrationNativePlatformLorIdealPhysical.State n Secret))
    (prior : before.1.snapshot.origins=RegistrationNativePlatformRecordSlotControl.origins before.2.2.2.2.1)
    (result : ((A × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) ×
      RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK ProviderState (RegistrationNativePlatformLorIdealPhysical.State n Secret))
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider physical)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front))).run before)) :
    RegistrationNativePlatformRecordSlotGhost.slots result.2.1.snapshot=PqxdhRecordLiftIdeal.handleSlot result.2.2.2.2.2.1 :=
  program service codec route setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider _
    (RegistrationNativePlatformPublicSlotSafety.run setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)
    before prior result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.slots
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical.run
