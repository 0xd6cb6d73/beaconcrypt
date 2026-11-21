-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginConcreteCodec
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
/-! The original initialized runtime produced/raw event reaches one all-random gated record client. The bound retains the original startup, one KEM shift, one initialized recovery client, and one complete-prefix client for each ordered record reduction. Primitive security remains expressed by its explicit advantages. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample after program)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_run)
open PqxdhRecordLiftCtxBills (effectBill worldBill)
variable (budget : PqxdhDeploymentInterface.Budget)
    (selected : Fin (budget.create + 1)) (previous : Platform)
local notation "work" => program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous


local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route


omit primitive in
private theorem program_conflict {Context : Type}
    (body : OracleComp (PqxdhRecordLiftInterface.WorldSpec (budget.cap 4+budget.cap 5)) (RegistrationNativeEntropyRun.Outcome Context Value))
    (warm : PqxdhRecordLiftIdeal.CtxPrivate (budget.cap 4+budget.cap 5)) :
    (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      (simulateQ service (RegistrationNativeRecordOriginProgram.program codec route body)).run warm=
      (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
        CborRawRecordOriginFlatten.interpret service codec route body
          CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl warm := by
  simp only [RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,
    CborRecordWorldClient.client,PqxdhRecordLiftProtocol.schedule,CborRawRecordOriginFlatten.interpret,
    simulateQ_map,StateT.run_map,Functor.map_map]

/-- The final cache conflict of the actual complete joint sampler/startup run is exactly the conflict observer of the same whole record source program. No warm state or sampler charge is reset. -/
theorem conflict_source :
    (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2.2.2.2.2) <$>
      RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous=
    (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      (simulateQ service (RegistrationNativeRecordOriginProgram.program codec route work)).run PqxdhRecordLiftIdeal.CtxPrivate.initial := by
  rw [program_conflict setup wire route budget]
  simp only [RegistrationNativePlatformG3UniformRecordProgram.program,CborRawRecordOriginFlatten.interpret_bind,map_bind,
    RegistrationNativePlatformRecordPartnerJointUniform.joint]
  rw [RegistrationNativePlatformLorIdealPhysical.program_source]
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  have framed:=RegistrationNativePlatformRecordPartnerSampler.frame service codec route (sample setup budget selected)
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial)
    (result.1.1.1,(result.1.1.2,(result.1.2,result.2))) ?_
  · change result.1.1.2=CborRecordWorldClient.initial ∧result.1.2=PqxdhRecordLiftProtocol.initialControl at framed
    simp only [RegistrationNativePlatformG3UniformRecordProgram.after]
    have joint:=RegistrationNativePlatformRecordBindingWarm.joint_source setup checks wire source
      result.1.1.1.seed result.1.1.1.scalar result.1.1.1.candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val result.1.1.1.profile.pairs
        result.1.1.1.profile.publicKey result.1.1.1.profile.challenge result.1.1.1.candidate)
      selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget result.1.1.1.materials)
      bounds mode adversary route (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id result.2
    have conflict:=RegistrationNativePlatformRecordBindingWarm.conflict_source setup checks wire source
      result.1.1.1.seed result.1.1.1.scalar result.1.1.1.candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val result.1.1.1.profile.pairs
        result.1.1.1.profile.publicKey result.1.1.1.profile.challenge result.1.1.1.candidate)
      selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget result.1.1.1.materials)
      bounds mode adversary route (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id result.2
    have combined:=(congrArg (Functor.map (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2)) joint).trans conflict
    rw [program_conflict setup wire route budget] at combined
    simpa only [Functor.map_map,framed.1,framed.2] using combined
  · rw [RegistrationNativePlatformLorIdealPhysical.program_source,support_map]
    exact ⟨result,supported,rfl⟩

private theorem joint_cross (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (result : _) (supported : result∈support
      (RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous))
    (crossed : PqxdhRecordLiftIdeal.CrossAccept codec route
      (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2.2.2.2.2 := by
  unfold RegistrationNativePlatformRecordPartnerJointUniform.joint at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨parameters,sampled,continued⟩:=supported
  have frame:=RegistrationNativePlatformRecordPartnerSampler.frame service codec route (sample setup budget selected)
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial) parameters sampled
  have same : parameters.2=(CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,parameters.2.2.2) :=
    Prod.ext frame.1 (Prod.ext frame.2 rfl)
  rw [same] at continued
  have actual : ((result.1,result.2.2.2.2.1),result.2.2.2.2.2)∈support
      (RegistrationNativePlatformRecordBindingWarm.run setup checks wire source parameters.1.seed parameters.1.scalar parameters.1.candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.1.profile.pairs
          parameters.1.profile.publicKey parameters.1.profile.challenge parameters.1.candidate)
        selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.1.materials)
        bounds mode adversary route (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id parameters.2.2.2) := by
    rw [←RegistrationNativePlatformRecordBindingWarm.joint_source,support_map]
    exact ⟨result,continued,rfl⟩
  exact RegistrationNativePlatformRecordBindingWarm.cross_conflict setup checks wire source parameters.1.seed parameters.1.scalar parameters.1.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.1.profile.pairs
      parameters.1.profile.publicKey parameters.1.profile.challenge parameters.1.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.1.materials)
    bounds mode adversary route (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) (by intro label impossible;cases impossible) id readback parameters.2.2.2
    ((result.1,result.2.2.2.2.1),result.2.2.2.2.2) actual
    ((RegistrationNativePlatformRecordBindingWarm.encoded_cross codec route _).mp crossed)

local notation "concreteCodec"=>RegistrationNativeWire.ledgerCodec
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire)

/-- The unchanged concrete joint source cross-accept event implies a digest conflict in that same actual final warm cache, with its codec law discharged internally. -/
theorem cross_conflict (result : _) (supported : result∈support
      (RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks RegistrationNativePlatformConcreteSource.wire route source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous))
    (crossed : PqxdhRecordLiftIdeal.CrossAccept concreteCodec route
      (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2.2.2.2.2 :=
  joint_cross setup checks RegistrationNativePlatformConcreteSource.wire route source ensureInit identityIndex serverKeyId selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous
    RegistrationNativePlatformOriginConcreteCodec.readback result supported crossed

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource.conflict_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource.conflict_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource.cross_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointConflictSource.cross_conflict
