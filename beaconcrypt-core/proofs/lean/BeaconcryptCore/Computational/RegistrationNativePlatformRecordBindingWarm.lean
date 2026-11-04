-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBindingEvent
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The actual genuine startup and current gated native run retain cross-handle commitment evidence at an arbitrary reached CTX cache. Exact joint-source and conflict-observer projections retain sampler charges and all original failures. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm
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



open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (route : RawCtxServerRouting.SenderDecoder)
local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "reference" => RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram (n := n) setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
local notation "FullResult" => RegistrationNativeEntropyRun.Result n (State n KemSK ProviderState Platform source) Value

omit primitive in
private def project (result : ((RegistrationNativeEntropyRun.Outcome (State n KemSK ProviderState Platform source) Value ×
    CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n) : FullResult :=
  ((result.1.1.1,result.1.2),result.2)

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) (warm : CtxPrivate n) : ProbComp FullResult :=
  project source <$> CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route reference
    CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl warm

/-- The complete source reference after genuine startup derives cross-handle conflict in its own final private cache. No ledger, cache or source-frame premise is supplied. -/
theorem cross_conflict (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (warm : CtxPrivate n) (result : FullResult)
    (supported : result ∈ support (run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace warm))
    (crossed : PqxdhRecordLiftIdeal.CrossAccept codec route (RegistrationNativeRecordBindingEvent.view result)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2 := by
  rw [run, support_map] at supported
  obtain ⟨full, possible, rfl⟩ := supported
  unfold RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram at possible
  rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at possible
  obtain ⟨started, startReached, continued⟩ := possible
  rcases started with ⟨⟨⟨_ | born, shell⟩, control⟩, secret⟩
  · simp only [CborRawRecordOriginFlatten.interpret_pure, mem_support_pure_iff] at continued
    subst full
    simp only [RegistrationNativeRecordBindingEvent.view, project, PqxdhRecordLiftIdeal.CrossAccept,
      Option.map_none] at crossed
    obtain ⟨value, member, _⟩ := crossed
    cases member
  · have safe := (RegistrationNativeRecordHandleSlots.interpreted
      (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route _ _ _
      PqxdhRecordLiftProtocolHistory.initial_safe _ _ startReached).1
    apply RegistrationNativePlatformGatedNativeRecordBindingEvent.initialized_conflict modes ideal replace setup codec route readback
      (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
      (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)) serverKeyId bounds mode
      (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) born.created
      ((born.native.frontend,previous),privateBefore) shell control safe secret (project source full) _ crossed
    rw [RegistrationNativePlatformGatedNativeEntropy.run, support_map]
    exact ⟨full, continued, rfl⟩

/-- The actual startup source joint lift retains the same complete result, final controls and warm CTX cache as the source reference; only analysis slots/G2 and the outer shell are projected here. -/
theorem joint_source (modes : Label n→KeyMode) (replace : Pqxdh.Bytes→Pqxdh.Bytes) (warm : CtxPrivate n) :
    (fun result=>((result.1,result.2.2.2.2.1),result.2.2.2.2.2)) <$>
      RegistrationNativePlatformRecordPartnerJointStartup.joint setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (RegistrationNativePlatformLorIdealPhysical.implementation (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route)
        ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,warm)=
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace warm := by
  have closed:=congrArg (Functor.map (fun result=>((result.1,result.2.2.1),result.2.2.2)))
    (RegistrationNativePlatformRecordPartnerJointStartup.program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativePlatformLorIdealPhysical.implementation (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) codec route)
      ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,warm))
  rw [RegistrationNativePlatformLorIdealPhysical.program_source,RegistrationNativePlatformSelectiveEntropyStartup.program_source] at closed
  simp only [Functor.map_map] at closed
  convert closed using 1; rfl
/-- The original physical conflict observer on the same warm source is its exact full-prefix record-program observer. -/
theorem conflict_source (modes : Label n→KeyMode) (replace : Pqxdh.Bytes→Pqxdh.Bytes) (warm : CtxPrivate n) :
    (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      run setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary route modes replace warm=
    (fun result=>PqxdhRecordFactsBindingEvent.conflictEvent result.2) <$>
      (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec)
        (RegistrationNativeRecordOriginProgram.program codec route reference)).run warm := by
  simp only [run,project,RegistrationNativeRecordOriginProgram.program,RegistrationNativeRecordPackage.client,
    CborRecordWorldClient.client,PqxdhRecordLiftProtocol.schedule,CborRawRecordOriginFlatten.interpret,
    simulateQ_map,StateT.run_map,Functor.map_map]
omit primitive in
/-- Packaging the original complete native result adds only an extra result coordinate and preserves the exact physical cross-accept event. -/
theorem encoded_cross {Env : Type} (currentCodec : PqxdhServerAuthExperiment.Codec Reader Response)
    (currentRoute : RawCtxServerRouting.SenderDecoder) (result : RegistrationNativeEntropyRun.Result n Env Value) :
    PqxdhRecordLiftIdeal.CrossAccept currentCodec currentRoute
      (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1.1,result.1.2) result.2.base.produced) ↔
    PqxdhRecordLiftIdeal.CrossAccept currentCodec currentRoute (RegistrationNativeRecordBindingEvent.view result) := by
  rcases result with ⟨⟨_ | born,control⟩,secret⟩
  all_goals simp [RegistrationNativeRecordPackage.encode,PqxdhRecordLiftIdeal.viewOf,
    RegistrationNativeRecordBindingEvent.view,PqxdhRecordLiftIdeal.CrossAccept,Option.mem_def]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.cross_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.cross_conflict

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.joint_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.joint_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.conflict_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.conflict_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.encoded_cross' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordBindingWarm.encoded_cross
