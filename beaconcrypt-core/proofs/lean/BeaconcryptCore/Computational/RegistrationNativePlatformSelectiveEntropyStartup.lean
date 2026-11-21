-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyInitialized
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The genuine effectful constructor, generated credential, shared pin hash and complete corrected dynamic source run have the gated native environment interpretation. Physical allocation is derived from the actual interpreted startup, and all original value, ledger, private/provider, cursor, Protocol, service and persistent platform poststates are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
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

noncomputable def stage (born : RegistrationNativeHiddenStartup.Started source) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Platform source) : OracleComp (WorldSpec n) (Outcome (State n KemSK ProviderState Platform source) Value) :=
  (fun result => some (PqxdhRegistrationJointServerBirth.encode born.created,result)) <$>
    (RegistrationNativePlatformSelectiveEntropyExecution.run setup checks wire source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)

noncomputable def referenceStage (born : RegistrationNativeHiddenStartup.Started source) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK ProviderState Platform source) : OracleComp (WorldSpec n) (Outcome (State n KemSK ProviderState Platform source) Value) :=
  RegistrationNativePlatformGatedNativeEntropy.program
    (RegistrationNativePlatformSelectiveEntropyQuery.environment setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
    (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount))
    setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
    serverKeyId bounds mode work born.created before

noncomputable def program (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    OracleComp (WorldSpec n) (Outcome (State n KemSK ProviderState Platform source) Value) := do
  let born ← RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  match born with
  | none => pure none
  | some born =>
      stage setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer born serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) ((born.native.frontend,previous),privateBefore)

noncomputable def referenceProgram (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    OracleComp (WorldSpec n) (Outcome (State n KemSK ProviderState Platform source) Value) := do
  let born ← RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
  match born with
  | none => pure none
  | some born =>
      referenceStage setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer born serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) ((born.native.frontend,previous),privateBefore)

omit primitive in
private def finish (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (result : (Value × RegistrationNativeLedger.State) × RegistrationNativeHiddenEnvironmentWorld.State n
      (State n KemSK ProviderState Platform source) Secret) :=
  (((some (PqxdhRegistrationJointServerBirth.encode created,result.1,result.2.1.1.1),result.2.1.1.2),result.2.1.2),result.2.2)

omit primitive in
private theorem package_lower
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (State n KemSK ProviderState Platform source) (OracleComp (WorldSpec n)) (Value × RegistrationNativeLedger.State))
    (before : State n KemSK ProviderState Platform source) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    CborRawRecordOriginFlatten.interpret service codec route
      ((fun result => some (PqxdhRegistrationJointServerBirth.encode created,result)) <$> work.run before) shell control secret =
      finish source created <$> (lower service codec route work).run (((before,shell),control),secret) := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run,RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  simp only [finish,Functor.map_map]

/-- The complete genuine startup and corrected dynamic source execution have the same gated native environment interpretation, retaining the actual cursor, control, private state and persistent P. -/
theorem program_source (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (secret : Secret) :
    CborRawRecordOriginFlatten.interpret service codec route
      (program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret =
      CborRawRecordOriginFlatten.interpret service codec route
        (referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret := by
  unfold program referenceProgram
  rw [CborRawRecordOriginFlatten.interpret_bind,CborRawRecordOriginFlatten.interpret_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨⟨_ | born,shell⟩,control⟩,after⟩ reached
  · rfl
  · have actual := RegistrationNativePlatformSelectiveEntropyInitialized.initialized_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId previous privateBefore service codec route secret born shell control after reached
      (pure none) bounds mode (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
    have mapped := congrArg (Functor.map (finish source born.created)) actual
    simpa only [stage,referenceStage,RegistrationNativePlatformSelectiveEntropyExecution.run,
      RegistrationNativePlatformGatedNativeEntropy.program,RegistrationNativePlatformSelectiveEntropyQuery.reference,
      package_lower] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup.program_source
