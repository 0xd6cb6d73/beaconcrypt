-- SPDX-License-Identifier: 0BSD
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup
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


variable (physical : QueryImpl (WorldSpec n) (StateT Secret ProbComp))

noncomputable def joint (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (physicalBefore : Secret) :
    ProbComp (Outcome (State n KemSK ProviderState Platform source) Value ×
      (RegistrationNativePlatformPublicRecordSlots.State n × RegistrationNativeG2Trace.State × Secret)) := do
  let start ← (simulateQ physical (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed))).run physicalBefore
  match start.1 with
  | none => pure (none,(RegistrationNativePlatformPublicRecordSlots.initial (n := n),RegistrationNativeG2Trace.initial,start.2))
  | some born =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode born.created,result.1.1,(result.1.2,result.2.2.2.1)),
      (result.2.1,result.2.2.1,result.2.2.2.2))) <$>
      StateT.run (simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate provider physical)
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source born.native.credential)
            selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
            serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) (born.native.frontend,previous))))
        (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,start.2))

/-- The complete actual startup and source execution has the exact joint slot/descriptor lift. Erasure keeps the original outcome, full private source/platform state and reached physical state. -/
theorem program_source (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (physicalBefore : Secret) :
    (fun result => (result.1,result.2.2.2)) <$>
      joint setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        physical ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary physicalBefore =
    (simulateQ physical (RegistrationNativePlatformSelectiveEntropyStartup.program setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)).run physicalBefore := by
  simp only [joint,RegistrationNativePlatformSelectiveEntropyStartup.program,simulateQ_bind,StateT.run_bind,map_bind]
  apply bind_congr
  rintro ⟨_ | born,after⟩
  · rfl
  · simp only [RegistrationNativePlatformSelectiveEntropyStartup.stage,simulateQ_map,StateT.run_map,Functor.map_map]
    have step := congrArg (Functor.map (fun result => (some (PqxdhRegistrationJointServerBirth.encode born.created,result.1),result.2)))
      (RegistrationNativePlatformRecordPartnerJointErasure.run setup wire seed scalar candidate provider physical checks source born.native.credential
        selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩) (born.native.frontend,previous) privateBefore after
        RegistrationNativePlatformPublicRecordSlots.initial RegistrationNativeG2Trace.initial)
    simpa only [Functor.map_map] using step

/-- A reached physical CTX state is retained while the same joint source lift is compared with the literal reference body; sampler charges and warmed private caches are not reset. -/
theorem ctx_warm_source (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (secret : PqxdhRecordLiftIdeal.CtxPrivate n) :
    (fun result => RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced) <$>
      joint setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (RegistrationNativePlatformLorIdealPhysical.implementation
          (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route)
        ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,secret) =
    (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.base.produced) <$>
      CborRawRecordOriginFlatten.interpret
        (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
        (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary)
        CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl secret := by
  have full := congrArg (Functor.map (fun result => RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.1) result.2.2.2.base.produced))
    (program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativePlatformLorIdealPhysical.implementation
        (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route)
      ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,secret))
  rw [RegistrationNativePlatformLorIdealPhysical.program_source] at full
  have transport := congrArg (Functor.map (fun result => RegistrationNativeRecordPackage.nativeView (result.1.1.1,result.1.2) result.2.base.produced))
    (RegistrationNativePlatformSelectiveEntropyStartup.program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route secret)
  simp only [Functor.map_map] at full
  exact full.trans transport

/-- The original all-random record view is the projection of this same complete startup/slot/descriptor lift; no private snapshot is made an ordinary oracle observation. -/
theorem ctx_source (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    (fun result => RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced) <$>
      joint setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (RegistrationNativePlatformLorIdealPhysical.implementation (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))) (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route)
        ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
        (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial) =
    RegistrationNativeRecordPackage.ctx modes setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route
      (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary) := by
  have full := congrArg (Functor.map (fun result => RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.1) result.2.2.2.base.produced))
    (program_source setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativePlatformLorIdealPhysical.implementation
        (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)))
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) route)
      ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary
      (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial))
  rw [RegistrationNativePlatformLorIdealPhysical.program_source] at full
  rw [←RegistrationNativePlatformSelectiveReferenceCrypto.ctx_transport setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary modes route]
  rw [RegistrationNativeRecordPackage.ctx_source]
  simpa only [Functor.map_map] using full

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup.ctx_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup.ctx_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup.ctx_warm_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup.ctx_warm_source
