-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEffectBounds
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The genuine record-free constructor and shared pin hash prefix are composed with the exact corrected gated native stage. Record counts retain the original send/raw budget; primitive and allocator effect bills use individual native frame, constructor/ML sampler and public reserve receipts. The complete source operational comparison remains a separate exact law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds
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




open PqxdhRecordLiftBudget (RecordKind WorldRecord recordBudget)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

/-- Genuine initialization is record-free and the exact corrected gated native stage retains the original joint send/raw budget. -/
theorem program_record (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) (kind : RecordKind) :
    (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary).IsQueryBoundP (WorldRecord kind) (recordBudget budget kind) := by
  unfold RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram
  refine (isQueryBoundP_bind (m := recordBudget budget kind)
    (RegistrationNativeSelectiveRecordStartup.start_record setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) kind) ?_).mono (by omega)
  intro initialized _
  cases initialized with
  | none => trivial
  | some born =>
    exact RegistrationNativePlatformGatedNativeRecordBounds.program
      (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none))
      (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount))
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
      serverKeyId bounds mode budget (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
      (bounded _) born.created ((born.native.frontend,previous),privateBefore) kind
/-- The actual interpreted startup adds its exact coin/hash prefix to the gated native stage bill; allocator draws remain separately charged. -/
theorem program_effect (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (allowance : Fin 14 → PqxdhRecordLiftInterface.EffectKind → Nat)
    (framed : ∀ credential, RegistrationNativeEntropyFrame.Frame
      (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)) 0 allowance)
    (reserveCoins : Nat) (reserveBounded : ∀ amount before, ((reserveFrame amount).run before).IsTotalQueryBound reserveCoins)
    (constructorCoins mlCoins : Nat)
    (constructorBound : ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()).IsTotalQueryBound constructorCoins)
    (mlBound : (RegistrationNativeMldsa.generate source).IsTotalQueryBound mlCoins)
    (kind : PqxdhRecordLiftInterface.EffectKind) :
    (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId previous privateBefore bounds mode adversary).IsQueryBoundP
      (PqxdhRecordLiftBudget.WorldEffect kind)
      (RegistrationNativeSelectiveRecordStartup.startupCost constructorCoins mlCoins kind +
        RegistrationNativePlatformGatedNativeEffectBounds.effectBudget budget bounds allowance reserveCoins kind) := by
  unfold RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram
  apply isQueryBoundP_bind (RegistrationNativeSelectiveRecordStartup.start_effect setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) constructorCoins mlCoins constructorBound mlBound kind)
  intro initialized _
  cases initialized with
  | none => trivial
  | some born =>
    exact RegistrationNativePlatformGatedNativeEffectBounds.program
      (RegistrationNativePlatformSelectiveEntropyQuery.environment (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)) 0 allowance (framed born.native.credential)
      (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)) reserveCoins
      (fun amount before => by
        simpa only [RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform,StateT.run,IsTotalQueryBound,isQueryBound_map_iff]
          using reserveBounded amount before.1.2)
      setup.source.crypto (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
      serverKeyId bounds mode budget (adversary ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩)
      (bounded _) born.created ((born.native.frontend,previous),privateBefore) kind

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds.program_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds.program_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds.program_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceBounds.program_effect
