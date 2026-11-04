-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
/-! The corrected Beacon material factor is interpreted through the literal runtime's native interpreter and the same common outer monad. Equality preserves the complete native state, actual private KEM pool, owner history, shared World and external platform state. There is no equality with the earlier identifier profile and no restoration of a prior state after failed callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconChargedRuntime
open RegistrationNativeBeaconFrontend (M Owner)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m]

noncomputable def interpret (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) :
    StateT (RegistrationNativeExperiment.State n KemSK source) m Value :=
  RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created work)

theorem post_root (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (erased : commitment.CommitmentTranscript)
    (index : Nat) (owner : Owner source) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) :
    interpret coins setup checks representation created
      (RegistrationBeaconChargedNative.postRoot (n := n) setup wire index owner (RegistrationBeaconBoundSource.atRoot descriptor root)) =
    interpret coins setup checks representation created (do
      let _ ← RegistrationBeaconChargedNative.charge .initialKdf
      let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
        (PqxdhRefinement.absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
        then RegistrationBeaconChargedNative.charge .ratchetKdf else pure ()
      let result ← RegistrationNativePlatformPairedBeaconOwner.knownStage setup.source
        (RegistrationBeaconChargedSource.primitive (RegistrationBeaconChargedNative.read setup wire))
        RegistrationNativeBeaconFrontend.effect owner.worldOwner (RegistrationBeaconPublicDescriptor.clear descriptor)
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root)
      RegistrationNativePlatformBeaconSettle.settle index owner result) := by
  rw [RegistrationBeaconPublicDescriptor.post_root setup wire erased.bytes index owner descriptor root]

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconChargedRuntime.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconChargedRuntime.post_root

end BeaconcryptCore.Computational.RegistrationBeaconChargedRuntime
