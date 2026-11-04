-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconChargedNative
/-! The actual post-root receive does not inspect the candidate's temporary root-input field. Clearing that field preserves the complete executable program, including all stateful callbacks. The executable descriptor therefore contains fixed cleared bytes, while the root and consumed seed chains stay private. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor

def clear (descriptor : RegistrationBeaconBoundSource.PublicAgreement) : RegistrationBeaconBoundSource.PublicAgreement :=
  {descriptor with candidate := PqxdhBeaconPhase2Publication.clearedCandidate descriptor.candidate}

theorem fields (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    (clear descriptor).candidate.server_binding = descriptor.candidate.server_binding ∧
    (clear descriptor).candidate.assigned_key_id = descriptor.candidate.assigned_key_id ∧
    (clear descriptor).candidate.associated_data = descriptor.candidate.associated_data ∧
    (clear descriptor).candidate.root_key_input =
      (PqxdhBeaconPhase2Shared.clearedMetadata (PqxdhBeaconPhase2Shared.candidateMetadata descriptor.candidate)).root_key_input ∧
    (clear descriptor).binding = descriptor.binding ∧ (clear descriptor).application = descriptor.application := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    RegistrationBeaconSeed.program source (clear descriptor) output = RegistrationBeaconSeed.program source descriptor output := by
  rfl

theorem known {n : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    RegistrationNativePlatformPairedBeaconOwner.knownStage source raw effects owner (clear descriptor) output =
      RegistrationNativePlatformPairedBeaconOwner.knownStage source raw effects owner descriptor output := by
  unfold RegistrationNativePlatformPairedBeaconOwner.knownStage
  rw [program]

theorem post_root {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
    {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationBeaconChargedNative.postRoot (n := n) (Auxiliary := Auxiliary) setup wire index owner
      (RegistrationBeaconBoundSource.atRoot descriptor root) = (do
        let _ ← RegistrationBeaconChargedNative.charge .initialKdf
        let _ ← if RawCtxReceive.ValidFrame descriptor.candidate.server_binding.identity_key_id
          (PqxdhRefinement.absBytes descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame descriptor)
          then RegistrationBeaconChargedNative.charge .ratchetKdf else pure ()
        let result ← RegistrationNativePlatformPairedBeaconOwner.knownStage setup.source
          (RegistrationBeaconChargedSource.primitive (RegistrationBeaconChargedNative.read setup wire))
          RegistrationNativeBeaconFrontend.effect owner.worldOwner (clear descriptor)
            (PqxdhServerAuthKeySchedule.fromRoot setup.source root)
        RegistrationNativePlatformBeaconSettle.settle index owner result) := by
  rw [RegistrationBeaconChargedNative.post_root setup wire erased index owner descriptor root]
  simp only [known]

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.fields

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.known

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.post_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor.post_root

end BeaconcryptCore.Computational.RegistrationBeaconPublicDescriptor
