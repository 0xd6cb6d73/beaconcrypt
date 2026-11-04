-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart

/-! The complete native profile is exactly the actual interpretation of opaque ML key handles. The adversary sees the unchanged original public initialization, while private analysis restores the actual final native state through reached source key rows. This theorem uses actual source draw receipts and does not equate the external EUF signer's different accounting receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableProfile
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (handleSource restore)
open RegistrationNativeMldsaTableProgram (evaluate)
open RegistrationNativeMldsaTableRun (observeRun)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeInterface (ModeSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) : ProbComp Bool := do
  let initialized ← evaluate source
    (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}
  match initialized.1 with
  | none => pure false
  | some initial =>
      match initialized.2.keys[initial.credential.secret]? with
      | none => pure false
      | some key => event <$> (observeRun source key <$>
          evaluate source (RegistrationNativeMldsaProfile.run setup checks wire route representation initial.created
            initial.credential bounds mode (adversary initial.public) initial.state) initialized.2)

/-- Whole opaque-key execution equals the complete original native profile, from actual startup through arbitrary adaptive callbacks and its literal final event. -/
theorem source_profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    profile source setup checks wire route representation ensureInit identityIndex serverKeyId bounds mode adversary event =
      RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode adversary event := by
  unfold profile RegistrationNativeExperiment.profile
  rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKeyId]
  rw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized supported
  cases current : initialized.1 with
  | none => simp only [current, RegistrationNativeMldsaTableStart.restored, Option.bind_none]
  | some initial =>
      have member : initial ∈ initialized.1 := by rw [current]; rfl
      obtain ⟨key, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex
        serverKeyId initialized supported initial member
      simp only [current, server.1, RegistrationNativeMldsaTableStart.restored, Option.bind_some,
        Option.map_some, RegistrationNativeMldsaMap.initial_public]
      have actual := RegistrationNativeMldsaTableRun.run source setup checks wire route representation initial.created
        initial.credential key bounds mode (adversary initial.public) initial.state initialized.2 server owners
      rw [actual]
      rw [RegistrationNativeMldsaMap.initial,
        RegistrationNativeMldsaOpaque.restore_live source key initialized.2 initial.credential key server]
end BeaconcryptCore.Computational.RegistrationNativeMldsaTableProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableProfile.source_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableProfile.source_profile
