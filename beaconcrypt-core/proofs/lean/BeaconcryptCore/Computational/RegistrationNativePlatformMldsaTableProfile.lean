-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRun
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart

/-! Actual private-table startup and adaptive corrected platform execution restore the complete literal initialized profile. Public initialization is unchanged; the actual source key rows restore only private credentials while true source draw receipts and the external platform poststate remain intact. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaTableProgram (evaluate)
open RegistrationNativePlatformMldsaTableRestore (observe)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)

noncomputable def profile : StateT Platform ProbComp Bool := fun previous => do
  let initialized ← evaluate source
    (RegistrationNativeMldsaCreation.start (n := n) setup ensureInit identityIndex serverKeyId) {}
  match initialized.1 with
  | none => pure (false, previous)
  | some initial =>
    match initialized.2.keys[initial.credential.secret]? with
    | none => pure (false, previous)
    | some key =>
      (fun result => (event (result.1.1.1, (result.1.1.2, result.1.2)), result.2)) <$>
        (observe source key <$>
          evaluate source ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation initial.created
            initial.credential view failure allocation reserveRegistration reservePeer erased helper writer bounds mode
              (adversary initial.public) initial.state).run previous) initialized.2)

omit primitive in
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit primitive in
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := bind_pure_comp _ _

/-- The complete actual table profile equals literal corrected source initialization, adaptive execution and final event, including its common platform state. -/
theorem source_profile :
    profile source setup checks wire route representation ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer erased
      helper writer bounds mode adversary event =
      RegistrationNativePlatformExperiment.profile RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation source ensureInit identityIndex serverKeyId
        view failure allocation reserveRegistration reservePeer erased helper writer bounds mode adversary event := by
  funext previous
  unfold profile RegistrationNativePlatformExperiment.profile
  simp only [RegistrationNativePlatformMldsaProgram.lift_coins, bind_apply, lift_apply, bind_map_left]
  rw [← RegistrationNativeMldsaTableStart.start source setup ensureInit identityIndex serverKeyId, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized supported
  cases current : initialized.1 with
  | none => simp only [current, RegistrationNativeMldsaTableStart.restored, Option.bind_none]; rfl
  | some initial =>
    have member : initial ∈ initialized.1 := by rw [current]; rfl
    obtain ⟨key, server⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex serverKeyId initialized supported initial member
    simp only [current, server.1, RegistrationNativeMldsaTableStart.restored, Option.bind_some,
      Option.map_some, RegistrationNativeMldsaMap.initial_public]
    have actual := RegistrationNativePlatformMldsaTableRun.run source setup checks wire route representation initial.created initial.credential key
      view failure allocation reserveRegistration reservePeer erased helper writer bounds mode (adversary initial.public) initial.state previous initialized.2 server
    rw [actual]
    rw [RegistrationNativeMldsaMap.initial,
      RegistrationNativeMldsaOpaque.restore_live source key initialized.2 initial.credential key server]
    simp only [StateT.run, map_apply]
    rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProfile.source_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProfile.source_profile
