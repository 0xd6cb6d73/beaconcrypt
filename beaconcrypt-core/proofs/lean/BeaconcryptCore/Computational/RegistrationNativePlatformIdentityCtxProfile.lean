-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The complete initialized runtime has the same private statistical CTX interpretation for unrestricted native-state events. Startup retains its actual warm cache and known journal, and every native/platform field is restored on all later failures and successes. This closed analysis game is distinct from an executable censored-signature forgery client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxLifecycle (native)
open RegistrationNativePlatformIdentityCtxInitial (fromInitial initial_owned initial_native)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def profile (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (pool : PqxdhDynamicIdentityPool.SourceState) : StateT Platform ProbComp Bool := fun previous => do
  let initialized ← RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure (false, previous)
  | some initial =>
    (fun result => (event (result.1.1, (result.1.2, (native result.2).1)), (native result.2).2)) <$>
      (RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
        (RegistrationNativePlatformIdentityCtxFull.run setup checks wire route representation initial.created initial.credential keys failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public))).run (fromInitial initial previous pool)

omit primitive in
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

omit primitive in
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

omit primitive in
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Every event of the complete actual native state has the same initialized runtime distribution and persistent P poststate under the physical interpreter. -/
theorem profile_source (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (pool : PqxdhDynamicIdentityPool.SourceState) (previous : Platform) :
    (profile setup checks wire route representation keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary event pool).run previous =
      (RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary event).run previous := by
  unfold profile RegistrationNativePlatformOrdinaryExperiment.profile
  simp only [StateT.run, state_bind_apply, state_lift_apply, bind_map_left]
  apply bind_congr_of_forall_mem_support
  intro initialized reached
  cases initialized with
  | none => rfl
  | some initial =>
    have empty := RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial reached
    have same := congrArg (fun distribution => (fun result => (event (result.1.1, (result.1.2, result.2.1)), result.2.2)) <$> distribution)
      (RegistrationNativePlatformIdentityCtxFull.run_source setup checks wire route representation initial.created initial.credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode (adversary initial.public)
        (fromInitial initial previous pool) (initial_owned setup.joint initial previous pool))
    rw [initial_native initial empty previous pool] at same
    simpa only [Functor.map_map, Prod.map_def, id_eq, state_map_apply, StateT.run] using same
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProfile.profile_source
