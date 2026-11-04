-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerReservationReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementPost
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Stateful replay-set allocation and the literal source agreement share the same Native/platform run. Capacity allocation retains either actual Rust allocation result and updated source set; its standard storage footprint preserves logical membership. The native projection observes the same success flag and external poststate before actual agreement and one-use retention. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerReservationNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt program)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
local notation "NativeM" => StateT (RegistrationNativeExperiment.State n KemSK mlSource) m
abbrev AllocationReply := core.result.Result Unit platform.ReserveError × AdapterPublicWrapperStorage.ReplaySet

noncomputable def project {R : Type} (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (result : (Receipt R × RustM (Word R)) × RegistrationNativeExperiment.State n KemSK mlSource) :
    RustM (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK mlSource) :=
  match result.1.1 with
  | some receipt => AdapterPublicServerAgreementRetention.project view before ((receipt, result.1.2), result.2)
  | none => .ok ((match result.1.2 with | .fail error => .fail error | .div => .div | .ok _ => .ok none), result.2)

noncomputable def native (coins : QueryImpl unifSpec m) {I : Type} {base : OracleSpec I}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (allocated : m AllocationReply) : NativeM (RustM (Option Nat)) := do
  let result ← StateT.lift allocated
  match result.1 with
  | .Err _ => pure (.ok none)
  | .Ok _ => do
    let effect ← RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated))
    AdapterPublicServerAgreementRetention.continueNative coins created effect

theorem program_run (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    project view before <$> ((program coins generator self control authenticated rng).run before) = (do
      let (allocated, current) ← ((AdapterPublicServerAcceptBody.setReserve (m := NativeM) self.consumed_registrations).run).run before
      match allocated with
      | .fail error => pure (.ok (.fail error, current))
      | .div => pure (.ok (.div, current))
      | .ok (allocation, history) => match allocation with
        | .Err _ => pure (.ok (.ok none, current))
        | .Ok _ => AdapterPublicServerAgreementRetention.project view before <$>
          ((AdapterPublicServerAgreementReceipt.program coins generator
            (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
            {self with consumed_registrations := history}
            (RegistrationAgreementExecutor.server control .Fresh authenticated) rng).run current)) := by
  unfold program
  rw [StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨allocated, current⟩
  cases allocated with
  | fail error | div => simp only [StateT.run_pure, map_pure, project]
  | ok pair =>
    rcases pair with ⟨allocation, history⟩
    cases allocation with
    | Err error => simp only [StateT.run_pure, map_pure, project]
    | Ok _ =>
      simp only [StateT.run_map, Functor.map_map]
      rfl


theorem coupled {PlatformState R E I : Type} {base : OracleSpec I}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    [ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (allocated : StateT PlatformState ProbComp AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT PlatformState ProbComp) views {self with consumed_registrations := history})
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    project view before <$>
      ((program coins generator self before.server.control authenticated rng).run before) =
      RustM.ok <$> (native coins setup checks model.representation created packet authenticated allocated).run before := by
  rw [program_run, operation]
  unfold native
  simp only [StateT.run_map, StateT.run_bind, StateT.run_lift, map_bind]
  apply StateT.ext
  intro previous
  simp only [StateT.run_bind, StateT.run_map, map_pure, pure_bind, bind_assoc]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨reply, between⟩ supported
  have currentMaterial := AdapterPublicWrapperState.replay_reserved view views created credential self
    before.server related reply (footprint previous reply between supported)
  rcases reply with ⟨allocation, history⟩
  cases allocation with
  | Err error => simp only [StateT.run_pure, map_pure]
  | Ok allocatedUnit =>
    have stage := AdapterPublicServerAgreementRetention.native coins generator setup checks view views model entropy
      (platform.arcView self.identity).identity_key.secret_key created related.identity.secret credential
      {self with consumed_registrations := history} rng packet authenticated before currentMaterial (insertion history) fresh
    simpa only [StateT.run_map] using congrArg (fun action => action.run between) stage


end BeaconcryptCore.Refinement.AdapterPublicServerReservationNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReservationNative.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReservationNative.program_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReservationNative.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReservationNative.coupled
