-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual source agreement and one-use insertion share one reached private receipt and one full Native/platform state. The final projection uses the actual returned token and private agreement, preserving all other Native coordinates; every source failure remains in the unprojected source program. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture)
open AdapterPublicServerAgreementReceipt (Receipt Word)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}

omit material platform ed in
def retained (effect : RustM agreement.AgreementEffect) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK mlSource :=
  match effect with
  | .fail error => (.fail error, before)
  | .div => (.div, before)
  | .ok (.ServerComplete completed) => (.ok (AdapterPublicServerRetain.handle before.server completed),
      { before with server := AdapterPublicServerRetain.after before.server completed })
  | .ok _ => (.ok none, before)

noncomputable def projectEffect {R : Type} (effect : RustM agreement.AgreementEffect)
    (result : RustM (Word R) × RegistrationNativeExperiment.State n KemSK mlSource) :
    RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK mlSource :=
  match effect with
  | .ok (.ServerComplete completed) => AdapterPublicServerRetainNative.project completed result
  | _ => match result.1 with
    | .fail error => (.fail error, result.2)
    | .div => (.div, result.2)
    | .ok _ => (.ok none, result.2)

noncomputable def project {R : Type} (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (result : (Receipt R × RustM (Word R)) × RegistrationNativeExperiment.State n KemSK mlSource) :
    RustM (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK mlSource) := do
  let (effect, current) ← AdapterPublicAgreementNativeWorldInterpreter.restore view before (result.1.1, result.2)
  .ok (projectEffect effect (result.1.2, current))

omit material platform ed in
def afterRestore (result : RustM (RustM agreement.AgreementEffect × RegistrationNativeExperiment.State n KemSK mlSource)) :
    RustM (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK mlSource) :=
  (fun pair => retained pair.1 pair.2) <$> result

omit material platform ed in
theorem afterRestore_ok (effect : RustM agreement.AgreementEffect)
    (current : RegistrationNativeExperiment.State n KemSK mlSource) :
    afterRestore (.ok (effect, current)) = .ok (retained effect current) := rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "NativeM" => StateT (RegistrationNativeExperiment.State n KemSK mlSource) m

omit material platform ed in
noncomputable def continueNative (coins : QueryImpl unifSpec m) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (effect : RustM agreement.AgreementEffect) : NativeM (RustM (Option Nat)) :=
  match effect with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete completed) => RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.server (RegistrationServerNativeSource.retain created completed))
  | .ok _ => pure (.ok none)

omit material platform ed [LawfulMonad m] in
theorem continueNative_run (coins : QueryImpl unifSpec m) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (effect : RustM agreement.AgreementEffect) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (continueNative coins created effect).run before = pure (retained effect before) := by
  cases effect with
  | fail error | div => rfl
  | ok effect => cases effect <;> first | rfl | exact AdapterPublicServerRetainPlatform.native coins created before _

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]

structure Standard (views : AdapterPublicWrapperStorage.Views) (self : beaconcrypt_public_wrapper.server.Server) : Prop where
  insertion : ∀ completed : agreement.ServerAgreement, ∃ reply : Bool × AdapterPublicWrapperStorage.ReplaySet,
    AdapterPublicServerAcceptBody.setInsert (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) m)
      self.consumed_registrations completed.pending.registration_id.bytes = pure reply ∧
    AdapterPublicWrapperStorage.ReplayInsert views self.consumed_registrations completed.pending.registration_id.bytes reply

theorem replay_step {R : Type} (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (self : beaconcrypt_public_wrapper.server.Server)
    (before current afterRole : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self afterRole.server)
    (standard : Standard (n := n) (KemSK := KemSK) (mlSource := mlSource) (m := m) views self) (receipt : Receipt R) (effect : RustM agreement.AgreementEffect)
    (restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before (receipt, current) = .ok (effect, afterRole)) :
    (fun pair => project view before ((receipt, pair.1), pair.2)) <$>
      ((AdapterPublicServerAgreementReceipt.replay (n := n) (KemSK := KemSK) (source := mlSource) (m := m) self receipt).run current) = pure (.ok (retained effect afterRole)) := by
  cases receipt with
  | fail error =>
    change RustM.fail error = .ok (effect, afterRole) at restored
    cases restored
  | div =>
    change RustM.div = .ok (effect, afterRole) at restored
    cases restored
  | ok pair =>
    rcases pair with ⟨⟨originalEffect, journal⟩, capture⟩
    have same : originalEffect = effect := congrArg Prod.fst (RustM.ok.inj restored)
    cases same
    cases effect with
    | fail error | div =>
      simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust,
        pure_bind, StateT.run_pure, map_pure, project, restored, bind_tc_ok, projectEffect, retained]
      rfl
    | ok effect =>
      cases effect <;> try { simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind,
        RustT.run_liftRust, pure_bind, AdapterPublicServerAcceptBody.record, RustT.run_pure,
        StateT.run_pure, map_pure, project, restored, bind_tc_ok, projectEffect, retained]; rfl }
      case ServerComplete completed =>
        rcases standard with ⟨insertion⟩
        obtain ⟨reply, operation, footprint⟩ := insertion completed
        have flag := AdapterPublicServerRetain.inserted_flag views self afterRole.server completed reply related.replay footprint
        simp only [AdapterPublicServerAgreementReceipt.replay, RustT.run_bind, RustT.run_liftRust, pure_bind]
        rw [AdapterPublicServerToken.record, operation, pure_bind]
        simp only [RustT.run_pure, StateT.run_pure, map_pure, project, restored, bind_tc_ok, projectEffect]
        rw [flag]
        cases present : afterRole.server.consumed.contains (PqxdhRefinement.absBytes completed.pending.registration_id.bytes) <;>
          simp only [AdapterPublicServerToken.result, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            AdapterPublicServerRetainNative.project, retained, AdapterPublicServerRetain.handle, AdapterPublicServerRetain.after,
            AdapterPublicWrapperStorage.inserted, present, ↓reduceIte] <;> simp_all

variable [original : CryptoOperations (RustT ProbComp)]

theorem program_run (coins : QueryImpl unifSpec m) {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : Keys) (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    project view before <$> ((AdapterPublicServerAgreementReceipt.program coins generator keys self work rng).run before) =
      (do let (receipt, current) ← ((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run).run before
          (fun pair => project view before ((receipt, pair.1), pair.2)) <$>
            (AdapterPublicServerAgreementReceipt.replay self receipt).run current) := by
  unfold AdapterPublicServerAgreementReceipt.program
  rw [StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨receipt, current⟩
  simp only [bind_pure_comp, StateT.run_map, Functor.map_map]

theorem program_after_restore {PlatformState R E : Type}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    [ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (standard : Standard (n := n) (KemSK := KemSK) (mlSource := mlSource) (m := StateT PlatformState ProbComp) views self) :
    project view before <$> ((AdapterPublicServerAgreementReceipt.program coins generator keys self work rng).run before) =
      afterRestore <$> (AdapterPublicAgreementNativeWorldInterpreter.restore view before <$>
        (((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run).run before)) := by
  rw [program_run, Functor.map_map]
  apply StateT.ext
  intro previous
  simp only [StateT.run_bind, StateT.run_map]
  rw [← bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨⟨receipt, current⟩, next⟩ supported
  cases receipt with
  | fail error | div =>
    simp only [AdapterPublicServerAgreementReceipt.replay, StateT.run_pure, map_pure,
      project, AdapterPublicAgreementNativeWorldInterpreter.restore,
      AdapterPublicAgreementServerNativeWorld.restore,
      AdapterPublicAgreementServerWorld.restoreSource, AdapterPublicAgreementServerWorld.restoreRole,
      afterRestore]
    rfl
  | ok pair =>
    rcases pair with ⟨⟨effect, journal⟩, capture⟩
    let world := (RegistrationAgreementWorldTrace.restore before.server.world
      (((effect, journal), AdapterPublicAgreementServerWorld.project view capture), current.server.world.world.1)).2
    let afterRole := { before with server := { before.server with world := world } }
    have restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before
        (.ok ((effect, journal), capture), current) = .ok (effect, afterRole) := rfl
    have materialAfter := AdapterPublicAgreementNativeSourceFrame.platform_restored_material
      coins generator keys work rng view views created credential self before current afterRole related
      (.ok ((effect, journal), capture)) previous next supported effect restored
    have step := replay_step view views created credential self before current afterRole materialAfter standard
      (.ok ((effect, journal), capture)) effect restored
    have ran := congrArg (fun action => action.run next) step
    simpa only [StateT.run_map, StateT.run_pure, restored, afterRestore_ok] using ran

omit material platform ed original containers [PublicWrapperPlatform.Allocator]
  [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem after_native (coins : QueryImpl unifSpec m) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : NativeM (RustM agreement.AgreementEffect))
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    afterRestore <$> (RustM.ok <$> work.run before) =
      RustM.ok <$> ((do
        let effect ← work
        continueNative coins created effect).run before) := by
  rw [Functor.map_map, StateT.run_bind, map_bind]
  rw [← bind_pure_comp]
  apply bind_congr
  rintro ⟨effect, current⟩
  rw [continueNative_run, map_pure]
  rfl

theorem native {PlatformState R E ι : Type} {base : OracleSpec ι}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (identity : material.EdSecretKey) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (identityView : view.edSecret identity = created.seed)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    [ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (standard : Standard (n := n) (KemSK := KemSK) (mlSource := mlSource) (m := StateT PlatformState ProbComp) views self)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    project view before <$>
      ((AdapterPublicServerAgreementReceipt.program coins generator (AdapterPublicAgreementServerNative.keys identity) self
        (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) rng).run before) =
      RustM.ok <$> ((do
        let effect ← RegistrationNativePlatformExperiment.liftNative coins
          (RegistrationNativeExperiment.server
            (RegistrationServerNativeSource.agree setup checks model.representation created packet authenticated))
        continueNative coins created effect).run before) := by
  rw [program_after_restore coins generator _ self _ rng view views created credential before related standard,
    AdapterPublicAgreementNativePlatformInterpreter.native coins model entropy identity created identityView rng packet authenticated before fresh]
  exact after_native coins created _ before

end BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.continueNative_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.continueNative_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.afterRestore_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.afterRestore_ok

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.replay_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.replay_step

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.program_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.program_after_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.program_after_restore

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.after_native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAgreementRetention.native
