-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate
/-! Constructor primitive requests preserve the full source-owner/environment stack while their physical projection reads only the actual retained backend. Uniform requests include both source coin-effect and true uniform accounting. Hash requests use the same shared ROM/cache. The statements apply at arbitrary source stack states, so subsequent constructor stages compose without resetting RNG, private pool or platform state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {I KemSK P A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT P ProbComp)
abbrev Full (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  (RegistrationNativeBeaconFrontend.State source × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
    RegistrationNativeExperiment.State n KemSK source

def project (before : Full n KemSK source) : Backend n KemSK :=
  backend (RegistrationNativeFinishTerminalTree.assemble before.1.1 before.1.2 before.2)

private theorem mk_apply {S V : Type} {m : Type → Type} (work : S → m (V × S)) (before : S) :
    (StateT.mk work) before = work before := rfl

private theorem lift_apply {S V : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m V) (before : S) :
    (StateT.lift work : StateT S m V) before = (fun value => (value,before)) <$> work := by
  change (StateT.lift work : StateT S m V).run before = _
  rw [StateT.run_lift,bind_pure_comp]

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

noncomputable def uniform : QueryImpl unifSpec SourceM :=fun query =>
  AdapterBeaconConstructorNative.lift coins setup checks representation created
    (RegistrationNativeBeaconFrontend.effect (.inl query))

theorem sample (work : ProbComp A) :
    simulateQ (uniform (n:=n) (source:=source) coins setup checks representation created) work =
      AdapterBeaconConstructorNative.lift coins setup checks representation created
        (RegistrationNativeBeaconFrontend.sample work) := by
  unfold uniform RegistrationNativeBeaconFrontend.sample AdapterBeaconConstructorNative.lift
  exact (RegistrationNativePlatformGenericBundle.liftLegacy_simulate _ _ work).symm

noncomputable def flatUniform : QueryImpl unifSpec (StateT (Full n KemSK source) (StateT P ProbComp)) :=
  (uniform coins setup checks representation created).flattenStateT.flattenStateT

theorem uniform_source (query : unifSpec.Domain) (before : Full n KemSK source) :
    Prod.map id project <$> (flatUniform coins setup checks representation created query).run before =
      (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created query).run (project before) := by
  have patched := RegistrationNativeLocalStatePatch.trusted_patch setup checks representation created
    (.inl (.inl query)) (by trivial) before.1.1 before.1.2 before.2
  have law := RegistrationNativePlatformSdkReification.coin_backend setup checks representation created query
    (RegistrationNativeFinishTerminalTree.assemble before.1.1 before.1.2 before.2)
  dsimp only [RegistrationNativePlatformSdkReification.leaf] at law
  rw [patched] at law
  have interpreted := congrArg (simulateQ coins) law
  simp only [simulateQ_map,Functor.map_map] at interpreted
  dsimp only [flatUniform,uniform,QueryImpl.flattenStateT,AdapterBeaconConstructorNative.lift,
    RegistrationNativePlatformGenericBundle.liftLegacy,RegistrationNativeBeaconFrontend.effect,
    AdapterBeaconConstructorKemLift.implementation,RegistrationNativePlatformInterpret.state,StateT.run]
  simp only [mk_apply,lift_apply,map_apply,simulateQ_map,simulateQ_spec_query,Functor.map_map,
    AdapterBeaconConstructorKemLift.implementation,RegistrationNativePlatformInterpret.state]
  exact interpreted

theorem program_source (work : ProbComp A) (before : Full n KemSK source) :
    Prod.map id project <$> (simulateQ (flatUniform coins setup checks representation created) work).run before =
      (simulateQ (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) work).run (project before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  exact uniform_source coins setup checks representation created

noncomputable def hash (request : registration.HashRequest) : SourceM CtxRomAuth.CtxDigest :=
  AdapterBeaconConstructorNative.lift coins setup checks representation created (RegistrationNativeBeaconFrontend.hash request)

noncomputable def flatHash (request : registration.HashRequest) :
    StateT (Full n KemSK source) (StateT P ProbComp) CtxRomAuth.CtxDigest :=
  fun before => (fun result => (result.1.1.1,((result.1.1.2,result.1.2),result.2))) <$>
    (((hash coins setup checks representation created request).run before.1.1).run before.1.2).run before.2

theorem hash_source (request : registration.HashRequest) (before : Full n KemSK source) :
    Prod.map id project <$> (flatHash coins setup checks representation created request).run before =
      (fun state => simulateQ coins ((RegistrationNativePlatformSdkReification.backendLeaf setup checks representation created
        (.inr (.inl (RegistrationInputs.hashBytes request)))).run state)) (project before) := by
  have patched := RegistrationNativeLocalStatePatch.trusted_patch setup checks representation created
    (.inl (.inr (.hash (RegistrationInputs.hashBytes request)))) (by trivial) before.1.1 before.1.2 before.2
  have law := RegistrationNativePlatformSdkReification.hash_backend setup checks representation created (RegistrationInputs.hashBytes request)
    (RegistrationNativeFinishTerminalTree.assemble before.1.1 before.1.2 before.2)
  dsimp only [RegistrationNativePlatformSdkReification.leaf] at law
  rw [patched] at law
  have interpreted := congrArg (simulateQ coins) law
  simp only [simulateQ_map,Functor.map_map] at interpreted
  dsimp only [flatHash,hash,QueryImpl.flattenStateT,AdapterBeaconConstructorNative.lift,
    RegistrationNativePlatformGenericBundle.liftLegacy,RegistrationNativeBeaconFrontend.hash,
    RegistrationNativeBeaconFrontend.effect,AdapterBeaconConstructorKemLift.implementation,
    RegistrationNativePlatformInterpret.state,StateT.run]
  simp only [lift_apply,map_apply,simulateQ_map,simulateQ_spec_query,Functor.map_map,AdapterBeaconConstructorKemLift.implementation,RegistrationNativePlatformInterpret.state]
  exact interpreted

theorem flatten_source {J : Type} {spec : OracleSpec J}
    (implementation : QueryImpl spec SourceM) (work : OracleComp spec A) (before : Full n KemSK source) :
    (simulateQ implementation.flattenStateT.flattenStateT work).run before =
      (fun result => (result.1.1.1,((result.1.1.2,result.1.2),result.2))) <$>
        ((((simulateQ implementation work).run before.1.1).run before.1.2).run before.2) := by
  rcases before with ⟨⟨owners,environment⟩,current⟩
  rw [OracleComp.simulateQ_flattenStateT_run,OracleComp.simulateQ_flattenStateT_run]
  simp only [bind_pure_comp,StateT.run_map,Functor.map_map]


end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.hash_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.flatten_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives.flatten_source
