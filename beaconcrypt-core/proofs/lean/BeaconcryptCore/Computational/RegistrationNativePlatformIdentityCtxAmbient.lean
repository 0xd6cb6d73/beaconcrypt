-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxEffects

/-! Actual Beacon ambient callbacks expose shared CTX queries through the private backend. KEM-only work retains its literal sampler and cannot inspect cache addresses. Full Context, KEM pool and costs are retained without a supplied source/security equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient
open RegistrationNativeIdentityWorld (Context)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformCtxBackend (Spec Cache)
variable {I KemSK Value : Type} {base : OracleSpec I} {n : Nat} {source : RegistrationNativeMldsa.Source}

def replace (cache : Cache) (before : Context n KemSK) : Context n KemSK :=
  {before with server := {before.server with world := {before.server.world with
    world := (RegistrationNativePlatformCtxCacheFrame.replace cache before.server.world.world.1, before.server.world.world.2)}}}

def world {m : Type → Type} [Functor m] (work : StateT (PqxdhRecordLiftWorld.State n) m Value) :
    StateT (Context n KemSK) m Value := fun before =>
  (fun result => (result.1, {before with server := {before.server with world := {before.server.world with
    world := (result.2, before.server.world.world.2)}}})) <$> work.run before.server.world.world.1

noncomputable def program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Context n KemSK) (OracleComp Spec))
  | .inl query => world (RegistrationNativePlatformCtxEffects.program query)
  | .inr query => fun before => simulateQ RegistrationNativePlatformCtxBackend.coin
      ((RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run before)

abbrev Full (n : Nat) (KemSK : Type) := Context n KemSK × RegistrationNativePlatformCtxBackend.State

def realize (before : Full n KemSK) : Context n KemSK := replace before.2.1 before.1

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (RegistrationNativeIdentityFrontend.Ambient n KemSK) (StateT (Full n KemSK) ProbComp) :=
  fun query before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation
      ((program (source := source) setup checks representation created query).run before.1)).run before.2

/-- KEM calls retain their actual costs/private history and are independent of CTX cache addresses. -/
theorem kem_frame (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (cache : Cache) (before : Context n KemSK) :
    Prod.map id (replace cache) <$>
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run before =
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run (replace cache before) := by
  simp only [RegistrationNativeIdentityWorld.ambient, RegistrationNativeExperiment.trusted,
    RegistrationNativeIdentityWorld.embed, PqxdhRecordLiftWorld.sampled,
    StateT.run, bind_pure_comp, Functor.map_map, replace, RegistrationNativePlatformCtxCacheFrame.replace]
  rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem effects_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Full n KemSK) :
    Prod.map id realize <$> (implementation (source := source) setup checks representation created (.inl query)).run before =
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inl query)).run (realize before) := by
  have same := congrArg (fun distribution => (fun result => (result.1, {before.1 with server := {before.1.server with
    world := {before.1.server.world with world := (result.2, before.1.server.world.world.2)}}})) <$> distribution)
    (RegistrationNativePlatformCtxEffects.query query (before.1.server.world.world.1, before.2))
  simp only [implementation, program, world, StateT.run, simulateQ_map, map_apply, Functor.map_map,
    Prod.map, id_eq, realize, replace, RegistrationNativePlatformCtxEffects.implementation,
    RegistrationNativePlatformCtxEffects.realize, RegistrationNativePlatformCtxCacheFrame.replace,
    RegistrationNativeIdentityWorld.ambient, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, RegistrationNativeIdentityWorld.embed, RegistrationNativeIdentityWorld.project] at same ⊢
  exact same

private theorem kem_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) (before : Full n KemSK) :
    Prod.map id realize <$> (implementation (source := source) setup checks representation created (.inr query)).run before =
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run (realize before) := by
  change Prod.map id realize <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation
      (simulateQ RegistrationNativePlatformCtxBackend.coin
        ((RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created (.inr query)).run before.1))).run before.2) = _
  rw [RegistrationNativePlatformCtxBackend.coins]
  simpa only [StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, realize] using
    kem_frame (source := source) setup checks representation created query before.2.1 before.1

/-- Every literal actual trusted ambient callback restores full Context/private-pool state and exact counters from one shared physical hash interpreter. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeIdentityFrontend.Ambient n KemSK).Domain) (before : Full n KemSK) :
    Prod.map id realize <$> (implementation (source := source) setup checks representation created query).run before =
      (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created query).run (realize before) := by
  cases query with
  | inl query => exact effects_source setup checks representation created query before
  | inr query => exact kem_source setup checks representation created query before

/-- All adaptive ambient work exposes CTX requests without source event or whole-handler assumptions. -/
theorem complete (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeIdentityFrontend.Ambient n KemSK) Value) (before : Full n KemSK) :
    Prod.map id realize <$> (simulateQ (implementation (source := source) setup checks representation created) work).run before =
      (simulateQ (RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created) work).run (realize before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ realize (query_source setup checks representation created) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient.kem_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient.kem_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbient.complete
