-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! Actual free Beacon creation uses pure pin selection, ordinary identity/prekey draws and indexed KEM generation. The Beacon controller generates no ML credential; every raw reply/count and failed source prefix is retained. Only the actual KEM key-generation program has an external primitive draw contract. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeMldsaCoinPrimitives (IsCoin)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let middle ← work state; next middle.1 middle.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private def Total (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (cap : Nat) : Prop := ∀ before : Local n KemSK source,
  ((lower setup checks representation created work).run before).IsTotalQueryBound cap
local notation "B" => Total (n := n) (source := source) setup checks representation created

private theorem pure_bound (value : Value) (cap : Nat) : B (pure value) cap := by
  intro before
  simp only [lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure, IsTotalQueryBound, isQueryBound_pure]

private theorem lower_bind
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next) :
    lower setup checks representation created (work >>= next) =
      (lower setup checks representation created work >>= fun value => lower setup checks representation created (next value)) := by
  funext before
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

private theorem bind_bound
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next)
    (first rest : Nat) (bounded : B work first) (continued : ∀ value, B (next value) rest) :
    B (work >>= next) (first + rest) := by
  intro before
  rw [lower_bind, StateT.run_bind]
  exact isTotalQueryBound_bind (bounded before) (fun middle => continued middle.1 middle.2)

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl
private theorem state_set_apply {S : Type} {m : Type → Type} [Monad m]
    (updated state : S) : (set updated : StateT S m Unit) state = pure ((), updated) := rfl

private theorem get_bound : B get 0 := by
  intro before
  simp only [lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure,
    IsTotalQueryBound, isQueryBound_pure]

private theorem set_bound (updated : RegistrationNativeBeaconFrontend.State source) : B (set updated) 0 := by
  intro before
  simp only [lower, StateT.run, state_set_apply, state_pure_apply, simulateQ_pure, map_pure,
    IsTotalQueryBound, isQueryBound_pure]

private theorem effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (cap : Nat)
    (bounded : ∀ before : PqxdhRecordLiftWorld.State n,
      ((PqxdhRecordLiftWorld.effects query).run before).IsTotalQueryBound cap) :
    B (RegistrationNativeBeaconFrontend.effect query) cap := by
  intro before
  simpa only [lower, RegistrationNativeBeaconFrontend.effect, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff, state_lift_apply, state_map_apply, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server] using bounded before.2.2.server.world.world.1

private theorem keygen (qKeygen : Nat)
    (bounded : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen) :
    B (RegistrationNativeBeaconFrontend.kem (.inr (.inl .create))) qKeygen := by
  intro before
  simp only [lower, RegistrationNativeBeaconFrontend.kem, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff, state_lift_apply, state_map_apply, simulateQ_map,
    simulateQ_spec_query, RegistrationNativeExperiment.trusted]
  apply isTotalQueryBound_bind (n₂ := 0)
  · apply RegistrationNativeMldsaCoinPrimitives.sampled
    simpa only [RegistrationNativeKemInterface.source, PqxdhLiveKemBirth.poolImpl,
      StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using bounded
  · intro result
    trivial

private theorem lower_sample (draw : ProbComp Value) (before : Local n KemSK source) :
    (lower setup checks representation created (RegistrationNativeBeaconFrontend.sample draw)).run before =
      (fun result => (result.1, (before.1, (before.2.1,
        RegistrationBeaconReferenceNativeEffects.embed before.2.2 result.2)))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin draw)).run
          before.2.2.server.world.world.1 := by
  rw [RegistrationNativeScalarSource.sample_effects]
  have restriction : RegistrationNativeExperiment.trusted (n := n) setup checks representation created source ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created := by
    funext selected
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, RegistrationBeaconReferenceNativeEffects.native]
  simp only [lower, StateT.run, state_lift_apply, state_map_apply, simulateQ_map, Functor.map_map,
    Prod.map, id_eq]
  rw [← QueryImpl.simulateQ_compose, restriction]
  have closed := RegistrationBeaconReferenceNativeEffects.program setup checks representation created
    (simulateQ RegistrationWorldCoinCompiler.envCoin draw) before.2.2
  simp only [StateT.run] at closed
  rw [closed]
  simp only [Functor.map_map, Prod.map, id_eq]

private theorem sample (draw : ProbComp Value) (cap : Nat) (bounded : draw.IsTotalQueryBound cap) :
    B (RegistrationNativeBeaconFrontend.sample draw) cap := by
  intro before
  simp only [lower_sample, IsTotalQueryBound, isQueryBound_map_iff]
  have native := RegistrationNativeMldsaCoinPrimitives.sampled draw cap bounded before.2.2.server.world.world.1
  have mapped : (Prod.map id RegistrationWorldCoinCompiler.eraseCoin <$>
      (PqxdhRecordLiftWorld.sampled draw).run before.2.2.server.world.world.1).IsTotalQueryBound cap := by
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using native
  rw [← RegistrationWorldCoinCompiler.coins_erase] at mapped
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using mapped

private theorem hash (request : registration.HashRequest) : B (RegistrationNativeBeaconFrontend.hash request) 64 :=
  effect setup checks representation created _ 64
    (RegistrationNativeMldsaCoinPrimitives.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))

private theorem append (keyId : U64) (edPin : Std.Array U8 32#usize) :
    B (RegistrationNativeBeaconFrontend.effect (.inr (.appendOwner keyId edPin .fresh))) 0 := by
  apply effect setup checks representation created _ 0
  intro before
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    IsTotalQueryBound, isQueryBound_pure]

attribute [local irreducible] registration.begin_server_pin

private theorem prepare (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize)
    (keyId : U64) : B (RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId) 128 := by
  unfold RegistrationNativeBeaconFrontend.prepare
  cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => exact pure_bound setup checks representation created _ _
  | ok pin =>
      apply bind_bound setup checks representation created _ _ 32 96
        (sample setup checks representation created _ 32 PqxdhJointIdentity.sampleSeed_uniform_bound)
      intro identity
      exact bind_bound setup checks representation created _ _ 32 64
        (sample setup checks representation created _ 32 PqxdhJointIdentity.sampleSeed_uniform_bound)
        (fun _ => pure_bound setup checks representation created _ _)

private theorem appendBorn (qKeygen : Nat)
    (bounded : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (pin : session.ServerAuthenticationPin)
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey : PqxdhJointGapDh.ScalarBytes) :
    B (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId pin identity prekey) qKeygen := by
  unfold RegistrationNativeBeaconFrontend.appendBorn
  apply bind_bound setup checks representation created _ _ qKeygen 0 (keygen setup checks representation created qKeygen bounded)
  intro born
  apply bind_bound setup checks representation created _ _ 0 0 (append setup checks representation created _ _)
  intro worldOwner
  apply bind_bound setup checks representation created _ _ 0 0 (get_bound setup checks representation created)
  intro owners
  exact bind_bound setup checks representation created _ _ 0 0 (set_bound setup checks representation created _)
    (fun _ => pure_bound setup checks representation created _ _)

private theorem suffix (qKeygen : Nat)
    (bounded : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    :
    B (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId) (128 + qKeygen) := by
  unfold RegistrationNativeBeaconFrontend.create
  apply bind_bound setup checks representation created _ _ 128 qKeygen (prepare setup checks representation created _ _ _)
  intro result
  cases result with
  | fail error | div => exact pure_bound setup checks representation created _ _
  | ok option => cases option with
    | none => exact pure_bound setup checks representation created _ _
    | some prepared => exact appendBorn setup checks representation created qKeygen bounded _ _ _ _ _

private theorem source_lower
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- Complete free source creation has128 ordinary pin/identity/prekey draws plus the actual indexed KEM generation cap; raw ML generation is a separate zero-coin capability. -/
theorem create (qKeygen : Nat)
    (bounded : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound qKeygen)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId).run before).IsQueryBoundP
      IsCoin (128 + qKeygen) := by
  unfold RegistrationNativeMldsaCreation.create
  apply RegistrationNativeMldsaCoinPrimitives.ordinary _ (128 + qKeygen)
  rw [source_lower]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    suffix setup checks representation created qKeygen bounded edPin mlPin keyId
      (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCreate.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinCreate.create
