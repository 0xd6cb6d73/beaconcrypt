-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend
import BeaconcryptCore.Computational.RegistrationWorldCoinCompiler

/-! The indexed identity source shares the existing native World and KEM pool. Its public auxiliary context contains no Beacon identity seeds; those appear only in the private identity pool. Actual key-generation coins execute through the original Env coin handler at the create call position, retaining both uniform and coin-effect counts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityWorld
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend (Ambient Trusted)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

structure Context (n : Nat) (KemSK : Type) where
  server : RegistrationServerFrontendCompiler.State n
  kem : PqxdhLiveKemBirth.Pool KemSK
  parsedAccepts : Nat

def project (native : RegistrationNativeExperiment.State n KemSK mlSource) : Context n KemSK :=
  ⟨native.server, native.pool, native.parsedAccepts⟩

def embed (before : Context n KemSK) : RegistrationNativeExperiment.State n KemSK mlSource :=
  ⟨before.server, [], before.kem, before.parsedAccepts⟩

noncomputable def ambient (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (Ambient n KemSK) (StateT (Context n KemSK) ProbComp) := fun query before =>
  Prod.map id project <$>
    (RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run (embed before)

/-- Removing the source's private Beacon roster has no effect on an actual native ambient primitive operation. -/
theorem ambient_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : (Ambient n KemSK).Domain)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id project <$>
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run before =
      (ambient (mlSource := mlSource) setup checks representation created query).run (project before) := by
  cases query <;>
    simp only [ambient, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
      RegistrationNativeExperiment.server, StateT.run, project, embed, Functor.map_map, Prod.map_def, id_eq]
  all_goals simp only [map_bind, map_pure]

structure State (n : Nat) (KemSK : Type) where
  context : Context n KemSK
  identities : PqxdhDynamicIdentityPool.SourceState

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (Trusted n KemSK) (StateT (State n KemSK) ProbComp)
  | .inl query => fun before =>
      (fun result => (result.1, { before with context := result.2 })) <$>
        (ambient (mlSource := mlSource) setup checks representation created query).run before.context
  | .inr query => fun before => do
      let result ← (simulateQ RegistrationWorldCoinCompiler.coin
        ((PqxdhDynamicIdentityPool.lazyImpl setup.joint (.inr query)).run before.identities)).run
          before.context.server.world.world.1
      pure (result.1.1, { before with
        identities := result.1.2
        context := { before.context with server := { before.context.server with
          world := { before.context.server.world with world := (result.2, before.context.server.world.world.2) } } } })

/-- An actual indexed native identity creation publishes precisely the seed sampled privately at that call and appends it at its generated index. -/
theorem create_generated (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n KemSK)
    (result : Option (Nat × PqxdhJointIdentity.PublicIdentity) × State n KemSK)
    (reached : result ∈ support ((implementation (mlSource := mlSource) setup checks representation created
      (.inr .create)).run before)) :
    ∃ seed ∈ support PqxdhJointIdentity.sampleSeed,
      result.1 = some (before.identities.seeds.length, setup.joint.publicKeys seed) ∧
      result.2.identities.seeds = before.identities.seeds ++ [seed] := by
  simp only [implementation, StateT.run, bind_pure_comp,
    support_map] at reached
  obtain ⟨inner, sampled, rfl⟩ := reached
  have actual : inner.1 ∈ support ((PqxdhDynamicIdentityPool.lazyImpl setup.joint (.inr .create)).run before.identities) := by
    apply OracleComp.support_simulateQ_run'_subset RegistrationWorldCoinCompiler.coin _
      before.context.server.world.world.1
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst sampled
  rw [PqxdhDynamicIdentityPool.lazyImpl_create] at actual
  obtain ⟨seed, drawn, equal⟩ := OracleComp.mem_support_map_peel _ _ actual
  refine ⟨seed, drawn, ?_, ?_⟩
  · change inner.1.1 = some (before.identities.seeds.length, setup.joint.publicKeys seed)
    exact congrArg Prod.fst equal
  · change inner.1.2.seeds = before.identities.seeds ++ [seed]
    exact congrArg (fun value => value.2.seeds) equal

/-- Native signing and static-DH services use their stored seed, retain the exact attempted query/reply and leave every unrelated World/context field unchanged. -/
theorem service_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (handle : Nat)
    (request : PqxdhJointIdentity.JointSpec.Domain) (before : State n KemSK) :
    (implementation (mlSource := mlSource) setup checks representation created (.inr (.service handle request))).run before =
      (let reply := (before.identities.seeds[handle]?).map (fun seed => PqxdhJointIdentity.primitiveReply setup.joint seed request)
       pure (reply, { before with identities :=
         PqxdhDynamicIdentityPool.record (.inr (.service handle request)) reply before.identities })) := by
  simp only [implementation, PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
    StateT.run, simulateQ_pure,
    StateT.monad_pure_def, StateT.pure, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeIdentityWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityWorld.ambient_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityWorld.ambient_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityWorld.create_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityWorld.create_generated
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityWorld.service_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityWorld.service_source
