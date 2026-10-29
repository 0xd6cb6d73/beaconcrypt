-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorld
import BeaconcryptCore.Computational.RegistrationNativeEnvSampling

/-! The generated-identity client executes ordinary native effects in its public auxiliary World and forwards identity creation, signing and static DH to the existing indexed joint service. Actual identity key-generation contributes exactly 32 original World coins. Private identity seeds never occur in the executable compiler state. Uniform-query observations in the joint game's analysis transcript are removed only by the explicit source projection. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDynamicIdentityPool
open RegistrationNativeIdentityWorld (Context)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def coins : QueryImpl unifSpec (OracleComp DynamicSpec) := fun query => DynamicSpec.query (.inl query)

def advance (before : Context n KemSK) : Context n KemSK :=
  { before with server := { before.server with world := { before.server.world with
      world := (RegistrationNativeEnvSampling.advance 32 before.server.world.world.1, before.server.world.world.2) } } }

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (RegistrationNativeIdentityFrontend.Trusted n KemSK)
      (StateT (Context n KemSK) (OracleComp DynamicSpec))
  | .inl query => fun before => simulateQ coins
      ((RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created query).run before)
  | .inr .create => fun before => do
      let answer ← DynamicSpec.query (.inr .create)
      pure (answer, advance before)
  | .inr (.service handle request) => StateT.lift (DynamicSpec.query (.inr (.service handle request)))
  | .inr (.reveal handle) => StateT.lift (DynamicSpec.query (.inr (.reveal handle)))

def keep : Observation → Bool
  | ⟨.inl _, _⟩ => false
  | ⟨.inr _, _⟩ => true

def poolView (before : SourceState) : SourceState :=
  { before with transcript := before.transcript.filter keep }

def project (before : Context n KemSK × SourceState) : RegistrationNativeIdentityWorld.State n KemSK :=
  ⟨before.1, poolView before.2⟩

noncomputable def compiled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (RegistrationNativeIdentityFrontend.Trusted n KemSK)
      (StateT (Context n KemSK × SourceState) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl setup.joint)
      ((implementation (source := source) setup checks representation created query).run before.1)).run before.2

private theorem pool_coin (query : unifSpec.Domain) (answer : unifSpec.Range query) (before : SourceState) :
    poolView (record (.inl query) answer before) = poolView before := by
  simp only [poolView, record, List.filter_append, List.filter_cons, keep, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.append_nil]

private theorem pool_service (query : PoolSpec.Domain) (answer : PoolSpec.Range query) (before : SourceState) :
    poolView (record (.inr query) answer before) = record (.inr query) answer (poolView before) := by
  simp only [poolView, record, List.filter_append, List.filter_cons, keep, ↓reduceIte, List.filter_nil]

/-- Ordinary native randomness is forwarded unchanged to the joint experiment; only its extra uniform-query transcript entries are projected away. -/
theorem coins_source (primitives : PqxdhJointIdentity.Primitives) (work : ProbComp Value) (before : SourceState) :
    Prod.map id poolView <$>
      (simulateQ (lazyImpl primitives) (simulateQ coins work)).run before =
      (fun value => (value, poolView before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, coins, simulateQ_spec_query, StateT.run_bind, map_bind]
      change (do
        let answer ← (unifSpec.query query : ProbComp _)
        Prod.map id poolView <$>
          (simulateQ (lazyImpl primitives) (simulateQ coins (next answer))).run (record (.inl query) answer before)) = _
      apply bind_congr
      intro answer
      simpa only [pool_coin] using ih answer (record (.inl query) answer before)

private theorem sampled_create (primitives : PqxdhJointIdentity.Primitives)
    (before : SourceState) (world : PqxdhRecordLiftWorld.State n) :
    (simulateQ RegistrationWorldCoinCompiler.coin ((lazyImpl primitives (.inr .create)).run before)).run world =
      (fun seed => (createdReply primitives before seed, RegistrationNativeEnvSampling.advance 32 world)) <$>
        PqxdhJointIdentity.sampleSeed := by
  rw [lazyImpl_create]
  have sampling : (simulateQ RegistrationWorldCoinCompiler.coin PqxdhJointIdentity.sampleSeed).run world =
      (fun value => (value, RegistrationNativeEnvSampling.advance 32 world)) <$> PqxdhJointIdentity.sampleSeed :=
    RegistrationNativeEnvSampling.bytes 32 world
  rw [simulateQ_map, StateT.run_map, sampling]
  simp only [Functor.map_map]

private theorem compiled_create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : Context n KemSK × SourceState) :
    (compiled (source := source) setup checks representation created (.inr .create)).run before =
      (fun seed => ((createdReply setup.joint before.2 seed).1,
        (advance before.1, (createdReply setup.joint before.2 seed).2))) <$> PqxdhJointIdentity.sampleSeed := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl setup.joint) ((fun answer => (answer, advance before.1)) <$>
      (DynamicSpec.query (.inr .create) : OracleComp DynamicSpec _))).run before.2 = _
  rw [simulateQ_map, StateT.run_map, simulateQ_spec_query, lazyImpl_create]
  simp only [Functor.map_map]

private theorem native_create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : RegistrationNativeIdentityWorld.State n KemSK) :
    (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created (.inr .create)).run before =
      (fun seed => ((createdReply setup.joint before.identities seed).1,
        (⟨advance before.context, (createdReply setup.joint before.identities seed).2⟩ :
          RegistrationNativeIdentityWorld.State n KemSK))) <$> PqxdhJointIdentity.sampleSeed := by
  change (do
    let result ← (simulateQ RegistrationWorldCoinCompiler.coin ((lazyImpl setup.joint (.inr .create)).run before.identities)).run
      before.context.server.world.world.1
    pure (result.1.1, { before with
      identities := result.1.2
      context := { before.context with server := { before.context.server with world := { before.context.server.world with
        world := (result.2, before.context.server.world.world.2) } } } })) = _
  rw [sampled_create]
  simp only [bind_pure_comp, Functor.map_map, advance]

private theorem compiled_service (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (handle : Nat)
    (request : PqxdhJointIdentity.JointSpec.Domain) (before : Context n KemSK × SourceState) :
    (compiled (source := source) setup checks representation created (.inr (.service handle request))).run before =
      (let answer := (before.2.seeds[handle]?).map (fun seed => PqxdhJointIdentity.primitiveReply setup.joint seed request)
       pure (answer, (before.1, record (.inr (.service handle request)) answer before.2))) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl setup.joint) ((fun answer => (answer, before.1)) <$>
      (DynamicSpec.query (.inr (.service handle request)) : OracleComp DynamicSpec _))).run before.2 = _
  rw [simulateQ_map, StateT.run_map, simulateQ_spec_query]
  simp only [lazyImpl, poolImpl, StateT.run, map_pure]

private theorem compiled_reveal (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (handle : Nat) (before : Context n KemSK × SourceState) :
    (compiled (source := source) setup checks representation created (.inr (.reveal handle))).run before =
      pure (before.2.seeds[handle]?, (before.1, record (.inr (.reveal handle)) before.2.seeds[handle]? before.2)) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (lazyImpl setup.joint) ((fun answer => (answer, before.1)) <$>
      (DynamicSpec.query (.inr (.reveal handle)) : OracleComp DynamicSpec _))).run before.2 = _
  rw [simulateQ_map, StateT.run_map, simulateQ_spec_query]
  simp only [lazyImpl, poolImpl, StateT.run, map_pure]

private theorem native_reveal (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (handle : Nat)
    (before : RegistrationNativeIdentityWorld.State n KemSK) :
    (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created (.inr (.reveal handle))).run before =
      pure (before.identities.seeds[handle]?, { before with
        identities := record (.inr (.reveal handle)) before.identities.seeds[handle]? before.identities }) := by
  simp only [RegistrationNativeIdentityWorld.implementation, lazyImpl, poolImpl,
    StateT.run, simulateQ_pure,
    StateT.monad_pure_def, StateT.pure, pure_bind]

/-- Every public compiler operation recovers the actual same-World identity source after removing only the joint game's additional uniform-query transcript observations. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeIdentityFrontend.Trusted n KemSK).Domain)
    (before : Context n KemSK × SourceState) :
    Prod.map id project <$>
      (compiled (source := source) setup checks representation created query).run before =
      (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created query).run (project before) := by
  cases query with
  | inl query =>
      have law := congrArg (fun work => (fun result => (result.1.1,
        (⟨result.1.2, result.2⟩ : RegistrationNativeIdentityWorld.State n KemSK))) <$> work)
        (coins_source setup.joint
          ((RegistrationNativeIdentityWorld.ambient (mlSource := source) setup checks representation created query).run before.1) before.2)
      simp only [compiled, implementation, RegistrationNativeIdentityWorld.implementation,
        StateT.run, Functor.map_map, Prod.map_def, id_eq, project] at law ⊢
      convert law using 1
      rfl
  | inr query => cases query with
    | create =>
        rw [compiled_create, native_create]
        simp only [Functor.map_map]
        apply congrArg (fun change => change <$> PqxdhJointIdentity.sampleSeed)
        funext seed
        simp only [createdReply, project, poolView, record, List.filter_append,
          List.filter_cons, keep, ↓reduceIte, List.filter_nil, Prod.map_def, id_eq]
    | service handle request =>
        rw [compiled_service, RegistrationNativeIdentityWorld.service_source]
        simp only [map_pure, Prod.map_def, id_eq, project]
        rw [pool_service]
        rfl
    | reveal handle =>
        rw [compiled_reveal, native_reveal]
        simp only [map_pure, Prod.map_def, id_eq, project]
        rw [pool_service]
        rfl

/-- The concrete compiler preserves the complete continued same-World source execution for every adaptive native identity program. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) Value)
    (before : Context n KemSK × SourceState) :
    Prod.map id project <$>
      (simulateQ (compiled (source := source) setup checks representation created) work).run before =
      (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created) work).run (project before) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source setup checks representation created) work before

/-- The concrete query interpreter is exactly the ordinary indexed joint-service game run on the executable compiler's continued program and public auxiliary state. -/
theorem compiled_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) Value)
    (before : Context n KemSK × SourceState) :
    (simulateQ (compiled (source := source) setup checks representation created) work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (lazyImpl setup.joint)
          ((simulateQ (implementation (source := source) setup checks representation created) work).run before.1)).run before.2 := by
  have same : compiled (n := n) (source := source) setup checks representation created =
      QueryImpl.Stateful.link (implementation (n := n) (source := source) setup checks representation created) (lazyImpl setup.joint) := by
    funext query current
    rfl
  rw [same, QueryImpl.Stateful.simulateQ_link_run]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.coins_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.compiled_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCompiler.compiled_program
