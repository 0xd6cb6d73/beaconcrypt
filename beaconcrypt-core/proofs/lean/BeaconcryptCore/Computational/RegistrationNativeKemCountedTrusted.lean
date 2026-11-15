-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler

/-! The actual native trusted requests have a free indexed KEM interpretation with the complete source uniform ledger retained. The executable client state omits the private pool, which is held only by the capability interpreter. The source equality preserves all other native state, cache, histories and query failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State ofNative)
open RegistrationNativeKemCountedProgram (Spec)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Client" => State n source

def withWorld (before : Client) (world : PqxdhRecordLiftWorld.State n) : Client :=
  { before with server := { before.server with world := { before.server.world with world := (world, before.server.world.world.2) } } }

def world (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec KemSK)) Value) :
    StateT Client (OracleComp (Spec KemSK)) Value := fun before =>
  (fun result => (result.1, withWorld before result.2)) <$> work.run before.server.world.world.1

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem world_run (baseImpl : QueryImpl base ProbComp) (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec KemSK)) Value) (before : Client) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.runState baseImpl kem (world work) before pool =
      (fun result => ((result.1.1, withWorld before result.1.2), result.2)) <$>
        RegistrationNativeKemCountedProgram.runState baseImpl kem work before.server.world.world.1 pool := by
  simp only [RegistrationNativeKemCountedProgram.runState, world, StateT.run, RegistrationNativeKemCountedProgram.evaluate,
    simulateQ_map]
  rw [map_apply]
  rfl

noncomputable def other (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : RegistrationNativeKemInterface.OtherRequest) : StateT Client ProbComp
      (RegistrationNativeKemInterface.OtherSpec.Range query) := fun before => do
  let result ← (PqxdhRecordLiftWorld.sampled ((RegistrationNativeKemBackend.serverOther setup checks representation created.seed query).run
    before.server.world.auxiliary)).run before.server.world.world.1
  pure (result.1.1, { before with server := { before.server with world :=
    { before.server.world with auxiliary := result.1.2, world := (result.2, before.server.world.world.2) } } })

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Client (OracleComp (Spec KemSK)))
  | .inl query => world (RegistrationNativeKemCountedProgram.liftState (PqxdhRecordLiftWorld.effects query))
  | .inr (.inl query) => RegistrationNativeKemCountedProgram.liftState (other setup checks representation created query)
  | .inr (.inr query) => world (RegistrationNativeKemCountedProgram.call query)

def project (before : Native) : Client × Pool KemSK := (ofNative before, before.pool)
def arrange (result : (Value × Client) × Pool KemSK) : Value × (Client × Pool KemSK) := (result.1.1, (result.1.2, result.2))

noncomputable def execute (setup : Setup base KemSK) (work : StateT Client (OracleComp (Spec KemSK)) Value) :
    StateT (Client × Pool KemSK) ProbComp Value := fun before =>
  arrange <$> RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem work before.1 before.2

private theorem execute_pure (setup : Setup base KemSK) (value : Value) :
    execute setup (pure value : StateT Client (OracleComp (Spec KemSK)) Value) = pure value := by
  funext before
  simp only [execute, RegistrationNativeKemCountedProgram.run_pure, map_pure]
  rfl

private theorem execute_bind {Next : Type} (setup : Setup base KemSK)
    (work : StateT Client (OracleComp (Spec KemSK)) Value)
    (next : Value → StateT Client (OracleComp (Spec KemSK)) Next) :
    execute setup (work >>= next) = (execute setup work >>= fun value => execute setup (next value)) := by
  funext before
  change arrange <$> RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem (work >>= next) before.1 before.2 =
    ((execute setup work >>= fun value => execute setup (next value))).run before
  rw [RegistrationNativeKemCountedProgram.run_bind, StateT.run_bind]
  simp only [execute, StateT.run, map_bind, bind_map_left, arrange]

private theorem execute_simulate {κ : Type} {spec : OracleSpec κ} (setup : Setup base KemSK)
    (implementation : QueryImpl spec (StateT Client (OracleComp (Spec KemSK)))) (work : OracleComp spec Value) :
    execute setup (simulateQ implementation work) = simulateQ (fun query => execute setup (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, execute_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, execute_bind, ih]

/-- Every actual native trusted request retains all full counters and private pool state in its exact indexed free interpretation. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (before : Native) :
    arrange <$> RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem (implementation setup checks representation created query)
      (ofNative before) before.pool =
      Prod.map id project <$> (RegistrationNativeExperiment.trusted setup checks representation created source query).run before := by
  cases query with
  | inl query =>
    rw [implementation, world_run, RegistrationNativeKemCountedProgram.run_liftState]
    simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run, Functor.map_map,
      arrange, project, ofNative, withWorld, Prod.map, id_eq]
  | inr query => cases query with
    | inl query =>
      rw [implementation, RegistrationNativeKemCountedProgram.run_liftState]
      simp only [other, RegistrationNativeExperiment.trusted, RegistrationNativeKemInterface.source,
        PqxdhRecordLiftWorld.sampled, StateT.run, simulateQ_map, bind_pure_comp, Functor.map_map,
        arrange, project, ofNative, Prod.map, id_eq]
      rw [map_apply]
      simp only [Functor.map_map]
      rfl
    | inr query =>
      rw [implementation, world_run, RegistrationNativeKemCountedProgram.call_source]
      cases query with
      | inl query =>
        simp only [RegistrationNativeExperiment.trusted, RegistrationNativeKemInterface.source,
          RegistrationNativeKemCountedCapability.draw, StateT.run, PqxdhRecordLiftWorld.sampled, simulateQ_map,
          bind_pure_comp, Functor.map_map, arrange, project, ofNative, withWorld, Prod.map, id_eq]
        rw [map_apply]
        simp only [Functor.map_map]
        rfl
      | inr key =>
        simp only [RegistrationNativeExperiment.trusted, RegistrationNativeKemInterface.source,
          RegistrationNativeKemCountedCapability.draw, StateT.run, PqxdhRecordLiftWorld.sampled, lift_apply,
          simulateQ_map, bind_pure_comp, Functor.map_map, map_apply, arrange, project, ofNative, withWorld, Prod.map, id_eq]
        rfl

/-- Arbitrary actual trusted continuations preserve every full native coordinate and the private pool through the free indexed source. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (before : Native) :
    (execute setup (simulateQ (implementation setup checks representation created) work)).run (project before) =
      Prod.map id project <$> (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before := by
  have step (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (first : Native) :
      Prod.map id project <$> (RegistrationNativeExperiment.trusted setup checks representation created source query).run first =
        (execute setup (implementation setup checks representation created query)).run (project first) :=
    (query_source setup checks representation created query first).symm
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project step work before
  rw [execute_simulate]
  exact law.symm

end BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedTrusted.program_source
