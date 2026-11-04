-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerPrimitive
import BeaconcryptCore.Computational.RegistrationNativeKemServerCompiler

/-! The actual complete Server agreement callback has a counted indexed interpretation with its full native request log, role, cache, counters and private pool retained. Stateful SDK pin/authentication/reservation prefixes are composed separately. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State ofNative)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativeKemCountedTrusted (execute arrange withWorld)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Client" => State n source
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem run_modify (setup : Setup base KemSK) (change : Client → Client) (before : Client) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem (modify change) before pool = pure (((), change before), pool) := by
  simp only [RegistrationNativeKemCountedProgram.runState, RegistrationNativeKemCountedProgram.evaluate, StateT.run_modify, simulateQ_pure, StateT.run_pure]

private theorem run_map {S : Type} (setup : Setup base KemSK) (function : Value → Next)
    (work : StateT S (OracleComp (Spec KemSK)) Value) (before : S) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem (function <$> work) before pool =
      (fun result => ((function result.1.1, result.1.2), result.2)) <$>
        RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem work before pool := by
  simp only [RegistrationNativeKemCountedProgram.runState, StateT.run_map, RegistrationNativeKemCountedProgram.evaluate, simulateQ_map]

private theorem world_run (setup : Setup base KemSK)
    (work : StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec KemSK)) Value) (before : Client) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem (RegistrationNativeKemCountedTrusted.world work) before pool =
      (fun result => ((result.1.1, withWorld before result.1.2), result.2)) <$>
        RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem work before.server.world.world.1 pool := by
  simp only [RegistrationNativeKemCountedProgram.runState, RegistrationNativeKemCountedTrusted.world, StateT.run,
    RegistrationNativeKemCountedProgram.evaluate, simulateQ_map]
  rw [map_apply]
  rfl

/-- Every actual logged native Server agreement query retains the full World and private pool in its indexed source. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : RegistrationAgreementExecutor.Request)
    (before : Client) (pool : Pool KemSK) :
    (execute setup (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created query)).run (before, pool) =
      (RegistrationNativeKemServerCompiler.nativeAgreement setup checks representation created query).run (before, pool) := by
  change arrange <$> RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem
    (modify (RegistrationNativeKemServerCompiler.logged query) >>= fun _ => RegistrationNativeKemCountedServerPrimitive.core setup checks representation created query)
    before pool = _
  rw [RegistrationNativeKemCountedProgram.run_bind, run_modify]
  simp only [pure_bind]
  cases query with
  | encapsulate key => cases key with
    | none =>
      simp only [RegistrationNativeKemCountedServerPrimitive.core, RegistrationNativeKemCountedServerPrimitive.missing,
        RegistrationNativeKemCountedProgram.run_pure, RegistrationNativeKemServerCompiler.nativeAgreement,
        RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
        RegistrationServerRoleBackend.localBackend, PqxdhRecordLiftWorld.sampled, StateT.run,
        map_pure, arrange, RegistrationNativeKemServerCompiler.logged]
      rfl
    | some key =>
      rw [RegistrationNativeKemCountedServerPrimitive.core, RegistrationNativeKemCountedServerPrimitive.encapsulate]
      by_cases valid : checks.kemKey (RegistrationRootInput.pqKey key) = true
      · simp only [valid, ite_true]
        rw [run_map, world_run, RegistrationNativeKemCountedProgram.call_source]
        simp only [RegistrationNativeKemServerCompiler.nativeAgreement, RegistrationWorldAgreement.agreement,
          RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend,
          valid, ite_true, PqxdhServerAuthExperiment.encapsulate, RegistrationNativeKemCountedCapability.draw,
          PqxdhRecordLiftWorld.sampled, StateT.run, lift_apply, simulateQ_map, map_apply, bind_pure_comp, Functor.map_map,
          arrange, withWorld, RegistrationNativeKemServerCompiler.logged, Prod.map, id_eq]
        rfl
      · simp only [valid, Bool.false_eq_true, ite_false, RegistrationNativeKemCountedProgram.run_pure,
          RegistrationNativeKemServerCompiler.nativeAgreement, RegistrationWorldAgreement.agreement,
          RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend,
          PqxdhRecordLiftWorld.sampled, StateT.run, map_pure,
          arrange, RegistrationNativeKemServerCompiler.logged]
        rfl
  | decapsulate ciphertext =>
    simp only [RegistrationNativeKemCountedServerPrimitive.core, RegistrationNativeKemCountedServerPrimitive.decapsulate,
      RegistrationNativeKemCountedProgram.run_pure, RegistrationNativeKemServerCompiler.nativeAgreement,
      RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.native,
      RegistrationServerRoleBackend.localBackend, PqxdhRecordLiftWorld.sampled, StateT.run,
      map_pure, arrange, RegistrationNativeKemServerCompiler.logged]
    rfl
  | root request =>
    simp only [RegistrationNativeKemCountedServerPrimitive.core, RegistrationNativeKemCountedProgram.run_pure,
      RegistrationNativeKemServerCompiler.nativeAgreement, RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
      PqxdhRecordLiftWorld.sampled, StateT.run, map_pure,
      arrange, RegistrationNativeKemServerCompiler.logged]
    rfl
  | convertPublic _ | convertSecret _ | generate _ | dh _ =>
    simp only [RegistrationNativeKemCountedServerPrimitive.core, RegistrationNativeKemCountedServerPrimitive.program,
      RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other, simulateQ_spec_query,
      RegistrationNativeKemCountedTrusted.implementation]
    rw [RegistrationNativeKemCountedProgram.run_liftState]
    simp only [RegistrationNativeKemCountedTrusted.other, RegistrationNativeKemServerCompiler.nativeAgreement,
      RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary, RegistrationNativeKemBackend.serverOther,
      RegistrationNativeKemInterface.OtherRequest.primitive, StateT.run, bind_pure_comp, Functor.map_map,
      arrange, RegistrationNativeKemServerCompiler.logged]
    rfl

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

/-- Every adaptive actual Server agreement continuation has the same complete indexed source state. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Client) (pool : Pool KemSK) :
    (execute setup (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) work)).run (before, pool) =
      (simulateQ (RegistrationNativeKemServerCompiler.nativeAgreement setup checks representation created) work).run (before, pool) := by
  rw [execute_simulate]
  have same : (fun query => execute setup (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created query)) =
      RegistrationNativeKemServerCompiler.nativeAgreement (n := n) (mlSource := source) setup checks representation created := by
    funext query current
    exact query_source setup checks representation created query current.1 current.2
  rw [same]

private def worldEmbed (before : Client) (pool : Pool KemSK)
    (world : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State) : Client × Pool KemSK :=
  ({ before with server := { before.server with world := world } }, pool)

private theorem native_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : Client) (pool : Pool KemSK) :
    (simulateQ (RegistrationNativeKemServerCompiler.nativeAgreement setup checks representation created) work).run (before, pool) =
      (fun result => (result.1, worldEmbed before pool result.2)) <$>
        (simulateQ (RegistrationWorldAgreement.agreement setup.source
          (RegistrationServerRoleBackend.native setup checks representation created.seed)) work).run before.server.world := by
  have step (query : RegistrationAgreementExecutor.Request) (first : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State) :
      Prod.map id (worldEmbed before pool) <$>
        (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed) query).run first =
      (RegistrationNativeKemServerCompiler.nativeAgreement setup checks representation created query).run (worldEmbed before pool first) := by
    simp only [RegistrationNativeKemServerCompiler.nativeAgreement, worldEmbed, StateT.run]
    rfl
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (worldEmbed before pool) step work before.server.world
  change (fun result => (result.1, worldEmbed before pool result.2)) <$>
      (simulateQ (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed)) work).run before.server.world =
    (simulateQ (RegistrationNativeKemServerCompiler.nativeAgreement setup checks representation created) work).run (before, pool) at law
  exact law.symm

private theorem run_get (setup : Setup base KemSK) (before : Client) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem get before pool = pure ((before, before), pool) := by
  simp only [RegistrationNativeKemCountedProgram.runState, RegistrationNativeKemCountedProgram.evaluate, StateT.run_get,
    simulateQ_pure, StateT.run_pure]

/-- The literal complete native Server agreement, including replay rejection and all failed continuations, has the exact counted indexed source. -/
theorem agree_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Native) :
    (execute setup (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)).run
      (RegistrationNativeKemCountedTrusted.project before) =
      Prod.map id RegistrationNativeKemCountedTrusted.project <$>
        (RegistrationNativeExperiment.server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)).run before := by
  change arrange <$> RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem
    (do let current ← get
        simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
          (RegistrationReplaySchedule.begin current.server.control authenticated current.server.consumed))
      (ofNative before) before.pool = _
  rw [RegistrationNativeKemCountedProgram.run_bind, run_get]
  simp only [pure_bind]
  change (execute setup (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
    (RegistrationReplaySchedule.begin before.server.control authenticated before.server.consumed))).run
      (RegistrationNativeKemCountedTrusted.project before) = _
  rw [program_source, native_program]
  simp only [RegistrationNativeExperiment.server, RegistrationServerNativeSource.agree, StateT.run,
    Functor.map_map, RegistrationNativeKemCountedTrusted.project, ofNative, worldEmbed, Prod.map, id_eq]

/-- Reassembling the entire private pool yields the literal actual native Server agreement and all original state fields. -/
theorem agree_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Native) :
    Prod.map id (fun current => RegistrationNativeKemServerState.toNative current.1 current.2) <$>
      (execute setup (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)).run
        (RegistrationNativeKemCountedTrusted.project before) =
      (RegistrationNativeExperiment.server (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)).run before := by
  rw [agree_source, Functor.map_map]
  change id <$> _ = _
  exact id_map _

end BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.agree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.agree_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.agree_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource.agree_native
