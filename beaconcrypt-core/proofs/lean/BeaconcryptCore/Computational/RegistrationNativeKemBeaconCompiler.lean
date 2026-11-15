-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemWorldEffects

/-! The actual Beacon primitive frontend opens its indexed birth and decapsulation requests through the same private KEM service as the selected Server getter. Public World effects use the original shared cache and capabilities. All source state and private pool entries remain in the equality except the separately bounded uniform ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeKemServerState (State mask ofNative)
open RegistrationNativeKemServerInterface (source withRole)
open RegistrationNativeKemAcceptCompiler (nativeProject)
variable {ι KemSK Reader Response Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK)
    (OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK))
  | .inl query => (RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.world query))
  | .inr query => RegistrationNativeKemServerInterface.lift query

private theorem primitive_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : State n mlSource) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup codec checks route verify representation created)
      (RegistrationNativeKemServerInterface.lift query)).run (mask before, pool) =
      (fun result => (result.1, (withRole (mask before) result.2.1, result.2.2))) <$>
        (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
            (before.server.world.auxiliary, pool) := by
  rcases query with query | (query | key)
  · simp only [RegistrationNativeKemServerInterface.lift, simulateQ_spec_query, source,
      RegistrationNativeKemInterface.source, RegistrationNativeKemServerInterface.other, StateT.run,
      Functor.map_map, withRole, mask, RegistrationNativeKemServerState.maskServer,
      RegistrationNativeKemWorldUniform.mask]
  · simp only [RegistrationNativeKemServerInterface.lift, simulateQ_spec_query, source,
      RegistrationNativeKemInterface.source, StateT.run, Functor.map_map, withRole, mask,
      RegistrationNativeKemServerState.maskServer]
  · simp only [RegistrationNativeKemServerInterface.lift, simulateQ_spec_query, source,
      RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp, Functor.map_map,
      withRole, mask, RegistrationNativeKemServerState.maskServer]

private def withWorldRole (before : State n mlSource) (world : PqxdhRecordLiftWorld.State n)
    (role : RegistrationServerRoleBackend.State) : State n mlSource :=
  { before with server := { before.server with world :=
    ⟨role, before.server.world.requests, before.server.world.recordRequests, (world, before.server.world.world.2)⟩ } }

private theorem native_canonical (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.trusted setup checks representation created mlSource (.inr query)).run before =
      (fun result => (result.1, (withRole (mask (ofNative before)) result.2.1, result.2.2))) <$>
        (RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
            (before.server.world.auxiliary, before.pool) := by
  have law := congrArg (fun work => (fun result =>
      (result.1.1, (withWorldRole (ofNative before) result.2 result.1.2.1, result.1.2.2))) <$> work)
    (RegistrationNativeKemWorldUniform.sampled_mask
      ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
        (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
          (before.server.world.auxiliary, before.pool)) before.server.world.world.1)
  simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, nativeProject,
    RegistrationNativeKemServerState.project, ofNative, mask, RegistrationNativeKemServerState.maskServer,
    RegistrationNativeKemWorldUniform.mask, withWorldRole, withRole] at law ⊢
  convert law using 1

/-- Actual native birth/handle operations and public World effects share the exposed selected-KEM source, including their complete private pool and reached failure states. -/
theorem trusted_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run before =
      (simulateQ (source setup codec checks route verify representation created) (trusted query)).run (nativeProject before) := by
  cases query with
  | inl query =>
      have law := congrArg (fun work => (fun result =>
          (result.1, (withWorldRole (ofNative before) result.2 before.server.world.auxiliary, before.pool))) <$> work)
        (RegistrationNativeKemWorldEffects.effects_input query before.server.world.world.1)
      simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server, trusted, simulateQ_spec_query, source,
        RegistrationNativeKemInterface.source, RegistrationNativeKemServerInterface.other,
        StateT.run, Functor.map_map, Prod.map, id_eq, nativeProject,
        RegistrationNativeKemServerState.project, ofNative, withWorldRole, mask,
        RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask] at law ⊢
      convert law using 1 <;> rfl
  | inr query =>
      rw [native_canonical]
      exact (primitive_source setup codec checks route verify representation created query (ofNative before) before.pool).symm

/-- An arbitrary actual Beacon primitive continuation, with adaptive handle use, compiles without any whole-program simulation premise. -/
theorem trusted_program (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work).run before =
      (simulateQ (source setup codec checks route verify representation created)
        (simulateQ trusted work)).run (nativeProject before) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ nativeProject
    (trusted_source setup codec checks route verify representation created) work before

private theorem get_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup codec checks route verify representation created)
      RegistrationNativeKemServerInterface.get).run before =
      pure (mask before.1, (mask before.1, before.2)) := by
  simp only [RegistrationNativeKemServerInterface.get, simulateQ_spec_query, source,
    RegistrationNativeKemInterface.source, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure]

private theorem put_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (next : State n mlSource) :
    (simulateQ (source setup codec checks route verify representation created)
      (RegistrationNativeKemServerInterface.put next)).run before = pure ((), (mask next, before.2)) := by
  simp only [RegistrationNativeKemServerInterface.put, simulateQ_spec_query, source,
    RegistrationNativeKemInterface.source, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure]

/-- The local owner and environment state are threaded outside the private indexed KEM service. -/
noncomputable def beacon
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) Value := do
  let before ← RegistrationNativeKemServerInterface.get
  let result ← simulateQ trusted ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))
  let current ← RegistrationNativeKemServerInterface.get
  RegistrationNativeKemServerInterface.put
    { current with beacons := result.1.2, server := { current.server with world := (RegistrationWorldAgreementCompiler.join result.2 current.server.world.world.1) } }
  pure result.1.1

/-- Every complete actual Beacon constructor, outgoing Init or finishing controller has the same full operational output through indexed KEM birth/decapsulation and the original World cache. -/
theorem beacon_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$> (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      (simulateQ (source setup codec checks route verify representation created) (beacon work)).run (nativeProject before) := by
  have law := congrArg (fun run => (fun result => (result.1.1.1,
      (mask { result.2.1 with beacons := result.1.1.2, server := { result.2.1.server with world := (RegistrationWorldAgreementCompiler.join result.1.2 result.2.1.server.world.world.1) } }, result.2.2))) <$> run)
    (trusted_program setup codec checks route verify representation created
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before)
  simp only [beacon, simulateQ_bind, StateT.run_bind, get_run, put_run, pure_bind,
    simulateQ_map, StateT.run_map, bind_pure_comp, map_pure]
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, nativeProject,
    RegistrationNativeKemServerState.project, ofNative, mask, RegistrationNativeKemServerState.maskServer,
    RegistrationNativeKemWorldUniform.mask, RegistrationWorldAgreementCompiler.erase,
    RegistrationWorldAgreementCompiler.join] at law ⊢
  convert law using 1

end BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler.trusted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler.trusted_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler.trusted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBeaconCompiler.beacon_source
