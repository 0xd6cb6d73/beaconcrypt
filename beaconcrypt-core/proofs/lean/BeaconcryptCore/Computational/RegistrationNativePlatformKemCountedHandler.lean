-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle
import BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon

/-! The corrected native typed dispatcher uses indexed true-cost KEM capabilities only at the actual constructor, Server agreement and Beacon completion sites. All source writers, allocator state, owner state and full primitive histories remain in their original order. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State ofNative toNative)
open RegistrationNativePlatformKemCountedProgram (M execute runState inject lift)
open RegistrationNativePlatformKemCountedBundle (project restore)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeWire (Wire ledgerCodec)
open PqxdhLiveKemBirth (Pool)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Client" => State n source
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

noncomputable def world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value) : StateT Client (StateT Platform ProbComp) Value :=
  fun before => StateT.lift ((fun result => (result.1, RegistrationNativeKemCountedTrusted.withWorld before result.2)) <$> work.run before.server.world.world.1)

def server (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value) :
    StateT Client (StateT Platform ProbComp) Value := fun before =>
  (fun result => (result.1, { before with server := result.2 })) <$> work.run before.server

noncomputable def record (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) :
    StateT Client (StateT Platform ProbComp) ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, before)
      | some selected => (world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some selected => (world (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (StateT Client (M KemSK Platform))
  | .inl coin => lift (world (PqxdhRecordLiftWorld.effects (.inl coin)))
  | .inr (.create edPin mlPin keyId) => inject (RegistrationNativeKemCountedBeacon.program setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))
  | .inr (.bundle owner) => RegistrationNativePlatformKemCountedBundle.program setup checks representation created implementation owner
  | .inr (.accept packet) => do
      modify fun before => { before with parsedAccepts := before.parsedAccepts + 1 }
      RegistrationNativePlatformKemCountedAccept.accept setup (ledgerCodec wire) checks (StateT.lift reserveRegistration)
        route representation created packet
  | .inr (.build session application) => lift (do
      let result ← server (RegistrationNativePlatformSourceSeal.build coins setup (ledgerCodec wire) view failure allocation
        erased reservePeer (RegistrationNativeMldsa.owned source credential) helper implementation session application)
      pure (do let optional ← result
               .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2))))
  | .inr (.finish owner packet) => inject (RegistrationNativeKemCountedBeacon.program setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire owner packet))
  | .inr (.hmac key message) => pure (setup.hmac.eval key message)
  | .inr (.hash bytes) => lift (world (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))))
  | .inr (.serverSend keyId plaintext) => lift (record setup wire route (.inl (.inl (plaintext, keyId))))
  | .inr (.serverRaw raw) => lift (record setup wire route (.inl (.inr raw)))
  | .inr (.beaconSend owner plaintext) => lift (record setup wire route (.inr (owner, .inl plaintext)))
  | .inr (.beaconRaw owner raw) => lift (record setup wire route (.inr (owner, .inr raw)))

omit primitives in
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
omit primitives in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

omit primitives in
private theorem world_source (setup : Setup base KemSK) (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : Native) (previous : Platform) :
    (execute setup (lift (world work))).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.world work))).run (before, previous) := by
  rw [RegistrationNativePlatformKemCountedProgram.execute_lift]
  simp only [world, RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.liftNative,
    RegistrationNativePlatformMldsaProgram.lift_coins, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    RegistrationNativeKemCountedTrusted.withWorld, StateT.run, lift_apply, Functor.map_map, project, ofNative, Prod.map, id_eq]

omit primitives in
private theorem beacon_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : Native) (previous : Platform) :
    (execute setup (inject (RegistrationNativeKemCountedBeacon.program setup checks representation created work))).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.beacon setup checks representation created work))).run (before, previous) := by
  have law := congrArg (fun distribution => (fun result => (result.1, ((result.2.1, previous), result.2.2))) <$> distribution)
    (RegistrationNativeKemCountedBeacon.source_program setup checks representation created work before)
  simp only [execute, RegistrationNativePlatformKemCountedProgram.run_inject,
    RegistrationNativePlatformKemCountedProgram.arrange, RegistrationNativePlatformPackedState.pack,
    RegistrationNativePlatformExperiment.liftNative, RegistrationNativePlatformMldsaProgram.lift_coins,
    StateT.run, lift_apply, Functor.map_map, project, RegistrationNativeKemCountedTrusted.execute,
    RegistrationNativeKemCountedTrusted.arrange, RegistrationNativeKemCountedTrusted.project, Prod.map, id_eq] at law ⊢
  exact law

omit primitives in
private theorem record_source (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : Native) (previous : Platform) :
    (execute setup (lift (record setup wire route query))).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.record setup wire route query source))).run (before, previous) := by
  cases query with
  | inl query => exact world_source setup _ before previous
  | inr query =>
      rcases query with ⟨owner, request⟩
      cases request with
      | inl plaintext =>
          cases found : before.beacons[owner]? with
          | none =>
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift]
              simp only [record, RegistrationNativeExperiment.record, project, ofNative, found,
                RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.liftNative,
                StateT.run, simulateQ_pure]
              rfl
          | some selected =>
              have law := world_source setup (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
                (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) before previous
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift] at law ⊢
              simp only [record, RegistrationNativeExperiment.record, RegistrationNativePlatformPackedState.pack,
                RegistrationNativePlatformExperiment.liftNative, StateT.run, project, ofNative, found] at law ⊢
              exact law
      | inr raw =>
          cases found : before.beacons[owner]? with
          | none =>
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift]
              simp only [record, RegistrationNativeExperiment.record, project, ofNative, found,
                RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.liftNative,
                StateT.run, simulateQ_pure]
              rfl
          | some selected =>
              have law := world_source setup (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
                (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) before previous
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift] at law ⊢
              simp only [record, RegistrationNativeExperiment.record, RegistrationNativePlatformPackedState.pack,
                RegistrationNativePlatformExperiment.liftNative, StateT.run, project, ofNative, found] at law ⊢
              exact law

omit primitives in
private theorem run_modify (setup : Setup base KemSK) (update : Client → Client)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    runState setup (modify update) before previous pool = pure ((((), update before), previous), pool) := by
  simp only [runState, StateT.run_modify, RegistrationNativeKemCountedProgram.evaluate, simulateQ_pure, StateT.run_pure]

/-- Every corrected native typed callback has the exact same full source state, private KEM rows, external platform and actual uniform ledger. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (before : Native) (previous : Platform) :
    (execute setup (handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper implementation query)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper implementation query)).run (before, previous) := by
  cases query with
  | inl coin => exact world_source setup _ before previous
  | inr command =>
      cases command with
      | create edPin mlPin keyId => exact beacon_source setup checks representation created _ before previous
      | bundle owner => exact RegistrationNativePlatformKemCountedBundle.source_program setup checks representation created implementation owner before previous
      | accept packet =>
          change @Eq (ProbComp ((RustM (Option Nat)) × ((Client × Platform) × Pool KemSK))) _ _
          change RegistrationNativePlatformKemCountedProgram.arrange <$> runState setup
            (modify (fun current : Client => { current with parsedAccepts := current.parsedAccepts + 1 }) >>= fun _ =>
              RegistrationNativePlatformKemCountedAccept.accept setup (ledgerCodec wire) checks (StateT.lift reserveRegistration)
                route representation created packet) (ofNative before) previous before.pool = _
          rw [RegistrationNativePlatformKemCountedProgram.run_bind, run_modify, pure_bind,
            RegistrationNativePlatformKemCountedAccept.accept_source]
          simp only [RegistrationNativePlatformExperiment.handler, RegistrationNativePlatformSourceAccept.accept]
          unfold RegistrationNativePlatformPackedState.pack
          dsimp only [StateT.run]
          simp only [StateT.monad_bind_def, StateT.bind]
          simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, Functor.map_map,
            RegistrationNativePlatformKemCountedProgram.arrange, project, ofNative, Prod.map, id_eq]
          have update : (modify (fun current : Native => { current with parsedAccepts := current.parsedAccepts + 1 }) :
              StateT Native (StateT Platform ProbComp) Unit) before previous =
              pure (((), { before with parsedAccepts := before.parsedAccepts + 1 }), previous) := rfl
          rw [update, pure_bind]
          simp only [Prod.map, id_eq, Functor.map_map]
          rfl
      | build session application =>
          change @Eq (ProbComp ((RustM (Option (U64 × Pqxdh.Bytes))) × ((Client × Platform) × Pool KemSK))) _ _
          rw [handler, RegistrationNativePlatformKemCountedProgram.execute_lift]
          simp only [RegistrationNativePlatformExperiment.handler]
          unfold RegistrationNativePlatformPackedState.pack
          dsimp only [StateT.run]
          simp only [StateT.monad_bind_def, StateT.bind]
          unfold server RegistrationNativePlatformExperiment.server
          simp only [StateT.run, map_apply, map_bind, bind_map_left, Functor.map_map,
            project, ofNative, Prod.map, id_eq]
          apply bind_congr
          rintro ⟨⟨result, current⟩, platform⟩
          rfl
      | finish owner packet => exact beacon_source setup checks representation created _ before previous
      | hmac key message =>
          rw [handler, RegistrationNativePlatformKemCountedProgram.execute_pure]
          rfl
      | hash bytes => exact world_source setup _ before previous
      | serverSend keyId plaintext => exact record_source setup wire route _ before previous
      | serverRaw raw => exact record_source setup wire route _ before previous
      | beaconSend owner plaintext => exact record_source setup wire route _ before previous
      | beaconRaw owner raw => exact record_source setup wire route _ before previous

/-- Arbitrary typed adaptive source work retains the same native client, external platform, full private rows and all actual source counters. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp TypedSpec Value) (before : Native) (previous : Platform) :
    (execute setup (simulateQ (handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper implementation) work)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper implementation) work)).run (before, previous) := by
  have step (query : TypedSpec.Domain) (first : Native × Platform) :
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper implementation query)).run first =
        (execute setup (handler setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper implementation query)).run (project first) :=
    (query_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased
      helper implementation query first.1 first.2).symm
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project step work (before, previous)
  rw [RegistrationNativePlatformKemCountedProgram.execute_simulate, RegistrationNativePlatformPackedState.simulate_pack]
  exact law.symm

/-- Reassembling the complete private KEM state yields the literal corrected typed source program. -/
theorem native_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp TypedSpec Value) (before : Native) (previous : Platform) :
    Prod.map id restore <$> (execute setup (simulateQ (handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper implementation) work)).run (project (before, previous)) =
      (RegistrationNativePlatformPackedState.pack
        (simulateQ (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper implementation) work)).run (before, previous) := by
  rw [program_source, Functor.map_map]
  change id <$> _ = _
  exact id_map _

end BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler.native_source
