-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle
import BeaconcryptCore.Computational.RegistrationNativeKemCountedBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler

/-! The single runtime profile combines actual dynamic ordinary record writers with the same indexed true-cost KEM registration callbacks. The new source equality retains all runtime writer rejection effects, continuation state, private rows and draw costs. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler
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

attribute [local irreducible] RegistrationNativePlatformKemCountedHandler.handler
  RegistrationNativePlatformExperiment.handler RegistrationNativePlatformKemCountedProgram.execute

def world (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value) : StateT Client (StateT Platform ProbComp) Value :=
  fun before => (fun result => (result.1, RegistrationNativeKemCountedTrusted.withWorld before result.2)) <$> work.run before.server.world.world.1

noncomputable def record (setup : Setup base KemSK) (wire : Wire)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    StateT Client (StateT Platform ProbComp) ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => world (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, before)
      | some selected => (world (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some selected => (world (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (StateT Client (M KemSK Platform))
  | .inr (.serverSend keyId plaintext) => lift (record setup wire reserveFrame route (.inl (.inl (plaintext, keyId))))
  | .inr (.serverRaw raw) => lift (record setup wire reserveFrame route (.inl (.inr raw)))
  | .inr (.beaconSend owner plaintext) => lift (record setup wire reserveFrame route (.inr (owner, .inl plaintext)))
  | .inr (.beaconRaw owner raw) => lift (record setup wire reserveFrame route (.inr (owner, .inr raw)))
  | query => RegistrationNativePlatformKemCountedHandler.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route representation created credential view failure allocation reserveRegistration reservePeer erased helper implementation query

omit primitives in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

omit primitives in
private theorem world_source (setup : Setup base KemSK) (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value)
    (before : Native) (previous : Platform) :
    (execute setup (lift (world work))).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformOrdinaryExperiment.world work)).run (before, previous) := by
  rw [RegistrationNativePlatformKemCountedProgram.execute_lift]
  simp only [world, RegistrationNativePlatformOrdinaryExperiment.world, RegistrationNativePlatformOrdinaryExperiment.replaceWorld,
    RegistrationNativePlatformPackedState.pack, StateT.run, map_apply, Functor.map_map,
    project, ofNative, RegistrationNativeKemCountedTrusted.withWorld, Prod.map, id_eq]

omit primitives in
private theorem record_source (setup : Setup base KemSK) (wire : Wire)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) (before : Native) (previous : Platform) :
    (execute setup (lift (record setup wire reserveFrame route query))).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source)).run (before, previous) := by
  cases query with
  | inl query => exact world_source setup _ before previous
  | inr query =>
      rcases query with ⟨owner, request⟩
      cases request with
      | inl plaintext =>
          cases found : before.beacons[owner]? with
          | none =>
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift]
              simp only [record, RegistrationNativePlatformOrdinaryExperiment.record, project, ofNative, found,
                RegistrationNativePlatformPackedState.pack, StateT.run]
              rfl
          | some selected =>
              have law := world_source setup (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route
                (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) before previous
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift] at law ⊢
              simp only [record, RegistrationNativePlatformOrdinaryExperiment.record, RegistrationNativePlatformPackedState.pack,
                StateT.run, project, ofNative, found] at law ⊢
              exact law
      | inr raw =>
          cases found : before.beacons[owner]? with
          | none =>
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift]
              simp only [record, RegistrationNativePlatformOrdinaryExperiment.record, project, ofNative, found,
                RegistrationNativePlatformPackedState.pack, StateT.run]
              rfl
          | some selected =>
              have law := world_source setup (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserveFrame route
                (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) before previous
              rw [RegistrationNativePlatformKemCountedProgram.execute_lift] at law ⊢
              simp only [record, RegistrationNativePlatformOrdinaryExperiment.record, RegistrationNativePlatformPackedState.pack,
                StateT.run, project, ofNative, found] at law ⊢
              exact law

theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (before : Native) (previous : Platform) :
    (execute setup (handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation query)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query)).run (before, previous) := by
  cases query with
  | inl query =>
      exact RegistrationNativePlatformKemCountedHandler.query_source setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper implementation (.inl query) before previous
  | inr command =>
      cases command with
      | serverSend keyId plaintext => exact record_source setup wire reserveFrame route _ before previous
      | serverRaw raw => exact record_source setup wire reserveFrame route _ before previous
      | beaconSend owner plaintext => exact record_source setup wire reserveFrame route _ before previous
      | beaconRaw owner raw => exact record_source setup wire reserveFrame route _ before previous
      | create edPin mlPin keyId =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.create edPin mlPin keyId)) before previous)
      | bundle owner =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.bundle owner)) before previous)
      | accept packet =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.accept packet)) before previous)
      | build session application =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.build session application)) before previous)
      | finish owner packet =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.finish owner packet)) before previous)
      | hmac key message =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.hmac key message)) before previous)
      | hash bytes =>
          exact (RegistrationNativePlatformKemCountedHandler.query_source (n := n) (Platform := Platform) (E := E) (source := source)
              setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created
              credential view failure allocation reserveRegistration reservePeer erased helper implementation
              (.inr (.hash bytes)) before previous)

/-- Arbitrary typed adaptive source work retains the same native client, external platform, full private rows and all actual source counters. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp TypedSpec Value) (before : Native) (previous : Platform) :
    (execute setup (simulateQ (handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation) work)).run (project (before, previous)) =
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (simulateQ (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation) work)).run (before, previous) := by
  have step (query : TypedSpec.Domain) (first : Native × Platform) :
      Prod.map id project <$> (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query)).run first =
        (execute setup (handler setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation query)).run (project first) :=
    (query_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased
      helper implementation query first.1 first.2).symm
  have law := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project step work (before, previous)
  rw [RegistrationNativePlatformKemCountedProgram.execute_simulate, RegistrationNativePlatformPackedState.simulate_pack]
  exact law.symm

/-- Reassembling the complete private KEM state yields the literal corrected typed source program. -/
theorem native_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp TypedSpec Value) (before : Native) (previous : Platform) :
    Prod.map id restore <$> (execute setup (simulateQ (handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation) work)).run (project (before, previous)) =
      (RegistrationNativePlatformPackedState.pack
        (simulateQ (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper implementation) work)).run (before, previous) := by
  rw [program_source, Functor.map_map]
  change id <$> _ = _
  exact id_map _

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler.native_source
