-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFrontendInterface

/-! The full concrete native dispatcher opens every indexed KEM operation and the selected literal Server getter. Ordinary SDK build and record operations retain their actual capability/writer behavior. The only projection is the separately bounded private uniform counter; original public and secrecy ledgers are retained outside this dispatcher. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeKemServerState (mask ofNative)
open RegistrationNativeKemAcceptCompiler (nativeProject)
open RegistrationNativeKemFrontendInterface (Spec source)
open PqxdhRecordLiftInterface (RecordQuery RecordSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private def withWorld (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (world : PqxdhRecordLiftWorld.State n) :=
  (mask { ofNative before with server := { before.server with world :=
    { before.server.world with world := (world, before.server.world.world.2) } } }, before.pool)

/-- The actual closed SDK response builder is an ordinary ambient operation that never acquires the selected private KEM key. -/
theorem build_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (session : Nat) (application : Option (Slice U8)) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.server (RegistrationServerSdkSource.build setup (ledgerCodec wire) checks
          (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse session application)).run before =
      (simulateQ (source setup checks wire route representation created credential)
        ((Spec n mlSource KemSK).query (.inl (.inr (.build session application))) :
          OracleComp (Spec n mlSource KemSK) (RustM (Option (U64 × Pqxdh.Bytes))))).run (nativeProject before) := by
  have law := congrArg (fun run => (fun result =>
      (result.1, (mask { ofNative before with server := result.2 }, before.pool))) <$> run)
    (RegistrationNativeKemBuildUniform.build_input setup (ledgerCodec wire) checks
      (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse session application before.server)
  simp only [RegistrationNativeExperiment.server, simulateQ_spec_query, source,
    RegistrationNativeKemInterface.source, RegistrationNativeKemFrontendInterface.other,
    RegistrationNativeKemServerInterface.server, StateT.run, Functor.map_map, Prod.map, id_eq,
    nativeProject, RegistrationNativeKemServerState.project, ofNative, mask,
    RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask] at law ⊢
  convert law using 1
  rfl

/-- Ordinary ongoing records resolve actual retained owner routes and keep refusal, writer failure, frame logs, cache and complete private pool. -/
theorem record_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : RecordQuery) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$> (RegistrationNativeExperiment.record setup wire route query mlSource).run before =
      (simulateQ (source setup checks wire route representation created credential)
        ((Spec n mlSource KemSK).query (.inl (.inr (.record query))) :
          OracleComp (Spec n mlSource KemSK) ((RecordSpec .O).Range query))).run (nativeProject before) := by
  cases query with
  | inl query =>
      have law := congrArg (fun run => (fun result => (result.1, withWorld before result.2)) <$> run)
        (RegistrationNativeKemWorldRecordUniform.guarded_input setup (ledgerCodec wire) route
          (.inr (.inr (.inl query))) before.server.world.world.1)
      simp only [RegistrationNativeExperiment.record, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
        simulateQ_spec_query, source, RegistrationNativeKemInterface.source, RegistrationNativeKemFrontendInterface.other,
        RegistrationNativeKemFrontendInterface.record, RegistrationNativeKemFrontendInterface.world,
        StateT.run, Functor.map_map, Prod.map, id_eq, nativeProject,
        RegistrationNativeKemServerState.project, ofNative, withWorld, mask,
        RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask] at law ⊢
      convert law using 1 <;> rfl
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query with
      | inl plaintext =>
          cases found : before.beacons[owner]? with
          | none => simp only [RegistrationNativeExperiment.record, simulateQ_spec_query, source,
              RegistrationNativeKemInterface.source, RegistrationNativeKemFrontendInterface.other,
              RegistrationNativeKemFrontendInterface.record, StateT.run, nativeProject,
              RegistrationNativeKemServerState.project, ofNative, mask, RegistrationNativeKemServerState.maskServer,
              RegistrationNativeKemWorldUniform.mask, found, map_pure, Prod.map, id_eq]
          | some selected =>
              have law := congrArg (fun run => (fun result => (result.1, withWorld before result.2)) <$> run)
                (RegistrationNativeKemWorldRecordUniform.guarded_input setup (ledgerCodec wire) route
                  (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))) before.server.world.world.1)
              simp only [RegistrationNativeExperiment.record, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
                simulateQ_spec_query, source, RegistrationNativeKemInterface.source, RegistrationNativeKemFrontendInterface.other,
                RegistrationNativeKemFrontendInterface.record, RegistrationNativeKemFrontendInterface.world,
                StateT.run, Functor.map_map, Prod.map, id_eq, nativeProject,
                RegistrationNativeKemServerState.project, ofNative, withWorld, mask,
                RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask, found] at law ⊢
              convert law using 1
      | inr raw =>
          cases found : before.beacons[owner]? with
          | none => simp only [RegistrationNativeExperiment.record, simulateQ_spec_query, source,
              RegistrationNativeKemInterface.source, RegistrationNativeKemFrontendInterface.other,
              RegistrationNativeKemFrontendInterface.record, StateT.run, nativeProject,
              RegistrationNativeKemServerState.project, ofNative, mask, RegistrationNativeKemServerState.maskServer,
              RegistrationNativeKemWorldUniform.mask, found, map_pure, Prod.map, id_eq]
          | some selected =>
              have law := congrArg (fun run => (fun result => (result.1, withWorld before result.2)) <$> run)
                (RegistrationNativeKemWorldRecordUniform.guarded_input setup (ledgerCodec wire) route
                  (.inr (.inr (.inr (selected.worldOwner, .inr raw)))) before.server.world.world.1)
              simp only [RegistrationNativeExperiment.record, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
                simulateQ_spec_query, source, RegistrationNativeKemInterface.source, RegistrationNativeKemFrontendInterface.other,
                RegistrationNativeKemFrontendInterface.record, RegistrationNativeKemFrontendInterface.world,
                StateT.run, Functor.map_map, Prod.map, id_eq, nativeProject,
                RegistrationNativeKemServerState.project, ofNative, withWorld, mask,
                RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask, found] at law ⊢
              convert law using 1

end BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler.build_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler.record_source
