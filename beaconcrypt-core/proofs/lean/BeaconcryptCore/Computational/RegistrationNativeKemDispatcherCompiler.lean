-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFrontendCompiler

/-! The complete native typed and original raw secrecy-ledger programs compile to the indexed private KEM source. Actual generated owner creation, outgoing publication, mandatory incoming authentication, replay, signed response, finish, raw record refusal and all failure states are retained. Only the independently bounded uniform analysis coordinate is projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeKemFrontendInterface (Spec source)
open RegistrationNativeKemAcceptCompiler (nativeProject)
open RegistrationNativeRawAdapter (TypedSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def handler (setup : Setup base KemSK) (wire : Wire) (checks : Checks) :
    QueryImpl TypedSpec (OracleComp (Spec n mlSource KemSK))
  | .inl coin => simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemBeaconCompiler.trusted (.inl (.inl coin)))
  | .inr (.create edPin mlPin keyId) => simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemBeaconCompiler.beacon
      (RegistrationNativeBeaconFrontend.create setup mlSource edPin mlPin keyId))
  | .inr (.bundle owner) => simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemBeaconCompiler.beacon
      (RegistrationNativeBeaconFrontend.bundle setup mlSource wire owner))
  | .inr (.accept packet) => simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemServerInterface.typedAccept setup checks packet)
  | .inr (.build session application) => (Spec n mlSource KemSK).query (.inl (.inr (.build session application)))
  | .inr (.finish owner packet) => simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemBeaconCompiler.beacon
      (RegistrationNativeBeaconFrontend.finish setup mlSource wire owner packet))
  | .inr (.hmac key message) => pure (setup.hmac.eval key message)
  | .inr (.hash bytes) => simulateQ RegistrationNativeKemFrontendInterface.lift (RegistrationNativeKemBeaconCompiler.trusted (.inl (.inr (.hash bytes))))
  | .inr (.serverSend keyId plaintext) => (Spec n mlSource KemSK).query (.inl (.inr (.record (.inl (.inl (plaintext, keyId))))))
  | .inr (.serverRaw raw) => (Spec n mlSource KemSK).query (.inl (.inr (.record (.inl (.inr raw)))))
  | .inr (.beaconSend owner plaintext) => (Spec n mlSource KemSK).query (.inl (.inr (.record (.inr (owner, .inl plaintext)))))
  | .inr (.beaconRaw owner raw) => (Spec n mlSource KemSK).query (.inl (.inr (.record (.inr (owner, .inr raw)))))

/-- Every actual native dispatcher operation opens its KEM requests with the original complete reached private source state. -/
theorem handler_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before =
      (simulateQ (source setup checks wire route representation created credential) (handler setup wire checks query)).run (nativeProject before) := by
  cases query with
  | inl coin =>
      simp only [handler, RegistrationNativeKemFrontendInterface.lift_program]
      exact RegistrationNativeKemBeaconCompiler.trusted_source setup (ledgerCodec wire) checks route mlSource.verify
        representation created (.inl (.inl coin)) before
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
          simp only [handler, RegistrationNativeKemFrontendInterface.lift_program, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemBeaconCompiler.beacon_source setup (ledgerCodec wire) checks route mlSource.verify representation created _ before
      | bundle owner =>
          simp only [handler, RegistrationNativeKemFrontendInterface.lift_program, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemBeaconCompiler.beacon_source setup (ledgerCodec wire) checks route mlSource.verify representation created _ before
      | accept packet =>
          simp only [handler, RegistrationNativeKemFrontendInterface.lift_program]
          exact RegistrationNativeKemAcceptCompiler.handler_source setup checks wire route representation created credential packet before
      | build session application =>
          simp only [handler, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemFrontendCompiler.build_source setup checks wire route representation created credential session application before
      | finish owner packet =>
          simp only [handler, RegistrationNativeKemFrontendInterface.lift_program, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemBeaconCompiler.beacon_source setup (ledgerCodec wire) checks route mlSource.verify representation created _ before
      | hmac key message =>
          simp only [handler, RegistrationNativeExperiment.handler, simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
      | hash bytes =>
          simp only [handler, RegistrationNativeKemFrontendInterface.lift_program]
          exact RegistrationNativeKemBeaconCompiler.trusted_source setup (ledgerCodec wire) checks route mlSource.verify
            representation created (.inl (.inr (.hash bytes))) before
      | serverSend keyId plaintext =>
          simp only [handler, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemFrontendCompiler.record_source setup checks wire route representation created credential (.inl (.inl (plaintext, keyId))) before
      | serverRaw raw =>
          simp only [handler, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemFrontendCompiler.record_source setup checks wire route representation created credential (.inl (.inr raw)) before
      | beaconSend owner plaintext =>
          simp only [handler, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemFrontendCompiler.record_source setup checks wire route representation created credential (.inr (owner, .inl plaintext)) before
      | beaconRaw owner raw =>
          simp only [handler, RegistrationNativeExperiment.handler]
          exact RegistrationNativeKemFrontendCompiler.record_source setup checks wire route representation created credential (.inr (owner, .inr raw)) before

/-- Arbitrary adaptive typed native programs compile from their proved actual per-operation laws. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp TypedSpec Value) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) work).run before =
      (simulateQ (source setup checks wire route representation created credential)
        (simulateQ (handler setup wire checks) work)).run (nativeProject before) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ nativeProject
    (handler_source setup checks wire route representation created credential) work before

def fullProject (result : Value × (RegistrationNativeLedger.State × RegistrationNativeExperiment.State n KemSK mlSource)) :=
  (result.1, (result.2.1, nativeProject result.2.2))

/-- The original full raw-CBOR execution retains all hidden test bits, fresh draws, native ML-pin-aware public entries and failed typed poststates through the actual indexed KEM source. -/
theorem full_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    fullProject <$> RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (source setup checks wire route representation created credential)
          (simulateQ (handler setup wire checks) (RegistrationNativeFullCompiler.compile setup.source.crypto wire
            created.server.server.metadata.sender bounds mode work))).run (nativeProject before) := by
  rw [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run]
  have law := congrArg (fun run => (fun result => (result.1.1, (result.1.2, result.2))) <$> run)
    (program_source setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before)
  simpa only [fullProject, Functor.map_map, Prod.map, id_eq, Function.comp_def] using law

end BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler.full_source
