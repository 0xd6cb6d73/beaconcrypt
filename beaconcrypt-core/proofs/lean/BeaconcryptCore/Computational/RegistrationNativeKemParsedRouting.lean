-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemRouting

/-! Only the chosen decoded accept attempt exposes its literal native KEM getter. Every earlier or later attempt uses ordinary public encapsulation, without moving the selected cut. The selector reads the actual source parsed-attempt counter before that attempt increments, including authentication and replay failures. Complete native/raw ledger outcomes are preserved. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemAcceptCompiler (nativeProject)
open RegistrationNativeRawAdapter (TypedSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Ambient (n : Nat) (mlSource : RegistrationNativeMldsa.Source) :=
  RegistrationNativeKemFrontendInterface.Ambient n mlSource + RegistrationNativeKemInterface.EncapsulationSpec
abbrev Spec (n : Nat) (mlSource : RegistrationNativeMldsa.Source) (KemSK : Type) :=
  RegistrationNativeKemInterface.Spec (Ambient n mlSource) KemSK

noncomputable def other (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource) :=
  RegistrationNativeKemRouting.publicAmbient setup.baseImpl setup.kem
    (RegistrationNativeKemFrontendInterface.other (n := n) setup checks wire route representation created credential)

noncomputable def source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource) :=
  RegistrationNativeKemInterface.source setup.baseImpl setup.kem (Ambient n mlSource)
    (other setup checks wire route representation created credential)

def get : OracleComp (Spec n mlSource KemSK) (RegistrationNativeKemServerState.State n mlSource) :=
  (Spec n mlSource KemSK).query (.inl (.inl (.inl .get)))

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (selected : Nat) :
    QueryImpl TypedSpec (OracleComp (Spec n mlSource KemSK))
  | .inr (.accept packet) => do
      let before ← get
      simulateQ (RegistrationNativeKemRouting.route (decide (before.parsedAccepts = selected)))
        (RegistrationNativeKemDispatcherCompiler.handler setup wire checks (.inr (.accept packet)))
  | query => simulateQ (RegistrationNativeKemRouting.route false)
      (RegistrationNativeKemDispatcherCompiler.handler setup wire checks query)

private theorem route_run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (chosen : Bool) (work : OracleComp (RegistrationNativeKemFrontendInterface.Spec n mlSource KemSK) Value)
    (before : RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup checks wire route representation created credential)
      (simulateQ (RegistrationNativeKemRouting.route chosen) work)).run before =
      (simulateQ (RegistrationNativeKemFrontendInterface.source setup checks wire route representation created credential) work).run before :=
  RegistrationNativeKemRouting.program_source setup.baseImpl setup.kem
    (RegistrationNativeKemFrontendInterface.other setup checks wire route representation created credential) chosen work before

private theorem get_run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (simulateQ (source setup checks wire route representation created credential) get).run (nativeProject before) =
      pure ((nativeProject before).1, nativeProject before) := by
  simp only [RegistrationNativeKemParsedRouting.get, simulateQ_spec_query, source, other,
    RegistrationNativeKemRouting.publicAmbient, RegistrationNativeKemInterface.source,
    RegistrationNativeKemFrontendInterface.other, RegistrationNativeKemServerInterface.other,
    StateT.run, map_pure, nativeProject, RegistrationNativeKemServerState.project,
    RegistrationNativeKemServerState.mask_idempotent]

/-- The chosen native parsed-attempt routing preserves the complete actual dispatcher, including every rejected attempt and original state. -/
theorem handler_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (selected : Nat) (query : TypedSpec.Domain) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query).run before =
      (simulateQ (source setup checks wire route representation created credential) (handler setup checks wire selected query)).run (nativeProject before) := by
  cases query with
  | inl coin =>
      simp only [handler, route_run]
      exact RegistrationNativeKemDispatcherCompiler.handler_source setup checks wire route representation created credential _ before
  | inr command =>
      cases command <;> simp only [handler, simulateQ_bind, StateT.run_bind, get_run, pure_bind, route_run]
      all_goals exact RegistrationNativeKemDispatcherCompiler.handler_source setup checks wire route representation created credential _ before

/-- Arbitrary adaptive typed programs preserve the original source while only the chosen decoded attempt can expose an encapsulation. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (selected : Nat) (work : OracleComp TypedSpec Value) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) work).run before =
      (simulateQ (source setup checks wire route representation created credential)
        (simulateQ (handler setup checks wire selected) work)).run (nativeProject before) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ nativeProject
    (handler_source setup checks wire route representation created credential selected) work before

/-- The complete original raw-CBOR and hidden secrecy ledger executes the actual selected-attempt client, including all public failures and private draws. -/
theorem full_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (selected : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    RegistrationNativeKemDispatcherCompiler.fullProject <$>
        RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (source setup checks wire route representation created credential)
          (simulateQ (handler setup checks wire selected) (RegistrationNativeFullCompiler.compile setup.source.crypto wire
            created.server.server.metadata.sender bounds mode work))).run (nativeProject before) := by
  rw [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run]
  have law := congrArg (fun run => (fun result => (result.1.1, (result.1.2, result.2))) <$> run)
    (program_source setup checks wire route representation created credential selected
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before)
  simpa only [RegistrationNativeKemDispatcherCompiler.fullProject, Functor.map_map, Prod.map, id_eq, Function.comp_def] using law

end BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting.full_source
