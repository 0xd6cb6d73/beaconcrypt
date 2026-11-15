-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication
import BeaconcryptCore.Computational.RegistrationNativeReceiveDispatch

/-! One unchanged mandatory-ML native experiment interpreted with the actual extracted authentication and ordinary receive controllers. The original typed parser, routing, full protocol/primitive state, secret test bit and ledger, constructor failures and every later callback are retained. The only added primitive functional contract is AEAD plaintext length. This is source-controller composition within the existing native Wire/frontend model; concrete source codec and public-wrapper correspondence remain separate obligations. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeExtractedControllers
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (RecordQuery)
open RegistrationNativeWire (Wire ledgerCodec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

/-- The exact existing owner-to-World address selection surrounds the source-selected guarded record service. -/
noncomputable def record (setup : Setup base KemSK) (wire : Wire) (erased : Array Std.U8 227#usize)
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery)
    (mlSource : RegistrationNativeMldsa.Source) : RegistrationNativeExperiment.M n KemSK mlSource ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) :=
  match query with
  | .inl query => RegistrationNativeExperiment.world (RegistrationNativeReceiveDispatch.guarded setup wire erased route (.inr (.inr (.inl query))))
  | .inr (owner, .inl plaintext) => fun before => match before.beacons[owner]? with
      | none => pure (none, before)
      | some selected => (RegistrationNativeExperiment.world (RegistrationNativeReceiveDispatch.guarded setup wire erased route
          (.inr (.inr (.inr (selected.worldOwner, .inl plaintext)))))).run before
  | .inr (owner, .inr raw) => fun before => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some selected => (RegistrationNativeExperiment.world (RegistrationNativeReceiveDispatch.guarded setup wire erased route
          (.inr (.inr (.inr (selected.worldOwner, .inr raw)))))).run before

/-- The complete native record interface retains all owner addresses, returned values and protocol/primitive states. -/
theorem record_native (setup : Setup base KemSK) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (query : RecordQuery) (mlSource : RegistrationNativeMldsa.Source) :
    record (n := n) setup wire erased route query mlSource =
      RegistrationNativeExperiment.record setup wire route query mlSource := by
  simp only [record, RegistrationNativeExperiment.record,
    RegistrationNativeReceiveDispatch.guarded_native setup wire length erased route]
  rfl

/-- Every native finish uses extracted response authentication, and every ordinary raw receive uses the extracted receive loop. -/
noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.M n KemSK mlSource)
  | .inr (.serverSend keyId plaintext) => record setup wire erased route (.inl (.inl (plaintext, keyId))) mlSource
  | .inr (.serverRaw bytes) => record setup wire erased route (.inl (.inr bytes)) mlSource
  | .inr (.beaconSend index plaintext) => record setup wire erased route (.inr (index, .inl plaintext)) mlSource
  | .inr (.beaconRaw index bytes) => record setup wire erased route (.inr (index, .inr bytes)) mlSource
  | query => RegistrationNativeExtractedAuthentication.handler setup checks wire route representation created mlSource credential query

/-- Callback equality preserves the same shared primitive caches, counters, private kernels, owner maps and optional-failure poststates through one deployment. -/
theorem handler_native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource) :
    handler (n := n) setup checks wire erased route representation created mlSource credential =
      RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential := by
  funext query
  have auth := congrFun
    (RegistrationNativeExtractedAuthentication.handler_native (n := n) setup checks wire route representation created mlSource credential) query
  cases query with
  | inl coin => exact auth
  | inr command =>
      cases command with
      | serverSend keyId plaintext => exact record_native setup wire length erased route (.inl (.inl (plaintext, keyId))) mlSource
      | serverRaw bytes => exact record_native setup wire length erased route (.inl (.inr bytes)) mlSource
      | beaconSend index plaintext => exact record_native setup wire length erased route (.inr (index, .inl plaintext)) mlSource
      | beaconRaw index bytes => exact record_native setup wire length erased route (.inr (index, .inr bytes)) mlSource
      | create edPin mlPin keyId => exact auth
      | bundle owner => exact auth
      | accept raw => exact auth
      | build session payload => exact auth
      | finish owner raw => exact auth
      | hmac key bytes => exact auth
      | hash bytes => exact auth

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :=
  RegistrationNativeFullCompiler.run setup.source.crypto wire created.server.server.metadata.sender bounds
    (handler setup checks wire erased route representation created mlSource credential) mode work before

/-- Every adaptive native execution retains its complete joint result and state under the source-controller interpretation. -/
theorem run_native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    run setup checks wire erased route representation created mlSource credential bounds mode work before =
      RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before := by
  simp only [run, RegistrationNativeExperiment.run,
    handler_native setup checks wire length erased route representation created mlSource credential]

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (mlSource : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK mlSource) → Bool) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start setup mlSource ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial => event <$> (run setup checks wire erased route representation initial.created mlSource initial.credential
      bounds mode (adversary initial.public) initial.state)

/-- Actual extracted controller refinements occur in this theorem's dependency chain. The distribution equality covers the unchanged mandatory-ML native profile, original ledger, constructor outcomes and all later callbacks; no security conclusion or source-distribution equation is supplied as a premise. -/
theorem profile_native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array Std.U8 227#usize) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (mlSource : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK mlSource) → Bool) :
    profile setup checks wire erased route representation mlSource ensureInit identityIndex serverKeyId bounds mode adversary event =
      RegistrationNativeExperiment.profile setup checks wire route representation mlSource ensureInit identityIndex serverKeyId bounds mode adversary event := by
  simp only [profile, RegistrationNativeExperiment.profile,
    run_native setup checks wire length erased route representation]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeExtractedControllers

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.record_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.record_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.handler_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.handler_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.run_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.run_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.profile_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedControllers.profile_native
