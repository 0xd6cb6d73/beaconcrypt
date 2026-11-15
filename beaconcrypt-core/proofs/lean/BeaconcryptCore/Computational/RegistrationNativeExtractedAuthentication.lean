-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse

/-! The unchanged mandatory-ML native experiment is interpreted with the actual extracted response-authentication body in every finish operation. The local definition exposes the existing frontend's context around that call and is proved exactly equal to it. Constructor outcomes, terminal consumption, authentication failures, root/record continuation, installation, shared primitive state and later callbacks remain in the same execution. Concrete packet codecs, public Rust wrapper correspondence and primitive implementation/security contracts remain separate boundaries. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface
open RegistrationNativeWire (Wire)
open RegistrationNativeBeaconFrontend
open BeaconcryptCore.Refinement
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

/-- The extracted authentication program occupies the original native finish context, including terminal movement before packet admission. -/
noncomputable def finish (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK mldsaSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => match owner.phase with
    | .initSent pending oneTime => do
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
        updatePhase index (.aborted aborted)
        let authenticated ← simulateQ (authentication setup mldsaSource)
          (AdapterAuthenticationStatefulResponse.authenticate pending (match packet with | none => core.option.Option.None | some value => core.option.Option.Some value))
        match authenticated with
        | .fail error => abort owner *> pure (.fail error)
        | .div => abort owner *> pure .div
        | .ok (.Err _) => abort owner *> pure (.ok none)
        | .ok (.Ok accepted) => do
          let agreed ← simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
          match agreed with
          | .fail error => abort owner *> pure (.fail error)
          | .div => abort owner *> pure .div
          | .ok (.BeaconComplete completed) => do
            let opened ← simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
            match opened with
            | .fail error => abort owner *> pure (.fail error)
            | .div => abort owner *> pure .div
            | .ok (.Err _) => abort owner *> pure (.ok none)
            | .ok (.Ok established) => do
              let shell : BeaconShell := ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
              let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known established.kernel)))
              if installed then
                updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
                pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
              else abort owner *> pure (.ok none)
          | .ok _ => abort owner *> pure (.ok none)
    | _ => pure (.ok none)

theorem authentication_source (pending : registration.BeaconPending)
    (packet : Option registration.ResponsePacket) :
    AdapterAuthenticationStatefulResponse.authenticate pending packet =
      RegistrationResponseExecutor.begin pending packet :=
  (AdapterAuthenticationStatefulResponse.source_certificate pending packet).2

/-- The source-interpreted finish equals the original native function on all states and optional packets. -/
theorem finish_native (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    finish (n := n) (Auxiliary := Auxiliary) setup mlSource wire index packet =
      RegistrationNativeBeaconFrontend.finish setup mlSource wire index packet := by
  simp only [finish, RegistrationNativeBeaconFrontend.finish, authentication_source]
  rfl

/-- Only the selected authentication body is expanded; every other native command is the unchanged original callback. -/
noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.M n KemSK mlSource)
  | .inr (.finish index packet) => RegistrationNativeExperiment.beacon setup checks representation created
      (finish setup mlSource wire index packet)
  | query => RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query

/-- The exact callback equality includes its entire original native poststate and all shared primitive histories. -/
theorem handler_native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource) :
    handler (n := n) setup checks wire route representation created mlSource credential =
      RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential := by
  funext query
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> simp only [handler, finish_native, RegistrationNativeExperiment.handler] <;> rfl

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :=
  RegistrationNativeFullCompiler.run setup.source.crypto wire created.server.server.metadata.sender bounds
    (handler setup checks wire route representation created mlSource credential) mode work before

/-- Every adaptive native run preserves the joint original ledger, returned value, owner state and complete shared primitive state. -/
theorem run_native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (mlSource : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    run setup checks wire route representation created mlSource credential bounds mode work before =
      RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before := by
  simp only [run, RegistrationNativeExperiment.run, handler_native]

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (mlSource : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK mlSource) → Bool) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start setup mlSource ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial => event <$> (run setup checks wire route representation initial.created mlSource initial.credential
      bounds mode (adversary initial.public) initial.state)

/-- The original native profile is exactly the source-authentication interpretation for every observable event. No distributional or wrapper correspondence is supplied as a premise. -/
theorem profile_native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (mlSource : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK mlSource) → Bool) :
    profile setup checks wire route representation mlSource ensureInit identityIndex serverKeyId bounds mode adversary event =
      RegistrationNativeExperiment.profile setup checks wire route representation mlSource ensureInit identityIndex serverKeyId bounds mode adversary event := by
  simp only [profile, RegistrationNativeExperiment.profile, run_native]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.authentication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.authentication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.finish_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.handler_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.handler_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.run_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.run_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.profile_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeExtractedAuthentication.profile_native
