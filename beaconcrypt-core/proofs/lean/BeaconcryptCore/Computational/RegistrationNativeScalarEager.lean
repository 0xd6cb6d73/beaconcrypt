-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSampling

/-! The source-only early-scalar experiment keeps the actual pure pin selection, identity and counted prekey draws. Only a successful selected roster birth substitutes the supplied private scalar before the literal indexed KEM/public-owner suffix. The original raw and secrecy compilers are unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarEager
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (scalar : ScalarBytes) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Nat)) := do
  match ← RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId with
  | .ok (some prepared) =>
      let owners ← get
      let prekey := if owners.length = selected then scalar else prepared.prekey
      RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin prepared.identity prekey
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : ScalarBytes) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.M n KemSK source)
  | .inr (.create edPin mlPin keyId) => RegistrationNativeExperiment.beacon setup checks representation created
      (create setup source selected scalar edPin mlPin keyId)
  | query => RegistrationNativeExperiment.handler setup checks wire route representation created source credential query

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : ScalarBytes) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :=
  RegistrationNativeFullCompiler.run setup.source.crypto wire created.server.server.metadata.sender bounds
    (handler setup checks wire route representation created source credential selected scalar) mode work before

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (selected : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) : ProbComp Bool := do
  let scalar ← PqxdhJointGapDh.sampleScalar
  let initialized ← RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial => event <$> (run setup checks wire route representation initial.created source initial.credential
      selected scalar bounds mode (adversary initial.public) initial.state)

end BeaconcryptCore.Computational.RegistrationNativeScalarEager
