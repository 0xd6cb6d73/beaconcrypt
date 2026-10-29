-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase

/-! The actual public build retains its record-request marker list through lookup, cancellation, complete sizing, material demand, signing and peer installation. Signing receipts remain the caller's real current-environment chronology. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceBuildRequests
variable {n : Nat} {KemSK : Type}

/-- Every actual open Server build outcome retains the existing environment record markers. -/
theorem build_keeps (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment)
    (result : (RegistrationServerMaterialFrontend.Result × RegistrationServerMaterialFrontend.State) × RegistrationServerReferenceCompiler.Environment)
    (supported : result ∈ support (((RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK)
      hkdf wire checks sign handle application).run before).run env)) :
    result.2.recordRequests = env.recordRequests := by
  exact RegistrationServerReferenceRequestBase.service_program RegistrationBeaconReferenceCompiler.effect
    RegistrationServerOpenReferenceCompiler.demand hkdf wire.frameWrite sign
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before) env result supported

end BeaconcryptCore.Computational.RegistrationServerReferenceBuildRequests
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceBuildRequests.build_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceBuildRequests.build_keeps
