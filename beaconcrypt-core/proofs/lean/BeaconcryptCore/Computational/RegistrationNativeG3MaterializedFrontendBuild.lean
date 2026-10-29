-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendSource
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendServer

/-! Actual open Server build materialization retains the complete mutable environment, independent key-service state and full receipt/World state. The compiler is interpreted against the current environment at every callback; its concrete service laws derive the shared representation before the already proved complete build coupling is applied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild
open beaconcrypt_core
open RegistrationNativeG3MaterializedFrontend (ServiceSpec)
open RegistrationNativeG3MaterializedFrontendInterface (Private Local interface lower put)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK KeyState : Type}

/-- The actual compiler consumes and returns its complete current environment on every success and failure branch. -/
theorem compiler_source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8))
    (control : RegistrationServerMaterialFrontend.State) (before : Local n RegistrationServerRoleBackend.State KeyState) :
    (lower (interface full seeds service fallback)
      ((RegistrationServerOpenReferenceCompiler.build hkdf wire checks sign handle application).run control)).run before =
      (fun result => (result.1, put before result.2)) <$>
        (simulateQ (RegistrationNativeG3MaterializedFrontendSource.target full hkdf wire.frameWrite sign seeds service)
          ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run control)).run
            (RegistrationNativeG3MaterializedFrontendInterface.get before) := by
  change (lower (interface full seeds service fallback)
    (simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      RegistrationServerOpenReferenceCompiler.demand hkdf wire.frameWrite sign)
      ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run control))).run before = _
  rw [RegistrationNativeG3MaterializedFrontendInterface.lower_program]
  exact RegistrationNativeG3MaterializedFrontendSource.program full seeds service fallback hkdf wire.frameWrite sign _ before

/-- Actual Server build has identical full outcomes with materialized hidden seeds, without a cache or unused-role premise. -/
theorem build_source (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8))
    (control : RegistrationServerMaterialFrontend.State) (before : Local n RegistrationServerRoleBackend.State KeyState) :
    (lower (interface true seeds service fallback)
      ((RegistrationServerOpenReferenceCompiler.build hkdf wire checks sign handle application).run control)).run before =
      (lower (interface false seeds service fallback)
        ((RegistrationServerOpenReferenceCompiler.build hkdf wire checks sign handle application).run control)).run before := by
  rw [compiler_source, compiler_source]
  exact congrArg (fun distribution => (fun result => (result.1, put before result.2)) <$> distribution)
    (RegistrationNativeG3MaterializedFrontendServer.build_source hkdf wire sign seeds service checks.reservePeer
      handle application control (RegistrationNativeG3MaterializedFrontendInterface.get before))

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild.compiler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild.compiler_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild.build_source
