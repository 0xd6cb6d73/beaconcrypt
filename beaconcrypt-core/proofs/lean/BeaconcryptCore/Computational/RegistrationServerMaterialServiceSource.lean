-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialSourceState

/-! A real private material lookup evaluates the native key schedule at its retained root; the public Server continuation receives only its ordinary service choice. The local source theorem below is independent of replay/preflight admission, which the outer native frontend derives before reaching this service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerMaterialSourceState (service)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

/-- The actual private known-root service preserves every common publication and installation query. -/
theorem common_program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    simulateQ (service hkdf writer sign roots) (simulateQ RegistrationNativePairedServerService.publicCommon work) =
      simulateQ (RegistrationServerKnownStageWorldSource.common (Auxiliary := RegistrationServerRoleBackend.State) hkdf writer sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreter => simulateQ interpreter work)
  funext query
  simp only [QueryImpl.apply_compose, RegistrationNativePairedServerService.publicCommon,
    simulateQ_spec_query, service]

/-- A reached real material lookup returns exactly fromRoot108 at the private retained descriptor and resumes the actual native known continuation. -/
theorem admitted (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    simulateQ (service (n := n) hkdf writer sign roots)
        (RegistrationNativePairedServerService.publicAdmitted encode control initial message) =
      simulateQ (RegistrationServerKnownStageWorldSource.common hkdf writer sign)
        (RegistrationNativePairedServerService.knownStage encode control initial
          (PqxdhServerAuthKeySchedule.fromRoot hkdf (roots message))) := by
  simp only [RegistrationNativePairedServerService.publicAdmitted, simulateQ_bind,
    simulateQ_spec_query, service, pure_bind, RegistrationNativePairedServerService.publicBranch]
  exact common_program hkdf writer sign roots _

/-- Under the actual source pending-role receipt, the reached service has precisely the full SDK fromInitial source distribution. -/
theorem native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) (message : RegistrationNativeRelatedFamily.Message)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray (roots message))) (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id RegistrationServerRecordWorldSource.project <$>
      (simulateQ (service setup.source codec.frameWrite sign roots)
        (RegistrationNativePairedServerService.publicAdmitted encode control
          (RegistrationBoundKeySchedule.publicInitial initial) message)).run before =
      Prod.map id RegistrationServerRecordWorldSource.project <$>
        (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial).run before := by
  rw [admitted]
  exact RegistrationServerKnownStageWorldSource.native setup codec sign encode control initial (roots message) role before

end BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource.common_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource.common_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource.native
