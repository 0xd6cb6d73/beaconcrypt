-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreatePublic

/-! The original public create allowance bounds actual private symbolic births through the complete raw ledger. All other operations, including internal secrecy sends and failed registration attempts, have zero private births. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordFrontend (handler run)
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Every adaptive typed program preserves its public constructor allowance through the actual symbolic frontend. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) count)
    (before : State source) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using
      RegistrationNativeSecretWordTargetNoCreatePublic.handler_bound (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query current
  · intro query free current
    simpa only [ite_eq_right free] using
      RegistrationNativeSecretWordTargetNoCreatePublic.handler_bound (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query current

/-- The full original mode-dependent native game makes at most its original public create budget in actual private births. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) budget.create :=
  program_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey _ budget.create
    (RegistrationNativeKemFullFootprint.compile_creates setup.source.crypto wire serverKeyId bounds mode work budget bounded) before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCreateBounds.run_bound
