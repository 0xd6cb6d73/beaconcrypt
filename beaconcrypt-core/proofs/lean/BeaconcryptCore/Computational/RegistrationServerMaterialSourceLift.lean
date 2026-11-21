-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialServiceSource

/-! Closing the public one-use frontend over its private source material service respects the actual state-monad operations. These local laws retain the same frontend and current local World rather than copying a mutable environment into itself. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift
open RegistrationServerMaterialSourceState (State close service)
variable {n : Nat} {Value Next : Type}

private theorem close_run (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (work : StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n)) Value)
    (before : State n) :
    (close hkdf writer sign roots work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (service hkdf writer sign roots) (work.run before.1)).run before.2 := rfl

/-- Literal pure frontend outcomes preserve all current private state. -/
theorem pure_run (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (value : Value) (before : State n) :
    (close hkdf writer sign roots (pure value)).run before = pure (value, before) := by
  rw [close_run]
  simp only [StateT.run_pure, simulateQ_pure, StateT.run_pure, map_pure]

/-- Reading the public frontend does not read or change the private World or root map. -/
theorem get_run (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (before : State n) :
    (close hkdf writer sign roots get).run before = pure (before.1, before) := by
  rw [close_run]
  simp only [StateT.run_get, simulateQ_pure, StateT.run_pure, map_pure]

/-- Actual adaptive continuations receive the complete reached frontend and private World state. -/
theorem bind_run (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (first : StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n)) Value)
    (next : Value → StateT RegistrationServerMaterialFrontend.State (OracleComp (RegistrationServerMaterialFrontend.Spec n)) Next)
    (before : State n) :
    (close hkdf writer sign roots (first >>= next)).run before = (do
      let result ← (close hkdf writer sign roots first).run before
      (close hkdf writer sign roots (next result.1)).run result.2) := by
  simp only [close_run]
  simp only [StateT.run_bind, simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]

/-- A pure service component retains the public frontend until its actual returned result is settled. -/
theorem lift_run (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots)
    (work : OracleComp (RegistrationServerMaterialFrontend.Spec n) Value) (before : State n) :
    (close hkdf writer sign roots (StateT.lift work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$> (simulateQ (service hkdf writer sign roots) work).run before.2 := by
  rw [close_run]
  simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map, ]

end BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.pure_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.pure_run
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.get_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.get_run
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.bind_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.bind_run
/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.lift_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialSourceLift.lift_run
