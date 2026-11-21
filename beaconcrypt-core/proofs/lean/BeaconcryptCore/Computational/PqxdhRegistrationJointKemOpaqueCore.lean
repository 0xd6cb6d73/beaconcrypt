-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueSuffix

/-! The actual extracted acceptance branch and every cleared pending-token field are independent of the selected KEM bytes. The bytes are required only inside the private root-input interpreter. This is a functional source equation, not a secrecy claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore
open PqxdhServerRootPreparation PqxdhRegistrationJointKemOpaqueSuffix
open PqxdhBeaconPhase2Preparation (Word32)
variable {Reader E : Type}

/-- Erase only the temporary root-input bytes in the actual extracted acceptance result. All errors, public token fields and the complete source control state are retained. -/
def clearedAccept (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E Word32) :
    RustM (core.result.Result (pqxdh.ServerState × pqxdh.PendingServerRegistration) pqxdh.RegistrationError) :=
  match PqxdhServerRelatedRootInput.accept control binding input with
  | .ok (.Ok (state, pending)) => .ok (.Ok (state, PqxdhServerClearedRoot.cleared pending))
  | .ok (.Err error) => .ok (.Err error)
  | .fail error => .fail error
  | .div => .div

/-- Literal extracted acceptance only tests the four DH values. After its temporary input is erased, its complete result is independent of the KEM value. -/
theorem cleared_shape (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E Word32) :
    clearedAccept control binding input =
      if Pqxdh.dhNonZero (absBytes input.first, absBytes input.second,
        absBytes input.third, absBytes input.fourth) then
        ok (.Ok (control, PqxdhServerClearedRoot.pending binding input))
      else ok (.Err pqxdh.RegistrationError.InvalidDhOutput) := by
  classical
  by_cases valid : Pqxdh.dhNonZero (absBytes input.first, absBytes input.second,
    absBytes input.third, absBytes input.fourth)
  · obtain ⟨root, built, _⟩ := (build_root_key_input_abs (PqxdhServerRelatedRootInput.secrets input)).1 valid
    have rid := PqxdhServerClearedRoot.registrationId_source input.verified
    simp only [clearedAccept, PqxdhServerRelatedRootInput.accept, pqxdh.server_accept,
      pqxdh.validate_registration_status, built, rid, valid, ite_true,
      PqxdhServerClearedRoot.cleared, PqxdhServerClearedRoot.pending]
    rfl
  · have rejected := (build_root_key_input_abs (PqxdhServerRelatedRootInput.secrets input)).2 valid
    simp only [clearedAccept, PqxdhServerRelatedRootInput.accept, pqxdh.server_accept,
      pqxdh.validate_registration_status, rejected, valid, ite_false]
    rfl

/-- The entire cleared source acceptance result is unchanged for any replacement KEM word, including invalid-DH rejection. -/
theorem cleared_replace (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Inputs Reader E Word32) (value : Word32) :
    clearedAccept control binding (replaceKem value input) = clearedAccept control binding input := by
  rw [cleared_shape, cleared_shape]
  rfl

/-- The marker representation computes the literal branch using its erased dummy; it neither tests nor returns the selected bytes. -/
def accept (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Prepared Reader E Word32) :=
  clearedAccept control binding (materialize (List.Vector.replicate 32 0) input)

/-- Materialization recovers the exact extracted acceptance and every cleared result field, for all markers and candidates. -/
theorem accept_native (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Prepared Reader E Word32) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    accept control binding input = clearedAccept control binding (materialize candidate input) := by
  simp only [accept, cleared_shape, materialize, PqxdhServerClearedRoot.pending]

/-- On the actual accepted branch there is an original un-cleared token whose complete source result and cleared projection are fixed. -/
theorem accepted_original (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : Prepared Reader E Word32) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (final : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (accepted : accept control binding input = ok (.Ok (final, pending))) :
    ∃ original, PqxdhServerRelatedRootInput.accept control binding (materialize candidate input) =
      ok (.Ok (final, original)) ∧ PqxdhServerClearedRoot.cleared original = pending := by
  rw [accept_native, clearedAccept] at accepted
  split at accepted <;> simp only [RustM.ok.injEq, core.result.Result.Ok.injEq,
    Prod.mk.injEq, reduceCtorEq] at accepted
  obtain ⟨rfl, rfl⟩ := accepted
  exact ⟨_, ‹_›, rfl⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.cleared_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.cleared_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.cleared_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.cleared_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.accept_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.accepted_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueCore.accepted_original
