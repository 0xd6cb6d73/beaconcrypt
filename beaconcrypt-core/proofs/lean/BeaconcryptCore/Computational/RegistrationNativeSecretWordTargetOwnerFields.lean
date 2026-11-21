-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCollect

/-! The ordered optional Beacon collector retains its original public header in every successful suffix, independently of all actual DH replies and their effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFields
open RegistrationNativeSecretWordBeaconPrefix (Header afterDecap)
open PqxdhPhase2GapDhSource (Inputs)
variable {I D K X Response : Type}

/-- All successful actual DH suffixes retain the same authenticated response, ciphertext, pin and converted first-DH operand. -/
theorem suffix (oneTime : D) (header : Header X Response) (shared : PqxdhBeaconPhase2Preparation.Word32)
    (plain : Inputs Response)
    (supported : some plain ∈ support (afterDecap (I := I) (K := K) oneTime header shared)) :
    plain.response = header.response ∧ plain.ciphertext = header.ciphertext ∧
      plain.server = header.server ∧ plain.serverConverted = header.serverConverted := by
  simp only [afterDecap, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨first, _first, supported⟩ := supported
  cases first with
  | none => cases supported
  | some first =>
      simp only [Option.elim_some] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨second, _second, supported⟩ := supported
      cases second with
      | none => cases supported
      | some second =>
          simp only [Option.elim_some] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨third, _third, supported⟩ := supported
          cases third with
          | none => cases supported
          | some third =>
              simp only [Option.elim_some] at supported
              rw [mem_support_bind_iff] at supported
              obtain ⟨fourth, _fourth, supported⟩ := supported
              cases fourth with
              | none => cases supported
              | some fourth =>
                  simp only [Option.elim_some] at supported
                  rw [mem_support_bind_iff] at supported
                  obtain ⟨assigned, _assigned, supported⟩ := supported
                  cases assigned with
                  | none => cases supported
                  | some assigned =>
                      simp only [Option.elim_some, mem_support_pure_iff] at supported
                      cases supported
                      exact ⟨rfl, rfl, rfl, rfl⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFields.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFields.suffix
