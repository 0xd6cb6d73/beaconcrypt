-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementTermination
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Finite source-loop fuel and the original nine-step agreement driver have exactly the same oracle program whenever their finite source rank is covered. Terminal repetitions issue no query. No output, acceptance or probabilistic identification is assumed. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
open RegistrationAgreementExecutor

theorem zero_terminal (phase : agreement.AgreementEffect) (zero : rank phase = 0) : Terminal phase := by
  cases phase with
  | Rejected aborted => exact .rejected aborted
  | ServerComplete completed => exact .server completed
  | BeaconComplete completed => exact .beacon completed
  | GenerateEphemeral pending => simp [rank] at zero
  | Encapsulate pending => simp [rank] at zero
  | ConvertPublic pending => simp [rank] at zero
  | ConvertSecret pending => simp [rank] at zero
  | Decapsulate pending => simp [rank] at zero
  | RootKdf pending => simp [rank] at zero
  | Dh pending => cases position : pending.position <;> simp [rank, position] at zero

theorem terminal_drive (phase : agreement.AgreementEffect) (terminal : Terminal phase) (fuel : Nat) :
    drive fuel phase = pure (.ok phase) := by
  cases terminal <;> induction fuel <;> simp_all only [drive, step, continueWith, pure_bind]

theorem drive_stable (fuel extra : Nat) (phase : agreement.AgreementEffect) (enough : rank phase ≤ fuel) :
    drive (fuel + extra) phase = drive fuel phase := by
  induction fuel generalizing phase with
  | zero =>
    have terminal := zero_terminal phase (Nat.eq_zero_of_le_zero enough)
    rw [terminal_drive phase terminal, terminal_drive phase terminal]
  | succ fuel ih =>
    simp only [Nat.succ_add, drive]
    apply OracleComp.bind_congr_of_forall_mem_support (step phase)
    intro result supported
    cases result with
    | fail error | div => rfl
    | ok next =>
      apply ih next
      rcases step_progress (step_sound phase next supported) with decreased | ⟨_, zero⟩
      · omega
      · omega

def loop : Nat → agreement.AgreementEffect → OracleComp Spec (RustM agreement.AgreementEffect)
  | 0, _ => pure .div
  | fuel + 1, phase =>
      if rank phase = 0 then pure (.ok phase)
      else do
        let next ← step phase
        continueWith next (loop fuel)

theorem loop_enough (fuel : Nat) (phase : agreement.AgreementEffect) (enough : rank phase < fuel) :
    loop fuel phase = drive (fuel - 1) phase := by
  induction fuel generalizing phase with
  | zero => omega
  | succ fuel ih =>
    by_cases terminal : rank phase = 0
    · rw [loop, ite_eq_left terminal, terminal_drive phase (zero_terminal phase terminal)]
    · cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [loop, ite_eq_right terminal, Nat.add_sub_cancel, drive]
        apply OracleComp.bind_congr_of_forall_mem_support (step phase)
        intro result supported
        cases result with
        | fail error | div => rfl
        | ok next =>
          change loop (fuel + 1) next = drive fuel next
          apply ih next
          rcases step_progress (step_sound phase next supported) with decreased | ⟨zero, _⟩
          · omega
          · exact False.elim (terminal zero)

theorem nine (phase : agreement.AgreementEffect) (bounded : rank phase ≤ 9) :
    loop (rank phase + 1) phase = drive 9 phase := by
  rw [loop_enough _ phase (Nat.lt_succ_self _), Nat.succ_sub_one]
  have stable := drive_stable (rank phase) (9 - rank phase) phase (Nat.le_refl _)
  rw [Nat.add_sub_of_le bounded] at stable
  exact stable.symm
end BeaconcryptCore.Computational.RegistrationAgreementSourceFuel

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.zero_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.zero_terminal

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.terminal_drive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.terminal_drive

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.drive_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.drive_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.loop_enough' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.loop_enough

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.nine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceFuel.nine
