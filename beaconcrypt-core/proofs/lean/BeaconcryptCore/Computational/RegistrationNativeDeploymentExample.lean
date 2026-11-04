-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeQuantitativeSecurity

/-! Exact rational arithmetic for the worked deployment example. These are guessing coefficients only; the event-specific cryptographic and selector losses in `app_min` remain separate summands. -/
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeDeploymentExample

theorem target_count : (2^20 : Nat) * 2^20 = 2^40 := by norm_num

theorem old_guessing : (2^20 : ℚ) * 2^20 * (256^16 : ℚ)⁻¹ = (2^88 : ℚ)⁻¹ := by
  norm_num

theorem single_guessing : (256^16 : ℚ)⁻¹ = (2^128 : ℚ)⁻¹ := by norm_num

theorem coefficient_ratio : (2^88 : ℚ)⁻¹ = 2^40 * (2^128 : ℚ)⁻¹ := by norm_num

end BeaconcryptCore.Computational.RegistrationNativeDeploymentExample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.target_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.target_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.old_guessing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.old_guessing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.single_guessing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.single_guessing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.coefficient_ratio' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDeploymentExample.coefficient_ratio
