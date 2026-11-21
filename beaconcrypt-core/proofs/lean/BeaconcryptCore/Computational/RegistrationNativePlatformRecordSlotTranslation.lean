-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation
open RegistrationNativePlatformPublicRecordSlots (State handler program)
open RegistrationNativeG3MaterializedLocal (translate)
variable {n : Nat} {KemSK A : Type}

/-- Realizing an installation reference retains the original raw-demand receipt. The observer remains below the material-reply transformation. -/
theorem query (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (request : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (ghost : State n) :
    (simulateQ handler (translate false seeds request)).run ghost =
      simulateQ (translate false seeds) ((handler request).run ghost) := by
  rcases request with (prepare | (demand | (publication | environment)) | kem) | record
  all_goals try rfl
  rcases environment with coin | capability
  · rfl
  · cases capability with
    | installServer keyId binding reference => cases reference <;> rfl
    | installBeacon owner shell reference => cases reference <;> rfl
    | _ => rfl

/-- Arbitrary adaptive source work keeps its raw material-slot snapshot when only hidden installation references are realized. -/
theorem program (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A) (ghost : State n) :
    RegistrationNativePlatformPublicRecordSlots.program (simulateQ (translate false seeds) work) ghost =
      simulateQ (translate false seeds) (RegistrationNativePlatformPublicRecordSlots.program work ghost) := by
  induction work using OracleComp.inductionOn generalizing ghost with
  | pure value => rfl
  | query_bind request next ih =>
    simp only [RegistrationNativePlatformPublicRecordSlots.program,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [query]
    apply bind_congr
    intro result
    exact ih result.1 result.2
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotTranslation.program
