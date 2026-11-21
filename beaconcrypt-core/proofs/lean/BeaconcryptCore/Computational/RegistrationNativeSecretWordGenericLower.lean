-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution

/-! The finite local-state lowering supports an arbitrary private observer state. This permits the actual chronological trace and original private interpreter to be threaded together without erasing a selected callback cut. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Private Value Next : Type}

abbrev Auxiliary (Private : Type) := Environment × Private

def lower (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) : StateT (Auxiliary Private) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation (work.run before.1)).run before.2

theorem lower_run (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value) (before : Auxiliary Private) :
    (lower implementation work).run before = (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ implementation (work.run before.1)).run before.2 := rfl

/-- Lowering preserves each actual reached public environment and private observer state through every continuation. -/
theorem lower_bind (implementation : QueryImpl (LocalSpec n KemSK) (StateT Private ProbComp))
    (work : StateT Environment (OracleComp (LocalSpec n KemSK)) Value)
    (next : Value → StateT Environment (OracleComp (LocalSpec n KemSK)) Next) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]
end BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower.lower_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower.lower_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower.lower_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower.lower_run
