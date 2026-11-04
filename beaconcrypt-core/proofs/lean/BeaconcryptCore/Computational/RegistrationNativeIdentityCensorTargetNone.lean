-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync
/-! Private source selection can install a target but can never reset it to none; this is an operational invariant for the actual canonical interpreter. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetNone
open RegistrationNativeIdentityCensorSource (State implementation)
open RegistrationNativeIdentityCensorOperational (Spec)
variable {A : Type}

/-- A callback with no target afterward also had no target before it. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (request : Spec.Domain)
    (before : State) (result : Spec.Range request × State)
    (supported : result ∈ support ((implementation joint selected request).run before))
    (missing : result.2.target=none) : before.target=none := by
  rw [RegistrationNativeIdentityCensorTargetSync.source_step joint selected request before result supported] at missing
  rcases request with (((protocol|message)|scanned)|hash)|marker
  · exact missing
  · cases chosen : result.1 <;> simp_all [RegistrationNativeIdentityCensorTargetSync.targetAfter]
  · exact missing
  · exact missing
  · exact missing

/-- Every complete original source program preserves the fact that an installed target cannot disappear. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (work : OracleComp Spec A)
    (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ (implementation joint selected) work).run before))
    (missing : result.2.target=none) : before.target=none := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact missing
  | query_bind request next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      exact query joint selected request before middle called (ih middle.1 middle.2 result continued missing)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetNone

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetNone.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetNone.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetNone.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetNone.program
