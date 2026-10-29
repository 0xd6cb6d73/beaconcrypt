-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBackend
import BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-! Actual native agreement getters cannot create a KEM owner or reveal a stored KEM secret. Those operations belong only to explicit owner creation or disclosure interfaces, so native Server/Beacon primitive continuations derive the zero-reveal condition used by the private indexed source. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBudget
open RegistrationAgreementShared (PrimitiveSpec PrimitiveRequest)
open RegistrationNativeKemInterface (Spec OtherSpec)
open RegistrationNativeKemPoolSource (IsReveal)
variable {KemSK Result : Type}

/-- No actual Server primitive getter can reveal a KEM secret, on any optional or key-check branch. -/
theorem server_step (checks : PqxdhServerAuthExperiment.Checks) (query : PrimitiveRequest) :
    (RegistrationNativeKemInterface.server (KemSK := KemSK) checks query).IsQueryBoundP (IsReveal (ambient := OtherSpec) (KemSK := KemSK)) 0 := by
  cases query with
  | convertPublic key | convertSecret key | generate key | dh key =>
      simp [RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other, IsReveal,
        isQueryBoundP_query_iff]
  | decapsulate ciphertext => simp [RegistrationNativeKemInterface.server]
  | encapsulate key =>
      cases key with
      | none => simp [RegistrationNativeKemInterface.server]
      | some key =>
        simp only [RegistrationNativeKemInterface.server]
        split <;> simp [RegistrationNativeKemInterface.encapsulate, IsReveal, isQueryBoundP_query_iff]

/-- Arbitrary adaptive native Server primitive work derives the zero private-reveal certificate. -/
theorem server_program (checks : PqxdhServerAuthExperiment.Checks) (work : OracleComp PrimitiveSpec Result) :
    (simulateQ (RegistrationNativeKemInterface.server (KemSK := KemSK) checks) work).IsQueryBoundP (IsReveal (ambient := OtherSpec) (KemSK := KemSK)) 0 := by
  exact OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim) (fun query _ => server_step checks query)

/-- A Beacon uses its opaque owner index only for actual ciphertext decapsulation, never for private-key access. -/
theorem beacon_step (handle : Option Nat) (query : PrimitiveRequest) :
    (RegistrationNativeKemInterface.beacon (KemSK := KemSK) handle query).IsQueryBoundP (IsReveal (ambient := OtherSpec) (KemSK := KemSK)) 0 := by
  cases query with
  | convertPublic key | convertSecret key | generate key | dh key =>
      simp [RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, IsReveal,
        isQueryBoundP_query_iff]
  | encapsulate key => simp [RegistrationNativeKemInterface.beacon]
  | decapsulate ciphertext =>
      cases ciphertext <;> cases handle <;>
        simp [RegistrationNativeKemInterface.beacon, IsReveal, isQueryBoundP_query_iff]

/-- The complete adaptive Beacon primitive program has no selected or other KEM secret-reveal query. -/
theorem beacon_program (handle : Option Nat) (work : OracleComp PrimitiveSpec Result) :
    (simulateQ (RegistrationNativeKemInterface.beacon (KemSK := KemSK) handle) work).IsQueryBoundP (IsReveal (ambient := OtherSpec) (KemSK := KemSK)) 0 := by
  exact OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim) (fun query _ => beacon_step handle query)

end BeaconcryptCore.Computational.RegistrationNativeKemBudget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBudget.server_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBudget.server_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBudget.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBudget.server_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBudget.beacon_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBudget.beacon_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBudget.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBudget.beacon_program
