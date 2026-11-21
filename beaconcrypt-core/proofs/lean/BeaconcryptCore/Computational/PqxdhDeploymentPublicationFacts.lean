-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublishedTuple
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports

/-! Selection facts for final published-bundle provenance across failed signing attempts. Constructor prekey and KEM fields are fixed by the existing actual-source invariant; a selected unpublished attempted tuple is therefore identified by its one-time message. These facts do not erase real signing requests or assume that writer failures are independent of signatures. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhRegistrationJointIssuedAttempts

/-- The immutable constructor fields make a one-time key determine the complete attempted tuple. -/
theorem fixed_tuple_eq (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (attempts : List Phase1KeyTuple) (fixed : Fixed prekey pqKey attempts)
    (first second : Phase1KeyTuple) (firstIn : first ∈ attempts) (secondIn : second ∈ attempts)
    (same : first.oneTime = second.oneTime) : first = second := by
  exact Phase1KeyTuple.ext' ((fixed first firstIn).1.trans (fixed second secondIn).1.symm)
    same ((fixed first firstIn).2.trans (fixed second secondIn).2.symm)

/-- A tuple differing from the final publication has a different one-time key, even after arbitrary failed attempts. -/
theorem unpublished_oneTime (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (attempts : List Phase1KeyTuple) (fixed : Fixed prekey pqKey attempts)
    (selected published : Phase1KeyTuple) (selectedIn : selected ∈ attempts)
    (publishedIn : published ∈ attempts) (publication : Option Phase1KeyTuple)
    (written : publication = some published) (unpublished : publication ≠ some selected) :
    published.oneTime ≠ selected.oneTime := by
  exact fun same => unpublished (written.trans (congrArg some
    (fixed_tuple_eq prekey pqKey attempts fixed published selected publishedIn selectedIn same)))

/-- Every repeated attempt containing the selected one-time message is the same complete unpublished tuple. -/
theorem matching_unpublished (prekey : X25519PublicKey) (pqKey : PqxdhKemIndCca.MlKem768PublicKey)
    (attempts : List Phase1KeyTuple) (fixed : Fixed prekey pqKey attempts)
    (selected repeated : Phase1KeyTuple) (selectedIn : selected ∈ attempts)
    (repeatedIn : repeated ∈ attempts) (publication : Option Phase1KeyTuple)
    (unpublished : publication ≠ some selected) (same : repeated.oneTime = selected.oneTime) :
    publication ≠ some repeated := by
  simpa only [fixed_tuple_eq prekey pqKey attempts fixed repeated selected repeatedIn selectedIn same]
    using unpublished

/-- The literal three-message source blocks uniquely determine the complete chronological attempt list, including repetitions. -/
theorem history_injective (first second : List Phase1KeyTuple)
    (same : history first = history second) : first = second := by
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons other tail => simp [history, messages] at same
  | cons keys rest ih =>
    cases second with
    | nil => simp [history, messages] at same
    | cons other tail =>
      simp only [history, messages, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at same
      exact congrArg₂ List.cons
        (Phase1KeyTuple.ext' (prekeyMessage_injective same.1)
          (oneTimeMessage_injective same.2.1) (pqMessage_injective same.2.2.1))
        (ih tail same.2.2.2)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.fixed_tuple_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.fixed_tuple_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.unpublished_oneTime' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.unpublished_oneTime

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.matching_unpublished' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.matching_unpublished

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.history_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationFacts.history_injective
