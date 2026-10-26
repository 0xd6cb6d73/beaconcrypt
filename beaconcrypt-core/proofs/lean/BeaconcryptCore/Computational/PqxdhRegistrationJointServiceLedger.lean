-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts

/-! Source-attempt caps compose into explicit global counts of every emitted private/native service class, on all typed replies of the actual executable client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhRegistrationJointServiceSchedule PqxdhRegistrationJointServiceCosts
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Routing private service programs preserves each exact private class and adds no native-tail or Server/public operation. -/
theorem pool_queries (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (kind : Kind) (budget : Nat) :
    (simulateQ (poolLift (Response := Response)) program).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) budget ↔
      program.IsQueryBoundP (fun query => poolClass (KemSK := KemSK) query = kind) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, poolLift, isQueryBoundP_query_bind_iff, ih]
      rfl

/-- The existing finish ledger groups only unrelated capabilities; the global partition keeps them distinct. -/
def finishClass : Kind → PqxdhRegistrationJointFinishCompiler.Kind
  | .tail => none
  | .decapsulate => some .decapsulate
  | .staticDh => some .staticDh
  | _ => some .localCall

/-- Reclassification of a literal finish backend request matches its existing component class exactly. -/
theorem finish_partition (query : (PqxdhRegistrationJointFinishCompiler.Spec KemSK Response).Domain) :
    PqxdhRegistrationJointFinishCompiler.classify (KemSK := KemSK) query =
      finishClass (classify (KemSK := KemSK) (.inl query)) := by
  rcases query with query | query
  · rcases query with (coin | request) | (coin | request) <;> try rfl
    all_goals cases request <;> try rfl
    rename_i index operation
    cases operation <;> rfl
  · rfl

/-- Routing a finish program preserves its exact global-class count, with no Server/public macro request. -/
theorem finish_queries (program : OracleComp (PqxdhRegistrationJointFinishCompiler.Spec KemSK Response) Result)
    (kind : Kind) (budget : Nat) :
    (simulateQ finishLift program).IsQueryBoundP (fun query => classify (KemSK := KemSK) query = kind) budget ↔
      program.IsQueryBoundP (fun query => classify (KemSK := KemSK) (.inl query) = kind) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, finishLift, isQueryBoundP_query_bind_iff, ih]
      rfl

/-- Every compiled whole-owner finish has at most one logical decapsulation, at most one joint DH, at most 56 native-tail calls and zero requests in all remaining global classes. -/
theorem finish_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationJointBundle.Owner) (kind : Kind) :
    (simulateQ finishLift (simulateQ (PqxdhRegistrationJointFinishCompiler.compiler setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner))).IsQueryBoundP
        (fun query => classify (KemSK := KemSK) query = kind) (finishCap kind) := by
  rw [finish_queries]
  apply IsQueryBoundP.of_imp (p' := fun query =>
    PqxdhRegistrationJointFinishCompiler.classify (KemSK := KemSK) query = finishClass kind)
  · exact fun query same => (finish_partition query).trans (congrArg finishClass same)
  · simpa only [show PqxdhRegistrationJointFinishCompiler.cap (finishClass kind) = finishCap kind by
      cases kind <;> rfl] using
      PqxdhRegistrationJointCompiledOwner.owner_queries setup codec raw owner (finishClass kind)

/-- The executable constructor's owner installation adds no service request to its exact creation ledger. -/
theorem create_bound (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((create (KemSK := KemSK) (Response := Response) pin keyId).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (createCap kind) := by
  simpa only [StateT.run, create, bind_pure_comp, isQueryBoundP_map_iff, pool_queries] using
    creation_queries (KemSK := KemSK) kind

/-- Missing owners, inactive phases and optional writer outcomes keep the same per-attempt bundle ledger. -/
theorem bundle_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((bundle setup codec address).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (bundleCap kind) := by
  cases found : owners[address]? with
  | none => simp only [StateT.run, bundle, found, isQueryBoundP_pure]
  | some entry =>
      simpa only [StateT.run, bundle, found, isQueryBoundP_map_iff, pool_queries] using
        bundle_queries setup codec entry.2.2 kind

/-- Full owner lookup and reinstallation add no backend call to the complete finish attempt, on success or failure. -/
theorem finish_owner_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((finish setup codec address raw).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (finishCap kind) := by
  cases found : owners[address]? with
  | none => simp only [StateT.run, finish, found, isQueryBoundP_pure]
  | some entry =>
      simpa only [StateT.run, finish, found, isQueryBoundP_map_iff] using
        finish_bound setup codec raw entry.2.2 kind

/-- The sparse source-to-service matrix bounds every public handler on every owner registry and every typed reply, without ownership or success premises. -/
theorem query_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : PqxdhRegistrationSchedule.Spec.Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((handler setup codec query).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (cost kind (PqxdhRegistrationSchedule.sourceKind query)) := by
  rcases query with coin | request
  case inl =>
    simp +contextual [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff, classify, poolClass, cost, PqxdhRegistrationSchedule.sourceKind, eq_comm]
  case inr =>
    cases request <;> first
    | exact create_bound _ _ owners kind
    | exact bundle_bound setup codec _ owners kind
    | exact finish_owner_bound setup codec _ _ owners kind
    | skip
    all_goals simp +contextual [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff, classify, cost, PqxdhRegistrationSchedule.sourceKind, eq_comm]

/-- Closed-form global service allowances in terms of the nine original source-attempt caps. -/
def total (budget : Fin 9 → Nat) : Kind → Nat
  | .identityCreate | .kemCreate => budget 1
  | .signing => 3 * budget 2
  | .staticDh | .decapsulate => budget 5
  | .uniform => budget 0 + 32 * budget 1 + 32 * budget 2
  | .tail => 56 * budget 5
  | .accept => budget 3
  | .build => budget 4
  | .hmac => budget 6
  | .hash => budget 7
  | .read => budget 8
  | .other => 0

/-- The sparse source-to-service matrix has exactly the displayed closed-form allowances; no source class is omitted from the sum. -/
theorem cost_total (budget : Fin 9 → Nat) (kind : Kind) :
    (∑ source, cost kind source * budget source) = total budget kind := by
  cases kind <;> simp [cost, total, Fin.sum_univ_succ, createCap, bundleCap, finishCap, Nat.add_assoc]

/-- All source attempts compose into the explicit global service ledger for the complete adaptive client, including failed calls and arbitrary typed replies. -/
theorem program_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp PqxdhRegistrationSchedule.Spec Result) (budget : Fin 9 → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationSchedule.sourceKind query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (kind : Kind) :
    ((simulateQ (handler setup codec) program).run owners).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (total budget kind) := by
  rw [← cost_total budget kind]
  exact FinitePartitionQueryBounds.weighted_bound PqxdhRegistrationSchedule.sourceKind
    (cost kind) budget (handler setup codec) (fun query => classify (KemSK := KemSK) query = kind)
    program certified (fun query before => query_bound setup codec query before kind) owners

end BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.pool_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.pool_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_partition

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.create_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.bundle_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.finish_owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.cost_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.cost_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServiceLedger.program_bound
