-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenCosts

/-! The complete initialized open program retains origin-sensitive creation, actual private service caps, initialization/import attempts and every local evaluated cost. These counts are operational certificates, not freshness or security assumptions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
open PqxdhRegistrationJointOpenInitialization (Spec poolLift)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Runtime initialization and supplied-seed import are local constructor calls, distinct from every generated private-service capability. -/
def classify : (Spec KemSK).Domain → Option Kind
  | .inl query => some (poolClass (KemSK := KemSK) query)
  | .inr _ => none

/-- Forwarding existing service requests through the initialized interface preserves every exact selective query certificate. -/
theorem lifted_queries (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (kind : Kind) (budget : Nat) :
    (simulateQ poolLift program).IsQueryBoundP (fun query => classify (KemSK := KemSK) query = some kind) budget ↔
      program.IsQueryBoundP (fun query => poolClass (KemSK := KemSK) query = kind) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, poolLift, isQueryBoundP_query_bind_iff]
      simp only [classify, Option.some.injEq] at ih ⊢
      exact and_congr Iff.rfl (forall_congr' fun reply => ih reply _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual constructor requests one generated identity at most on its generated branch; caller-known import never becomes a generated target or an additional private capability. -/
theorem constructor_private (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (kind : Kind) :
    (PqxdhRegistrationJointServerBirth.client (KemSK := KemSK) (P := Unit) sender supplied).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = some kind)
      (if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) := by
  cases kind <;> cases supplied <;>
    simp [PqxdhRegistrationJointServerBirth.client, classify, poolClass, isQueryBoundP_query_bind_iff]
  all_goals split <;> simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Actual initialization and the complete adaptive source-command program have one origin-sensitive generated-Server allowance plus the exact existing private command caps, counting all failed attempts and every typed reply. -/
theorem initialized_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = some kind)
      ((if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
        PqxdhRegistrationJointOpenCosts.privateTotal budget kind) := by
  unfold PqxdhRegistrationJointOpenInitialization.client
  apply isQueryBoundP_bind (constructor_private setup.serverKeyId supplied kind)
  rintro (_ | created) _
  · trivial
  · simpa only [isQueryBoundP_map_iff, lifted_queries] using
      PqxdhRegistrationJointOpenCosts.command_program setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity program budget certified [] (PqxdhRegistrationJointInitializedAccept.initial created) kind nonuniform

/-- True counts runtime initialization; false counts caller-known import. These are actual local constructor calls, not private primitive security oracles. -/
def localClass : (Spec KemSK).Domain → Option Bool
  | .inr .initialize => some true
  | .inr (.importSeed _) => some false
  | .inl _ => none

/-- The subsequent complete command program cannot repeat runtime initialization or import another Server seed through its service-forwarding path. -/
theorem lifted_local_free (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (kind : Bool) :
    (simulateQ poolLift program).IsQueryBoundP (fun query => localClass (KemSK := KemSK) query = some kind) 0 := by
  induction program using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, poolLift, isQueryBoundP_query_bind_iff, localClass,
        reduceCtorEq, not_false_eq_true, true_or, ite_false, true_and]
      exact ih

set_option backward.isDefEq.respectTransparency false in
/-- Initial construction keeps one initialization allowance and at most one import attempt on the supplied branch, including all rejection paths and arbitrary typed replies. -/
theorem constructor_local (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (kind : Bool) :
    (PqxdhRegistrationJointServerBirth.client (KemSK := KemSK) (P := Unit) sender supplied).IsQueryBoundP
      (fun query => localClass (KemSK := KemSK) query = some kind)
      (if kind then 1 else if supplied.isSome then 1 else 0) := by
  cases kind <;> cases supplied <;>
    simp [PqxdhRegistrationJointServerBirth.client, localClass, isQueryBoundP_query_bind_iff]
  all_goals split <;> simp [isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The complete initialized adaptive execution has at most one initialization callback and, on the supplied branch, at most one import. Later commands cannot repeat either local constructor action. -/
theorem initialized_local (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (kind : Bool) :
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program).IsQueryBoundP
      (fun query => localClass (KemSK := KemSK) query = some kind)
      (if kind then 1 else if supplied.isSome then 1 else 0) := by
  unfold PqxdhRegistrationJointOpenInitialization.client
  apply isQueryBoundP_bind (m := 0) (constructor_local setup.serverKeyId supplied kind)
  rintro (_ | created) _
  · trivial
  · simpa only [isQueryBoundP_map_iff] using lifted_local_free
      ((PqxdhRegistrationJointOpenBackend.compile setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program) []).run
          (PqxdhRegistrationJointInitializedAccept.initial created)) kind

end BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.lifted_queries' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.lifted_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.constructor_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.constructor_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.initialized_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.initialized_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.lifted_local_free' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.lifted_local_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.constructor_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.constructor_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.initialized_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedCosts.initialized_local
