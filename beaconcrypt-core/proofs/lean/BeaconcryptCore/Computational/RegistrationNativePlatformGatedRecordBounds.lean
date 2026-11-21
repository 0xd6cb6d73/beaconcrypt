-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface
import BeaconcryptCore.Computational.CborRawRecordLiftBounds
/-! Public allocation introduces no send or raw-receive request. The exact source secrecy-wrapper record caps therefore carry into the same gated World client in every observation mode, independently of allocator randomness or failure. Public allocator uniform costs are separate from these record caps. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftBudget (RecordKind WorldRecord NativeRecord recordBudget)
open PqxdhDeploymentInterface (Spec Mode ModeSpec FreshBounds Budget)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformGatedRecordInterface (closed post native program client)
variable {n : Nat} {E Failure A X Reader Response : Type}

private theorem closed_zero (work : StateT E ProbComp A) (before : E) (kind : RecordKind) :
    ((closed (n := n) work).run before).IsQueryBoundP (WorldRecord kind) 0 := by
  apply (isQueryBoundP_false (work.run before) 0).simulateQ_of_step
  all_goals simp [PqxdhRecordLiftInterface.coinLift, WorldRecord, isQueryBoundP_query_iff]

private theorem post_zero (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (reply : Spec.Range query) (before : E) (kind : RecordKind) :
    ((post (n := n) reserve query reply).run before).IsQueryBoundP (WorldRecord kind) 0 := by
  rcases query with coin | command
  · exact isQueryBoundP_pure _ _ 0
  · cases command <;> first | exact closed_zero _ before kind | exact isQueryBoundP_pure _ _ 0

/-- Allocation does not increase either native record category on any reply branch. -/
theorem native_step (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (kind : RecordKind) (query : Spec.Domain) (before : E) :
    ((native env reserve query).run before).IsQueryBoundP (WorldRecord kind)
      (if NativeRecord kind query then 1 else 0) := by
  simp only [native, StateT.run_bind]
  exact (isQueryBoundP_bind (PqxdhRecordLiftBudget.native_record_step env kind query before)
    (fun result _ => post_zero reserve query result.1 result.2 kind)).mono (Nat.add_zero _).le

/-- All adaptive native continuations retain their joint send/raw budget through the stateful terminal gate. -/
theorem native_bound (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (kind : RecordKind) (work : OracleComp Spec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (NativeRecord kind) cap) (before : E) :
    ((simulateQ (native env reserve) work).run before).IsQueryBoundP (WorldRecord kind) cap :=
  bounded.simulateQ_run_of_step
    (fun query selected state => by simpa only [ite_eq_left selected] using native_step env reserve kind query state)
    (fun query other state => by simpa only [ite_eq_right other] using native_step env reserve kind query state) before

/-- The actual test/fresh wrapper counts each send once before any allocation reply is known. -/
theorem program_bound (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) (kind : RecordKind) :
    (program env reserve crypto codec serverKid bounds mode adversary).IsQueryBoundP (WorldRecord kind) (recordBudget budget kind) := by
  apply (isQueryBoundP_bind (m := recordBudget budget kind)
    (PqxdhRecordLiftBudget.startup_record_bound env kind) ?_).mono (by omega)
  rintro (_ | ⟨created, initial⟩) _ <;>
    simp only [WorldRecord, isQueryBoundP_query_bind_iff, bind_pure_comp, isQueryBoundP_map_iff]
  · exact isQueryBoundP_pure _ _ _
  · constructor
    · exact Or.inl (fun impossible => impossible)
    · intro _
      exact native_bound env reserve kind _ _
        (PqxdhRecordLiftBudget.wrap_record_bound crypto codec serverKid bounds mode budget adversary respects kind) initial

/-- The same open client used by the chain and CTX reductions has the original finite record budget after actual cursor admission. -/
theorem client_bound (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    PqxdhRecordLiftLaterWorlds.RecordBounded budget (client env reserve crypto codec serverKid bounds mode adversary) :=
  fun kind => CborRecordWorldClient.client_bound _ (WorldRecord kind) _
    (program_bound env reserve crypto codec serverKid bounds mode budget adversary respects kind)

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.native_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.native_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds.client_bound
