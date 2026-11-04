-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalWriters
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts
open BeaconcryptCore.Refinement
variable {E A B : Type}
open AdapterRecordHelperRequestMonad (Program)
private theorem lift_bound (action : RustM A) (next : A → Program E B) (cap : Nat)
    (bounded : ∀ value, (next value).run.IsTotalQueryBound cap) :
    ((AdapterRecordRequestMonad.liftRust action >>= next : Program E B).run).IsTotalQueryBound cap := by
  cases action <;> simp only [Program.run_bind, Program.run_lift, pure_bind]
  · exact bounded _
  all_goals trivial
private theorem pure_bound (value : A) (cap : Nat) :
    ((pure value : Program E A).run).IsTotalQueryBound cap := by trivial
private theorem query_bound (query : AdapterRecordHelperRequestMonad.Request) (next : AdapterRecordHelperRequestMonad.Response E query → Program E B) (cap : Nat)
    (bounded : ∀ value, (next value).run.IsTotalQueryBound cap) :
    ((Program.query query >>= next : Program E B).run).IsTotalQueryBound (cap + 1) := by
  simp only [Program.run_bind, Program.query]
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, ?_⟩
  intro reply
  cases reply with
  | ok value => simpa only [Nat.add_sub_cancel] using bounded value
  | fail error | div => trivial
theorem raw (parts : Std.Array (Slice U8) 3#usize) :
    (AdapterRecordHelperRequestExtraction.raw (E := E) (m := Program E) parts).run.IsTotalQueryBound 1 := by
  unfold AdapterRecordHelperRequestExtraction.raw
  repeat' first
    | apply lift_bound; intro value
    | apply query_bound; intro value
    | split
    | exact pure_bound _ _
    | trivial
theorem frame (sequence sender : U64) (parts : Std.Array (Slice U8) 3#usize) :
    (AdapterRecordHelperRequestExtraction.frame (E := E) (m := Program E) sequence sender parts).run.IsTotalQueryBound 2 := by
  unfold AdapterRecordHelperRequestExtraction.frame
  repeat' first
    | apply lift_bound; intro value
    | apply query_bound; intro value
    | split
    | exact pure_bound _ _
    | trivial
/-- The selected source dispatcher reaches at most two helper leaves; serializer work is included conservatively in this syntax count. -/
theorem route (request : record_effects.RecordWriteRequest) :
    (AdapterRecordHelperRouting.route (E := E) (m := Program E) request).run.IsTotalQueryBound 2 := by
  cases request with
  | Raw parts => exact (raw parts).mono (by decide)
  | Frame parts sequence sender => exact frame sequence sender parts

namespace Seal
variable [primitive : AdapterSealPrimitive.Operations]
private theorem lift_bound (action : RustM A) (next : A → AdapterSealRequestMonad.Program E B) (cap : Nat)
    (bounded : ∀ value, (next value).run.IsTotalQueryBound cap) :
    ((AdapterRecordRequestMonad.liftRust action >>= next : AdapterSealRequestMonad.Program E B).run).IsTotalQueryBound cap := by
  cases action <;> simp only [AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.run_lift, pure_bind]
  · exact bounded _
  all_goals trivial
private theorem pure_bound (value : A) (cap : Nat) :
    ((pure value : AdapterSealRequestMonad.Program E A).run).IsTotalQueryBound cap := by trivial
private theorem query_bound (query : AdapterSealRequestMonad.Request) (next : AdapterSealRequestMonad.Response E query → AdapterSealRequestMonad.Program E B) (cap : Nat)
    (bounded : ∀ value, (next value).run.IsTotalQueryBound cap) :
    ((AdapterSealRequestMonad.Program.query query >>= next : AdapterSealRequestMonad.Program E B).run).IsTotalQueryBound (cap + 1) := by
  simp only [AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.query]
  rw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, ?_⟩
  intro reply
  cases reply with
  | ok value => simpa only [Nat.add_sub_cancel] using bounded value
  | fail error | div => trivial
/-- The complete actual seal source program reaches at most its one allocator and one native AEAD request; Single reaches only AEAD. -/
theorem source (request : record_effects.AeadSealRequest) :
    (AdapterSealRequestExtraction.execute (E := E) (m := AdapterSealRequestMonad.Program E) request).run.IsTotalQueryBound 2 := by
  unfold AdapterSealRequestExtraction.execute AdapterSealRequestMonad.Lifted.join AdapterSealJoinRequestExtraction.join
  repeat' first
    | rw [bind_assoc]
    | apply lift_bound; intro value
    | apply query_bound; intro value
    | split
    | exact pure_bound _ _
    | trivial
end Seal
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.route

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.Seal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicHelperCounts.Seal.source
