-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import BeaconcryptCore.Computational.CtxComputationalSecurity
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts

/-! Syntactic uniform-query receipts for the actual counted native samplers and shared hash. These bound every reply branch of the original program before any operational counter projection. ML capability replies remain free, so no dummy signer evaluation is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Forwarding and recording each actual uniform query introduces no additional draw. -/
theorem counted (work : ProbComp Value) (cap : Nat) (bounded : work.IsTotalQueryBound cap) (before : Nat) :
    ((simulateQ PqxdhRecordLiftWorld.countCoin work).run before).IsTotalQueryBound cap := by
  apply (isQueryBoundP_true_iff _ _).mp
  apply ((isQueryBoundP_true_iff work cap).mpr bounded).simulateQ_run_StateT_of_step _ before
  intro query current
  simp only [PqxdhRecordLiftWorld.countCoin, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, ite_true]
  exact fun _ => Nat.zero_lt_one

/-- The native World sampler preserves the primitive program's complete all-replies draw cap. -/
theorem sampled (work : ProbComp Value) (cap : Nat) (bounded : work.IsTotalQueryBound cap)
    (before : PqxdhRecordLiftWorld.State n) :
    ((PqxdhRecordLiftWorld.sampled work).run before).IsTotalQueryBound cap := by
  simpa only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff] using counted work cap bounded before.primitive.1.uniform

/-- One actual shared hash request pays at most its64-byte cache miss, retaining all cache-hit branches. -/
theorem hash (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n) :
    ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before).IsTotalQueryBound 64 := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff]
  exact sampled _ _ (CtxComputationalSecurity.ctxRandomOracle_total_query_bound _ _) _

private theorem capability_hash {Auxiliary : Type} (bytes : Pqxdh.Bytes) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationWorldServerCompletion.capability (.hash bytes)).run before).IsTotalQueryBound 64 := by
  simpa only [RegistrationWorldServerCompletion.capability, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    hash bytes before.world.1

/-- Current pin selection is pure and has no uniform query. -/
theorem initializePin_no_queries {Auxiliary : Type} (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary) :
    ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before).IsTotalQueryBound 0 := by
  rw [RegistrationWorldServerFrontend.initializePin_native]
  trivial

/-- The prior conservative ceiling follows from the exact zero-query result. -/
theorem initializePin {Auxiliary : Type} (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary) :
    ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before).IsTotalQueryBound 64 :=
  (initializePin_no_queries binding publicKey before).mono (Nat.zero_le 64)

/-- Initial Server installation and pure pin selection fit the prior conservative64-draw resource ceiling. -/
theorem frontend_start {Auxiliary : Type} (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (publicKey : Std.Array U8 1952#usize) (auxiliary : Auxiliary) (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationWorldServerFrontend.start created publicKey auxiliary).run before).IsTotalQueryBound 64 := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run]
  apply isTotalQueryBound_bind (n₁ := 0) (n₂ := 64)
  · cases present : before.server <;>
      simp only [PqxdhRecordLiftWorld.initializeServer, present, IsTotalQueryBound, isQueryBound_pure]
  · intro installed
    exact isTotalQueryBound_bind (n₂ := 0) (initializePin _ _ _) (fun _ => by trivial)

variable {source : RegistrationNativeMldsa.Source}

def IsCoin : (RegistrationNativeMldsaProgram.Spec source).Domain → Prop
  | .inl _ => True
  | _ => False
instance : DecidablePred (IsCoin (source := source)) := fun query => by
  cases query
  · exact instDecidableTrue
  · exact instDecidableFalse

/-- Ordinary source work retains its literal uniform-query cap when lifted into the free ML language. -/
theorem ordinary (work : ProbComp Value) (count : Nat) (bounded : work.IsTotalQueryBound count) :
    (RegistrationNativeMldsaProgram.lift (source := source) work).IsQueryBoundP IsCoin count := by
  have transferred := IsQueryBoundP.simulateQ_of_step_le_total
    (impl := RegistrationNativeMldsaProgram.ordinary) bounded (fun query => by
      change OracleComp.IsQueryBoundP ((RegistrationNativeMldsaProgram.Spec source).query (.inl query) :
        OracleComp (RegistrationNativeMldsaProgram.Spec source) _) IsCoin 1
      simp only [isQueryBoundP_query_iff, IsCoin]
      trivial)
  simpa only [RegistrationNativeMldsaProgram.lift, Nat.mul_one] using transferred

/-- A named capability request adds no ordinary uniform query, for any optional reply and any private accounting count. -/
theorem call (accounting : RegistrationNativeMldsaCapability.Accounting)
    (query : RegistrationNativeMldsaCapability.Request source) (before : PqxdhRecordLiftWorld.State n) :
    ((RegistrationNativeMldsaProgram.call accounting query).run before).IsQueryBoundP IsCoin 0 := by
  simp [RegistrationNativeMldsaProgram.call, StateT.run, IsCoin]

/-- Complete free startup pays the actual initializer and32 identity-byte draws, retaining the prior conservative64 allowance for the now-pure pin prefix; Server generation remains a separate named slot. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (qInit : Nat) (initialization : (ensureInit.run ()).IsTotalQueryBound qInit)
    (identityIndex : Nat) (serverKid : U64) :
    (RegistrationNativeMldsaCreation.start (n := n) (source := source) setup ensureInit identityIndex serverKid).IsQueryBoundP
      IsCoin (qInit + 32 + 64) := by
  have constructor :
      ((PqxdhLiveServerConstruction.construct (P := Std.Array U8 151#usize) setup.joint ensureInit identityIndex serverKid none).run ()).IsTotalQueryBound
        (qInit + 32) := by
    simpa only [Option.isNone_none, ite_true] using
      PqxdhLiveServerConstruction.construct_uniform (P := Std.Array U8 151#usize) setup.joint ensureInit qInit
        (fun state => by cases state; exact initialization) identityIndex serverKid none ()
  unfold RegistrationNativeMldsaCreation.start
  apply isQueryBoundP_bind (n := qInit + 32) (m := 64)
    (ordinary _ (qInit + 32) (sampled _ _ constructor _))
  intro constructed _
  cases selected : constructed.1.1 with
  | none => trivial
  | some created =>
    apply isQueryBoundP_bind (n := 0) (m := 64) (call .native .generate constructed.2)
    intro generated _
    cases generated.1 with
    | none => trivial
    | some credential =>
      apply isQueryBoundP_bind (n := 64) (m := 0)
        (ordinary _ 64 (frontend_start created credential.publicKey RegistrationServerRoleBackend.empty generated.2))
      intro initialized _
      cases initialized.1 <;> try trivial
      rename_i answer
      cases answer <;> trivial
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.counted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.sampled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.initializePin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.initializePin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.frontend_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.frontend_start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.initializePin_no_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives.initializePin_no_queries
