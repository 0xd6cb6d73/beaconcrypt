-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal
/-! Actual first-record primitive calls erase only request/signing/owner instrumentation. The physical backend retains the same private pool, auxiliary state, counters, record state, frames and shared cache. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}

def project (pool : PqxdhLiveKemBirth.Pool KemSK) (before : RegistrationServerRootCompiler.Local n) : Backend n KemSK :=
  ⟨before.auxiliary,pool,worldBackend before.world.1⟩

noncomputable def record (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (Backend n KemSK) ProbComp) :=fun query before=>
  (fun result=>(result.1,{before with world:=worldBackend {before.world with primitive:=result.2}})) <$>
    (PqxdhRecordLiftWorld.primitives setup codec query).run before.world.primitive

theorem record_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationWorldRecords.record setup codec query).run before=
      (record setup codec query).run (project pool before) := by
  have same:=congrArg (fun computation=>(fun result=>(result.1,
      (⟨before.auxiliary,pool,worldBackend {before.world.1 with primitive:=result.2}⟩ :Backend n KemSK))) <$>computation)
    (RegistrationNativePlatformSdkOrdinaryReification.primitive_query setup codec query before.world.1.primitive)
  simp only [record,RegistrationWorldRecords.record,StateT.run,project,worldBackend,
    RegistrationNativePlatformSdkOrdinaryReification.primitive,Functor.map_map,Prod.map,id_eq] at same ⊢
  simpa only [Function.update_idem] using same

noncomputable def hash (bytes : Pqxdh.Bytes) : StateT (Backend n KemSK) ProbComp CtxRomAuth.CtxDigest :=fun before=>
  (fun result=>(result.1,{before with world:=worldBackend result.2})) <$>
    (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before.world

private theorem hash_world (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id worldBackend <$> (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before=
      (PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run (worldBackend before) := by
  simp only [PqxdhRecordLiftWorld.effects,PqxdhRecordLiftWorld.chargeEffect,PqxdhRecordLiftInterface.effectKind,
    PqxdhRecordLiftWorld.capability,PqxdhRecordLiftWorld.sampled,worldBackend,StateT.run,bind_pure_comp,Functor.map_map]
  dsimp only [Prod.map,id_eq,worldBackend]
  congr 1
  funext result
  have effects : Function.update (Function.update before.primitive.1.effects .hash (before.primitive.1.effects .hash+1)) .administrative 0=
      Function.update (Function.update before.primitive.1.effects .administrative 0) .hash
        ((Function.update before.primitive.1.effects .administrative 0) .hash+1) := by
    funext kind
    cases kind <;> simp
  simp only [effects]

noncomputable def shared (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl MldsaSharedNative.Spec (StateT (Backend n KemSK) ProbComp)
  | .inr query=>record setup codec query
  | .inl query=>hash query.2

theorem shared_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (query : MldsaSharedNative.Spec.Domain)
    (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationWorldRecords.shared setup codec query).run before=
      (shared setup codec query).run (project pool before) := by
  cases query with
  | inr query=>exact record_source setup codec pool query before
  | inl query=>
    have same:=congrArg (fun computation=>(fun result=>(result.1,
      (⟨before.auxiliary,pool,worldBackend result.2⟩ :Backend n KemSK))) <$>computation)
      (hash_world query.2 before.world.1)
    simp only [shared,hash,RegistrationWorldRecords.shared,StateT.run,project,Functor.map_map,Prod.map,id_eq] at same ⊢
    simpa only [RegistrationNativePlatformSdkReification.worldBackend_idempotent] using same

noncomputable def records (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RegistrationRecordPrimitives.Spec (StateT (Backend n KemSK) ProbComp) :=
  shared setup codec ∘ₛ RegistrationRecordPrimitives.callbacks setup.source

theorem records_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (query : RegistrationRecordPrimitives.Spec.Domain)
    (before : RegistrationServerRootCompiler.Local n) :
    Prod.map id (project pool) <$> (RegistrationWorldRecords.handler setup codec query).run before=
      (records setup codec query).run (project pool before) := by
  have same:=OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project pool)
    (shared_source setup codec pool) (RegistrationRecordPrimitives.callbacks setup.source query) before
  simp only [records,QueryImpl.apply_compose,RegistrationWorldRecords.handler,StateT.run,
    Functor.map_map,Prod.map,id_eq,project]
  change (fun result=>(result.1,project pool result.2)) <$>
    (simulateQ (RegistrationWorldRecords.shared setup codec) (RegistrationRecordPrimitives.callbacks setup.source query)).run before=_
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend.record_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend.shared_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend.records_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRecordBackend.records_source
