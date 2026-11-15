-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
variable {n : Nat} {I KemSK A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def OnlyWorld : (Trusted n KemSK).Domain → Prop
  | .inl _ => True
  | .inr _ => False

 theorem query (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (effect : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Backend n KemSK) :
    Prod.map id erase <$> (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created (.inl effect)).run before =
      (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created (.inl effect)).run (erase before) := by
  simp only [RegistrationNativePlatformSdkFinishBackend.handler,StateT.run,Functor.map_map,erase]
  rfl

 theorem query_frame (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (effect : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Backend n KemSK)
    (result : (PqxdhRecordLiftInterface.EnvEffects n).Range effect × Backend n KemSK)
    (supported : result∈support ((RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created (.inl effect)).run before)) :
    result.2.pool=before.pool ∧worldBackend result.2.world=result.2.world := by
  simp only [RegistrationNativePlatformSdkFinishBackend.handler,StateT.run] at supported
  rw [support_map] at supported
  obtain ⟨middle,_called,same⟩:=supported
  subst result
  exact ⟨rfl,RegistrationNativePlatformSdkReification.worldBackend_idempotent middle.2⟩

 theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Trusted n KemSK) A) (safe : work.AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK))) (before : Backend n KemSK) :
    Prod.map id erase <$> (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created) work).run before =
      (simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created) work).run (erase before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,map_pure];rfl
  | query_bind selected next ih=>
      rw [allQueriesSatisfy_query_bind_iff] at safe
      cases selected with
      | inr kem=>exact False.elim safe.1
      | inl effect=>
          simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          rw [←query setup checks representation created effect before,bind_map_left]
          apply bind_congr
          intro middle
          exact ih middle.1 (safe.2 middle.1) middle.2

 theorem program_frame (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Trusted n KemSK) A) (safe : work.AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)))
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (result : A × Backend n KemSK)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created) work).run before)) :
    result.2.pool=before.pool ∧worldBackend result.2.world=result.2.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>
      simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨rfl,canonical⟩
  | query_bind selected next ih=>
      rw [allQueriesSatisfy_query_bind_iff] at safe
      cases selected with
      | inr kem=>exact False.elim safe.1
      | inl effect=>
          simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
          obtain ⟨middle,called,later⟩:=supported
          have first:=query_frame setup checks representation created effect before middle called
          have rest:=ih middle.1 (safe.2 middle.1) middle.2 first.2 later
          exact ⟨rest.1.trans first.1,rest.2⟩

private theorem simulate_only {J : Type} {spec : OracleSpec J}
    (handler : QueryImpl spec (OracleComp (Trusted n KemSK)))
    (leaves : ∀query,(handler query).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)))
    (work : OracleComp spec A) : (simulateQ handler work).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value=>exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>
      simp only [simulateQ_bind,simulateQ_spec_query]
      exact allQueriesSatisfy_bind (leaves query) ih

private theorem coins_only (work : ProbComp A) :
    (RegistrationNativeAgreementJournal.coins (n:=n) (KemSK:=KemSK) work).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)) :=
  simulate_only (fun query : unifSpec.Domain=>((Trusted n KemSK).query (.inl (.inl query)) : OracleComp (Trusted n KemSK) _))
    (fun _query=>(allQueriesSatisfy_query_iff _ _).mpr trivial) work

 theorem authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup query).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)) := by
  cases query with
  | hash request=>
      unfold AdapterPublicFinishFreeTree.authentication
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _=>allQueriesSatisfy_pure _ _)
  | mldsa request | ed25519 request=>exact allQueriesSatisfy_pure _ _

 theorem record (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    (RegistrationNativeRecordJournal.core (n:=n) setup wire query).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)) := by
  cases query with
  | hash transcript | adHash request=>
      unfold RegistrationNativeRecordJournal.core
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _=>allQueriesSatisfy_pure _ _)
  | _=>exact coins_only _

 theorem authentication_program (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec A) :
    (simulateQ (AdapterPublicFinishFreeTree.authentication (n:=n) (source:=source) setup) work).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)) :=
  simulate_only _ (authentication setup) work

 theorem record_program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec A) :
    (simulateQ (RegistrationNativeRecordJournal.core (n:=n) setup wire) work).AllQueriesSatisfy (OnlyWorld (n:=n) (KemSK:=KemSK)) :=
  simulate_only _ (record setup wire) work

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.query_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.query_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.program_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.authentication_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.authentication_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.record_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishWorld.record_program
