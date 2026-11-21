-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
import BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkReification (Backend backend worldBackend backendLeaf)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

noncomputable def handler (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Trusted n KemSK) (StateT (Backend n KemSK) ProbComp)
  | .inl effect=>fun before=>(fun result=>(result.1,{before with world:=worldBackend result.2})) <$>
      (PqxdhRecordLiftWorld.effects effect).run before.world
  | .inr kem=>backendLeaf setup checks representation created (.inr (.inr kem))

theorem query (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (selected : (Trusted n KemSK).Domain) (safe : RegistrationNativeWorldOwnerFrame.Safe selected) (before : Native) :
    Prod.map id backend <$>(RegistrationNativeExperiment.trusted setup checks representation created source selected).run before=
      (handler setup checks representation created selected).run (backend before) :=by
  cases selected with
  | inr kem=>exact RegistrationNativePlatformSdkReification.kem_backend setup checks representation created kem before
  | inl effect=>cases effect with
    | inl coin=>exact RegistrationNativePlatformSdkReification.coin_backend setup checks representation created coin before
    | inr capability=>cases capability with
      | hash bytes=>exact RegistrationNativePlatformSdkReification.hash_backend setup checks representation created bytes before
      | _=>exact False.elim safe

theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Trusted n KemSK) A) (safe : AllQueriesSatisfy work (RegistrationNativeWorldOwnerFrame.Safe (KemSK:=KemSK)))
    (before : Native) :
    Prod.map id backend <$>(simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before=
      (simulateQ (handler setup checks representation created) work).run (backend before) :=by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,map_pure];rfl
  | query_bind selected next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at safe
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    rw [←query setup checks representation created selected safe.1 before,bind_map_left]
    apply bind_congr
    intro middle
    exact ih middle.1 (safe.2 middle.1) middle.2

theorem platform (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (Trusted n KemSK) A) (safe : AllQueriesSatisfy work (RegistrationNativeWorldOwnerFrame.Safe (KemSK:=KemSK)))
    (before : Native) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      (simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)).run previous=
      (simulateQ coins ((simulateQ (handler setup checks representation created) work).run (backend before))).run previous :=by
  rw [←program setup checks representation created work safe before,simulateQ_map,StateT.run_map]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend.platform
