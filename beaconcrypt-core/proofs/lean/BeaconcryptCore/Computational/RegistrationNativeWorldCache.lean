-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationWorldCache
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-! Every actual native trusted program extends the single current CTX cache, independently of local owner and environment mutations. Native closure restores its cache from the reached World, so all Beacon constructor, outgoing and terminal finish continuations retain every earlier hash receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeWorldCache
open PqxdhServerAuthExperiment (Setup Checks Codec)
variable {n : Nat} {ι KemSK Value Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def cache (before : RegistrationNativeExperiment.State n KemSK source) : CtxRomAuth.CtxRO.QueryCache :=
  before.server.world.world.1.primitive.2

/-- Actual environment requests and private indexed KEM calls retain every earlier shared hash receipt. -/
theorem trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    cache before ≤ cache result.2 := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server, StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨inner, possible, same⟩ := supported
      cases same
      exact RegistrationWorldCache.effects_cache query before.server.world.world.1 inner possible
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, possible, same⟩ := supported
      cases same
      exact (RegistrationWorldCache.sampled_cache
        ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
            (before.server.world.auxiliary, before.pool)) before.server.world.world.1 inner possible).ge

/-- Complete actual trusted continuations preserve the reached shared cache through every supported failure path. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    cache before ≤ cache result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, continued⟩ := supported
      exact (trusted setup checks representation created query before middle first).trans
        (ih middle.1 middle.2 result continued)

/-- Native owner/environment closure cannot drop a hash receipt reached inside the actual callback. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    cache before ≤ cache result.2 := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact program setup checks representation created
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before inner possible

/-- The same monotonicity holds before closing native local instrumentation. -/
theorem localProgram (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeMldsaShared.Local n KemSK source)
    (result : Value × RegistrationNativeMldsaShared.Local n KemSK source)
    (supported : result ∈ support ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before)) :
    cache before.2.2 ≤ cache result.2.2.2 := by
  simp only [RegistrationNativeMldsaShared.lower, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact program setup checks representation created ((work.run before.1).run before.2.1) before.2.2 inner possible

/-- Native record size refusal leaves the cache untouched; admitted actual record callbacks extend it. -/
theorem guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain)
    (before : PqxdhRecordLiftWorld.State n)
    (result : (PqxdhRecordLiftInterface.WorldSpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((CborRecordWorldSimulation.guarded setup codec route query).run before)) :
    before.primitive.2 ≤ result.2.primitive.2 := by
  unfold CborRecordWorldSimulation.guarded at supported
  simp only [StateT.run] at supported
  cases refused : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | none =>
      simp only [refused] at supported
      exact RegistrationWorldCache.handler_cache setup codec route query before result supported
  | some reply =>
      simp only [refused, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact le_refl _

end BeaconcryptCore.Computational.RegistrationNativeWorldCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldCache.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldCache.trusted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldCache.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldCache.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldCache.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldCache.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldCache.localProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldCache.localProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldCache.guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldCache.guarded
