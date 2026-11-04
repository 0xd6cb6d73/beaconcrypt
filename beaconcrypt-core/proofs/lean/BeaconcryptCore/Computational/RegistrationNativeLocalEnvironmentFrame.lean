-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
/-! Actual Native interpretation preserves the local frontend roster and erased environment for free trees that emit only World effects and indexed private KEM calls. The frame is derived from the actual implementations, including pool changes, true draw counters and arbitrary primitive outcomes. Reassembling a doubly lifted safe tree therefore yields the same complete Native execution; no read-only backend or whole-program frame premise is assumed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame
open RegistrationNativeBeaconFrontend (Trusted)
variable {n : Nat} {I J KemSK Auxiliary A : Type} {base : OracleSpec I} {ambient : OracleSpec J} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def Allowed : (Trusted n KemSK).Domain → Prop
  | .inr (.inl _) => False
  | _ => True

private theorem source_aux (baseImpl : QueryImpl base ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (query : PqxdhLiveKemBirth.Query ⊕ PqxdhKemIndCca.MlKem768PublicKey)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (result : (RegistrationNativeKemInterface.Spec ambient KemSK).Range (.inr query) × (Auxiliary × PqxdhLiveKemBirth.Pool KemSK))
    (supported : result ∈ support ((RegistrationNativeKemInterface.source baseImpl kem ambient other (.inr query)).run before)) :
    result.2.1 = before.1 := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeKemInterface.source, StateT.run, support_map] at supported
      obtain ⟨inner, _, returned⟩ := supported
      cases returned
      rfl
  | inr key =>
      simp only [RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, returned⟩ := supported
      cases returned
      rfl

theorem trusted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (Trusted n KemSK).Domain) (allowed : Allowed query) (before : Native)
    (result : (Trusted n KemSK).Range query × Native)
    (supported : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    result.2.beacons = before.beacons ∧
      RegistrationWorldAgreementCompiler.erase result.2.server.world = RegistrationWorldAgreementCompiler.erase before.server.world := by
  cases query with
  | inl effect =>
      simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server, StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨inner, _, returned⟩ := supported
      cases returned
      exact ⟨rfl, rfl⟩
  | inr query => cases query with
    | inl other => exact False.elim allowed
    | inr lower =>
        simp only [RegistrationNativeExperiment.trusted, PqxdhRecordLiftWorld.sampled, StateT.run,
          bind_pure_comp, Functor.map_map, support_map] at supported
        obtain ⟨inner, sampled, returned⟩ := supported
        cases returned
        have actual : inner.1 ∈ support ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
            (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) (.inr lower)).run
              (before.server.world.auxiliary, before.pool)) := by
          apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin _ before.server.world.world.1.primitive.1.uniform
          rw [StateT.run'_eq, support_map]
          exact Set.mem_image_of_mem Prod.fst sampled
        have same := source_aux setup.baseImpl setup.kem _ lower _ inner.1 actual
        refine ⟨rfl, ?_⟩
        simp only [RegistrationWorldAgreementCompiler.erase]
        rw [same]

theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (Trusted n KemSK) A) (allowed : work.AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK)))
    (before : Native) (result : A × Native)
    (supported : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    result.2.beacons = before.beacons ∧
      RegistrationWorldAgreementCompiler.erase result.2.server.world = RegistrationWorldAgreementCompiler.erase before.server.world := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, called, continued⟩ := supported
      have first := trusted setup checks representation created query allowed.1 before inner called
      have later := ih inner.1 (allowed.2 inner.1) inner.2 result continued
      exact ⟨later.1.trans first.1, later.2.trans first.2⟩

def restore (before after : Native) : Native :=
  {after with
    beacons := before.beacons
    server := {after.server with world := RegistrationWorldAgreementCompiler.join (RegistrationWorldAgreementCompiler.erase before.server.world) after.server.world.world.1}}

theorem restore_eq (before after : Native) (owners : after.beacons = before.beacons)
    (env : RegistrationWorldAgreementCompiler.erase after.server.world = RegistrationWorldAgreementCompiler.erase before.server.world) :
    restore before after = after := by
  unfold restore
  rw [← owners, ← env, RegistrationWorldAgreementCompiler.join_erase]

theorem beacon_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (Trusted n KemSK) A) (allowed : work.AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK))) :
    RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeAgreementJournal.lift work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) =
      simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work := by
  funext before
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run, bind_pure_comp]
  change (fun result => (result.1.1.1, {result.2 with
      beacons := result.1.1.2
      server := {result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1}})) <$>
    ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      (((RegistrationNativeAgreementJournal.lift work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) = _
  rw [RegistrationNativeAgreementJournal.lift_run]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  change (fun result : A × Native => (result.1, restore before result.2)) <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before = _
  calc
    _ = id <$> (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before := by
      simp only [map_eq_bind_pure_comp]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      have preserved := program setup checks representation created work allowed before result supported
      change pure (result.1, restore before result.2) = pure result
      rw [restore_eq before result.2 preserved.1 preserved.2]
    _ = _ := id_map _

end BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.restore_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.restore_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.beacon_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame.beacon_lift
