-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint
import BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant

/-! Actual native callbacks without indexed creation preserve the complete private KEM key list. They may retain their real history, cache, randomness and role-state effects. The concrete Beacon zero-creation footprints instantiate this frame condition, rather than assuming that source controllers leave the pool unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeKemBeaconFootprint (counted Bounded)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

private theorem pool_keys (baseImpl : QueryImpl base ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := base) (SK := KemSK)) (query : PqxdhLiveKemBirth.Query)
    (notCreate : query ≠ .create) (before : PqxdhLiveKemBirth.Pool KemSK)
    (result : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query × PqxdhLiveKemBirth.Pool KemSK)
    (supported : result ∈ support ((PqxdhLiveKemBirth.poolImpl baseImpl kem query).run before)) :
    result.2.keys = before.keys := by
  cases query with
  | create => exact False.elim (notCreate rfl)
  | reveal handle =>
      simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | decapsulate handle ciphertext =>
      cases found : before.keys[handle]? with
      | none =>
          simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, found, pure_bind,
            support_pure, Set.mem_singleton_iff] at supported
          cases supported
          rfl
      | some pair =>
          simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, found, mem_support_bind_iff,
            support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨reply, _decapsulated, returned⟩ := supported
          cases returned
          rfl

private theorem source_keys (baseImpl : QueryImpl base ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (query : (RegistrationNativeKemInterface.Spec ambient KemSK).Domain)
    (notCreate : ¬ RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK) query)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (result : (RegistrationNativeKemInterface.Spec ambient KemSK).Range query × (Auxiliary × PqxdhLiveKemBirth.Pool KemSK))
    (supported : result ∈ support ((RegistrationNativeKemInterface.source baseImpl kem ambient other query).run before)) :
    result.2.2.keys = before.2.keys := by
  rcases query with otherQuery | (pool | key)
  · simp only [RegistrationNativeKemInterface.source, StateT.run, support_map] at supported
    obtain ⟨inner, _reached, returned⟩ := supported
    cases returned
    rfl
  · simp only [RegistrationNativeKemInterface.source, StateT.run, support_map] at supported
    obtain ⟨inner, reached, returned⟩ := supported
    cases returned
    apply pool_keys baseImpl kem pool _ before.2 inner reached
    intro same
    subst pool
    exact notCreate trivial
  · simp only [RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp, support_map] at supported
    obtain ⟨inner, _reached, returned⟩ := supported
    cases returned
    rfl

/-- One actual trusted callback without private creation preserves every generated private KEM pair. -/
theorem trusted_keys (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (notCreate : ¬ counted (n := n) (KemSK := KemSK) .create query)
    (before : State n KemSK source)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    result.2.pool.keys = before.pool.keys := by
  cases query with
  | inl effect =>
      simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server, StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨inner, _reached, returned⟩ := supported
      cases returned
      rfl
  | inr lower =>
      simp only [RegistrationNativeExperiment.trusted, PqxdhRecordLiftWorld.sampled, StateT.run,
        bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, sampled, returned⟩ := supported
      cases returned
      have actual : inner.1 ∈ support
          ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
            (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) lower).run
              (before.server.world.auxiliary, before.pool)) := by
        apply OracleComp.support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin _
          before.server.world.world.1.primitive.1.uniform
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst sampled
      apply source_keys setup.baseImpl setup.kem _ lower _ _ inner.1 actual
      rcases lower with other | (pool | key)
      · simp [RegistrationNativeKemReservation.IsCreate]
      · cases pool <;> simp_all [RegistrationNativeKemReservation.IsCreate, counted]
      · simp [RegistrationNativeKemReservation.IsCreate]

/-- An actual adaptive trusted AST with the derived zero-create bill preserves the full private key list. -/
theorem program_keys (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (bounded : work.IsQueryBoundP (counted (n := n) (KemSK := KemSK) .create) 0)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    result.2.pool.keys = before.pool.keys := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, later⟩ := supported
      have preserved := trusted_keys setup checks representation created query (allowed.resolve_right (by omega)) before middle first
      exact (ih middle.1 (by simpa using rest middle.1) middle.2 result later).trans preserved

/-- The complete actual local-owner wrapper preserves private keys whenever its actual nested source AST has zero creation cost. -/
theorem beacon_keys (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (bounded : Bounded .create 0 work) (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.pool.keys = before.pool.keys := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have preserved := program_keys setup checks representation created _ (bounded before.beacons _) before inner reached
  cases returned
  exact preserved

end BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame.trusted_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame.trusted_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame.program_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame.beacon_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame.beacon_keys
