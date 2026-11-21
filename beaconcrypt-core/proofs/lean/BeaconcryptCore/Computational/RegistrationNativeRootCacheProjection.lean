-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation

/-! The actual ideal related-family root interpreter projects to its protected PRK cache through arbitrary adaptive root clients. Fixed ordinary inputs and chronological family instrumentation are removed only by this explicit analysis projection; every client reply, including selected signing and public HMAC, remains identical. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection
open RegistrationNativeRelatedRoot (RootSpec reduction)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

noncomputable def implementation (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl RootSpec (StateT HmacOracle.QueryCache ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr (.sign message) => pure (joint.sign seed message)
  | .inr (.publicHmac key message) => pure (hmac.eval key message)
  | .inr (.derive message) => RegistrationNativeKeyFamilyPreparation.root source hmac joint dh seed scalar message

def project (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (state : RegistrationNativeRelatedFamily.State) : HmacOracle.QueryCache :=
  RegistrationNativeKeyFamilyPreparation.cacheOf (joint.staticDh seed (dh.publicKey scalar)) state.cache

/-- Every actual root-valued family callback keeps its exact reply while retaining only the protected cache. -/
theorem query_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : RootSpec.Domain) (before : RegistrationNativeRelatedFamily.State) :
    Prod.map id (project joint dh seed scalar) <$>
      (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) (reduction query)).run before =
      (implementation source hmac joint dh seed scalar query).run (project joint dh seed scalar before) := by
  cases query with
  | inl coin =>
      simp only [reduction, simulateQ_spec_query, RegistrationNativeRelatedFamily.idealImpl,
        RegistrationNativeRelatedFamily.impl, implementation, StateT.run, StateT.lift,
        bind_pure_comp, Functor.map_map]
      rfl
  | inr query => cases query with
    | sign message =>
      simp only [reduction, simulateQ_spec_query, RegistrationNativeRelatedFamily.idealImpl,
        RegistrationNativeRelatedFamily.impl, implementation, StateT.run,
        map_pure, Prod.map, id_eq, project]
      rfl
    | publicHmac key message =>
      simp only [reduction, simulateQ_spec_query, RegistrationNativeRelatedFamily.idealImpl,
        RegistrationNativeRelatedFamily.impl, implementation, StateT.run,
        map_pure, Prod.map, id_eq, project]
      rfl
    | derive message =>
      exact RegistrationNativeKeyFamilyPreparation.root_project source hmac correct joint dh seed scalar message before

/-- The complete adaptive root client, including all its ordinary local effects and failures, has the same result and protected cache. -/
theorem program_project {Value : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp RootSpec Value) (before : RegistrationNativeRelatedFamily.State) :
    Prod.map id (project joint dh seed scalar) <$>
      (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar)
        (simulateQ reduction work)).run before =
      (simulateQ (implementation source hmac joint dh seed scalar) work).run (project joint dh seed scalar before) := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (project joint dh seed scalar)
    (query_project source hmac correct joint dh seed scalar) work before

/-- The concrete correlated ideal-root game has the derived private-cache implementation, rather than a supplied initializer equality. -/
theorem game_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp RootSpec Bool) :
    RegistrationNativeRelatedRoot.idealRootGame hmac joint dh client = (do
      let seed ← PqxdhJointIdentity.sampleSeed
      let scalar ← PqxdhJointGapDh.sampleScalar
      (simulateQ (implementation source hmac joint dh seed scalar)
        (client (PqxdhJointGapDh.challenge joint dh seed scalar))).run' ∅) := by
  unfold RegistrationNativeRelatedRoot.idealRootGame RegistrationNativeRelatedFamily.idealGame
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  have projected := congrArg (fun experiment => Prod.fst <$> experiment)
    (program_project source hmac correct joint dh seed scalar
      (client (PqxdhJointGapDh.challenge joint dh seed scalar)) RegistrationNativeRelatedFamily.empty)
  have emptyCache : project joint dh seed scalar RegistrationNativeRelatedFamily.empty = ∅ := by
    apply QueryCache.ext
    intro bytes
    simp [project, RegistrationNativeRelatedFamily.empty, RegistrationNativeKeyFamilyPreparation.cacheOf]
  simpa only [StateT.run'_eq, Functor.map_map, Prod.map, id_eq, emptyCache] using projected

end BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection.program_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection.game_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRootCacheProjection.game_project
