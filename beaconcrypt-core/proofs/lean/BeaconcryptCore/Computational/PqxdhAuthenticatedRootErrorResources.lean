import BeaconcryptCore.Computational.PqxdhKemCorrectnessError

/-!
The ordinary correctness-error experiment pays its actual evaluated key-generation, encapsulation and decapsulation costs in source order. The primitive operations each occur once in this endpoint's syntax; a zero oracle-query cost for functional decapsulation does not remove its deterministic local invocation or runtime. This is a resource theorem about the existing error game, not a primitive correctness or security assumption.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootErrorResources
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhKemCorrectnessError
variable {ι KemSK : Type} {baseSpec : OracleSpec ι}

/-- The same ordinary recipient-error endpoint retains all three evaluated primitive bills, including the actual decapsulation attempt. -/
theorem error_uniform
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (qKeygen qEncap qDecap : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)).IsTotalQueryBound qEncap)
    (decapBound : ∀ key ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps key ciphertext)).IsTotalQueryBound qDecap) :
    (simulateQ (kemAmbientImpl baseImpl) (errorExperiment kem)).IsTotalQueryBound (qKeygen + qEncap + qDecap) := by
  simp only [errorExperiment, sample, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  apply (isTotalQueryBound_bind keygenBound (n₂ := qEncap + qDecap) ?_).mono (Nat.add_assoc _ _ _).symm.le
  intro keys
  apply isTotalQueryBound_bind (encapBound keys.1)
  exact fun pair => by simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using decapBound keys.2 pair.1

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootErrorResources

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootErrorResources.error_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootErrorResources.error_uniform
