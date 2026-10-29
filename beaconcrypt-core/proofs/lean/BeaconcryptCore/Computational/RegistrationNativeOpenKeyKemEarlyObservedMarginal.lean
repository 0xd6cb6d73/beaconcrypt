-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal

/-! Only a candidate-independent original decision is transported from the honest complete KEM source to the explicit real presampled provider. The retained candidate is then available for the later uniform-side alias observer; no candidate-observed bad event is transported by the old prefix swap. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal
open PqxdhKemIndCca
open RegistrationNativeOpenKey (Spec Ambient)
open RegistrationNativeOpenKeyKemGame (other normal)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample

/-- Every original candidate-independent full-client decision has the exact real presampled-provider marginal, including inactive and mismatched getter branches. -/
theorem real_marginal (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Value) (decision : Value → Bool) (count : Nat) (selected : Fin (count + 1))
    (bounded : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    normal baseImpl kem (simulateQ RegistrationNativeOpenKey.native (decision <$> work)) =ᵈ
      RegistrationNativeOpenKeyKemEarlyObservedReal.source baseImpl kem work (fun _ result => decision result) count selected := by
  have creates : (simulateQ RegistrationNativeOpenKey.native (decision <$> work)).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count := by
    simpa only [simulateQ_map, isQueryBoundP_map_iff] using bounded
  have hidden : (simulateQ RegistrationNativeOpenKey.native (decision <$> work)).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0 := by
    simpa only [simulateQ_map, isQueryBoundP_map_iff] using noReveal
  have honest := RegistrationNativeOpenKeyKemGame.normal_source baseImpl kem
    (simulateQ RegistrationNativeOpenKey.native (decision <$> work)) count selected creates hidden
  have early := RegistrationNativeKemEarlySource.source_real baseImpl kem (other baseImpl kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native (decision <$> work)) count selected
  have observed := RegistrationNativeOpenKeyKemEarlyObservedReal.real_source baseImpl kem work
    (fun _ result => decision result) count selected bounded noReveal
  have same : RegistrationNativeKemEarlyCorrectness.sourceReal baseImpl kem (other baseImpl kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native (decision <$> work)) count selected =
      RegistrationNativeKemEarlyObservedCorrectness.sourceReal baseImpl kem (other baseImpl kem) (pure ∅)
        (simulateQ RegistrationNativeOpenKey.native work) (fun _ result => decision result) count selected := by
    simp only [simulateQ_map]
    rfl
  rw [same] at early
  exact honest.trans (early.symm.trans observed)

/-- The original complete native decision pays one ordinary KEM-CCA advantage and correctness loss to the explicit candidate-retaining uniform branch. Materialization and its candidate-observed audit are performed only on that uniform side. -/
theorem normal_close (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (work : OracleComp (Spec KemSK) Value) (decision : Value → Bool) (count : Nat) (selected : Fin (count + 1))
    (bounded : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    (normal baseImpl kem (simulateQ RegistrationNativeOpenKey.native (decision <$> work))).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem (other baseImpl kem) (pure ∅)
        (simulateQ RegistrationNativeOpenKey.native work) (fun _ result => decision result) count selected false) ≤
      (kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (RegistrationNativeKemEarlyObservedGame.adversary baseImpl kem (other baseImpl kem) (pure ∅)
          (simulateQ RegistrationNativeOpenKey.native work) (fun _ result => decision result) count selected).toINDCCA).toReal +
      RegistrationNativeKemEarlyCorrectness.correctnessError baseImpl kem := by
  have equal := (real_marginal baseImpl kem work decision count selected bounded noReveal).prEvent_eq (fun result => result = true)
  have close := RegistrationNativeOpenKeyKemEarlyObservedReal.source_close baseImpl kem functional work
    (fun _ result => decision result) count selected bounded noReveal
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, ← equal] using close

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal.real_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal.real_marginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal.normal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedMarginal.normal_close
