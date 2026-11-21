-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyRealSource
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedRealSource

/-! The explicit real observed KEM source closes the actual original open-key client with the literal real reserved provider and lazy108-byte table. The mathematical real challenge secret reaches only the pure final observer. The entire original client result and table/provider transcript pass through the exact source reassociation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeOpenKey (Spec Ambient)
open RegistrationNativeOpenKeyKemGame (other)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample

noncomputable def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  observe pair.2 <$> (simulateQ (RegistrationNativeOpenKeyKemEarlyRealSource.reference baseImpl kem
    (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2) work).run' ((PqxdhLiveKemBirth.empty, none), ∅)

/-- The complete original native open-key real source retains the real challenge secret only for its pure final observation, with the same actual real provider and lazy table. -/
theorem real_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyObservedCorrectness.sourceReal baseImpl kem (other baseImpl kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native work) observe count selected =ᵈ
      source baseImpl kem work observe count selected := by
  have real := RegistrationNativeKemEarlyObservedRealSource.source_real baseImpl kem (other baseImpl kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native work) observe count selected bounded noReveal
  refine real.trans ?_
  unfold RegistrationNativeKemEarlyObservedRealSource.source source
  simp only [pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro chosen
  apply _root_.EvalDistEq.bind_right
  intro others
  apply _root_.EvalDistEq.bind_right
  intro pair
  apply _root_.EvalDistEq.bind_right
  intro unused
  rw [← QueryImpl.simulateQ_compose]
  change EvalDistEq
    (observe pair.2 <$> (simulateQ (RegistrationNativeOpenKeyKemEarlyRealSource.implementation baseImpl kem
      (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 pair.2) work).run' ((∅, PqxdhLiveKemBirth.empty), none)) _
  rw [RegistrationNativeOpenKeyKemEarlyRealSource.values_source]
  exact .rfl

/-- The complete observed real open-key source has one explicit ordinary CCA advantage and one unconditional correctness loss against the challenge-retaining uniform branch. -/
theorem source_close (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (work : OracleComp (Spec KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    (source baseImpl kem work observe count selected).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem (other baseImpl kem) (pure ∅)
        (simulateQ RegistrationNativeOpenKey.native work) observe count selected false) ≤
      (kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (kemAmbientImpl baseImpl))
        (RegistrationNativeKemEarlyObservedGame.adversary baseImpl kem (other baseImpl kem) (pure ∅)
          (simulateQ RegistrationNativeOpenKey.native work) observe count selected).toINDCCA).toReal +
      RegistrationNativeKemEarlyCorrectness.correctnessError baseImpl kem := by
  have equal := (real_source baseImpl kem work observe count selected bounded noReveal).prEvent_eq (fun result => result = true)
  have close := RegistrationNativeKemEarlyObservedCorrectness.source_close baseImpl kem functional
    (other baseImpl kem) (pure ∅) (simulateQ RegistrationNativeOpenKey.native work) observe count selected
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, equal] using close

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal.real_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedReal.source_close
