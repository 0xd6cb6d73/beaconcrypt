-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedSource
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyUniform

/-! The challenge-retaining early ordinary CCA uniform branch closes through the actual early provider and literal lazy108-byte table. The unchanged open native client remains independent of the candidate; only its pure final observer receives that supplied challenge value. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedUniform
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeOpenKey (Spec Ambient)
open RegistrationNativeOpenKeyKemGame (other)
open RegistrationNativeOpenKeyKemEarlySource (reference)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let candidate ← $ᵗ MlKemSharedSecret
  observe candidate <$> (simulateQ (reference baseImpl kem selected.val (List.ofFn (selected.insertNth chosen others))
    chosen.1 pair.1 candidate) work).run' ((PqxdhLiveKemBirth.empty, none), ∅)

/-- The actual ordinary CCA uniform branch retains its challenge candidate for the final observation of the same complete closed native client. -/
theorem uniform_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyObservedGame.branch baseImpl kem (other baseImpl kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native work) observe count selected false =ᵈ
      source baseImpl kem work observe count selected := by
  have online := RegistrationNativeKemEarlyObservedSource.branch_source baseImpl kem (other baseImpl kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native work) observe count selected false bounded noReveal
  simp only [RegistrationNativeKemEarlyObservedSource.source, pure_bind, Bool.false_eq_true, ite_false] at online
  refine online.trans ?_
  unfold source
  apply _root_.EvalDistEq.bind_right
  intro chosen
  apply _root_.EvalDistEq.bind_right
  intro others
  apply _root_.EvalDistEq.bind_right
  intro pair
  apply _root_.EvalDistEq.bind_right
  intro candidate
  rw [← QueryImpl.simulateQ_compose]
  change EvalDistEq
    (observe candidate <$> (simulateQ (RegistrationNativeOpenKeyKemEarlySource.implementation baseImpl kem selected.val
      (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 candidate) work).run'
        ((∅, PqxdhLiveKemBirth.empty), none)) _
  rw [RegistrationNativeOpenKeyKemEarlySource.values_source]
  exact .rfl

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedUniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source
