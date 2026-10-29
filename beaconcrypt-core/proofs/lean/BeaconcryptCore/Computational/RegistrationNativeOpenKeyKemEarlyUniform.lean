-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlySource
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyGame

/-! The ordinary early-CCA uniform branch has its literal closed-provider/key-table source. Actual key generation, selected reservation, challenge ciphertext, uniform candidate and all inactive or mismatched executions remain in the same experiment. Reassociation changes no client observation or target multiplicity. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyUniform
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeOpenKey (Spec Ambient)
open RegistrationNativeOpenKeyKemGame (other)
open RegistrationNativeOpenKeyKemEarlySource (reference)
variable {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let candidate ← $ᵗ MlKemSharedSecret
  (simulateQ (reference baseImpl kem selected.val (List.ofFn (selected.insertNth chosen others))
    chosen.1 pair.1 candidate) work).run' ((PqxdhLiveKemBirth.empty, none), ∅)

/-- The actual bounded early uniform KEM branch is the same complete observation after closing the exact candidate provider and lazy108 table. -/
theorem uniform_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (Spec KemSK) Bool) (count : Nat) (selected : Fin (count + 1))
    (bounded : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : (simulateQ RegistrationNativeOpenKey.native work).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeOpenKeyKemEarlyGame.uniform baseImpl kem (simulateQ RegistrationNativeOpenKey.native work) count selected =ᵈ
      source baseImpl kem work count selected := by
  have online := RegistrationNativeKemEarlyOnline.branch_online baseImpl kem (other baseImpl kem) (pure ∅)
    (simulateQ RegistrationNativeOpenKey.native work) count selected false bounded noReveal
  simp only [pure_bind, Bool.false_eq_true, ite_false] at online
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
    ((simulateQ (RegistrationNativeOpenKeyKemEarlySource.implementation baseImpl kem selected.val
      (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 candidate) work).run'
        ((∅, PqxdhLiveKemBirth.empty), none)) _
  rw [RegistrationNativeOpenKeyKemEarlySource.values_source]
  exact .rfl
end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyUniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyUniform.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyUniform.uniform_source
