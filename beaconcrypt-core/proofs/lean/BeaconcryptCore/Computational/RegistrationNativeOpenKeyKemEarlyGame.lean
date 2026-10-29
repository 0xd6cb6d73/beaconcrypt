-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame
import BeaconcryptCore.Computational.RegistrationNativeKemEarlySource

/-! The actual open G2 key-table client has an early ordinary-CCA replacement. Its selected exact-ciphertext decapsulation is covered from genuine birth, even before the selected getter. The same original indexed create/no-reveal bills supply reservation; no activity, temporal eligibility, or source-equivalence premise is introduced. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyGame
open PqxdhKemIndCca
open RegistrationNativeOpenKey (Ambient NativeSpec)
open RegistrationNativeOpenKeyKemGame (other normal)
variable {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def adversary (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (NativeSpec KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) : OneKeyAdversary kem :=
  RegistrationNativeKemEarlyGame.adversary baseImpl kem (other baseImpl kem) (pure ∅) work count selected

noncomputable def uniform (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (work : OracleComp (NativeSpec KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool :=
  RegistrationNativeKemEarlyGame.branch baseImpl kem (other baseImpl kem) (pure ∅) work count selected false

/-- The complete actual G2 native program pays exactly one concrete ordinary CCA advantage and one unconditional correctness error for its early challenge. -/
theorem normal_close (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (work : OracleComp (NativeSpec KemSK) Bool) (count : Nat) (selected : Fin (count + 1))
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    (normal baseImpl kem work).boolDistance (uniform baseImpl kem work count selected) ≤
      (kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (adversary baseImpl kem work count selected).toINDCCA).toReal +
      RegistrationNativeKemEarlyCorrectness.correctnessError baseImpl kem := by
  have source := RegistrationNativeOpenKeyKemGame.normal_source baseImpl kem work count selected bounded noReveal
  have equal := source.prEvent_eq (fun result => result = true)
  have bound := RegistrationNativeKemEarlySource.source_close baseImpl kem functional (other baseImpl kem) (pure ∅) work count selected
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, ← equal, uniform, adversary] using bound

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyGame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyGame.normal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyGame.normal_close
