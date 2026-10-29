-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKey
import BeaconcryptCore.Computational.RegistrationNativeKemTotalSource
import BeaconcryptCore.Computational.RegistrationNativeKemReservation
import BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-! The open native G2 client uses an actual lazy uniform108 table beside an external indexed KEM service. Its selected KEM reduction retains that complete table in its private context. Ordinary encapsulation remains real, generated keys are private to the service, and the total challenge branch includes inactive and mismatched first-getter executions. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame
open PqxdhKemIndCca
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeOpenKey (Ambient NativeSpec)
variable {ι KemSK : Type} {base : OracleSpec ι}

abbrev Table := (Pqxdh.Bytes →ₒ PqxdhServerAuthKeySchedule.Output).QueryCache

noncomputable def other (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) : QueryImpl Ambient (StateT Table ProbComp)
  | .inl query => PqxdhRegistrationJointKemSecondEntry.lazyImpl query
  | .inr (.inl query) => StateT.lift (RegistrationNativePublicInterpreter.unavailable query)
  | .inr (.inr key) => StateT.lift
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key))

noncomputable def normal (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (work : OracleComp (NativeSpec KemSK) Bool) : ProbComp Bool :=
  (simulateQ (RegistrationNativeKemInterface.source baseImpl kem Ambient (other baseImpl kem)) work).run'
    (∅, PqxdhLiveKemBirth.empty)

noncomputable def adversary (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (work : OracleComp (NativeSpec KemSK) Bool)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : OneKeyAdversary kem :=
  RegistrationNativeKemTotalGame.adversary baseImpl kem (other baseImpl kem) (pure ∅) work count selected index

noncomputable def uniform (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (work : OracleComp (NativeSpec KemSK) Bool)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : ProbComp Bool :=
  RegistrationNativeKemTotalGame.branch baseImpl kem (other baseImpl kem) (pure ∅) work count selected index false

/-- Honest on-demand indexed keys and the genuine reserved selected-key source have the same complete client decision. -/
theorem normal_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (work : OracleComp (NativeSpec KemSK) Bool)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    EvalDistEq (normal baseImpl kem work)
      (RegistrationNativeKemTotalSource.source baseImpl kem (other baseImpl kem) (pure ∅) work count selected) := by
  have reserved := (RegistrationNativeKemReservation.target_first baseImpl kem (other baseImpl kem) work count selected
    (bounded.mono (Nat.le_succ count)) (∅, PqxdhLiveKemBirth.empty)).map Prod.fst
  have staged : EvalDistEq (normal baseImpl kem work) (do
      let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen
      let others ← PqxdhLiveKemSelection.sampleFamily
        (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen) count
      Prod.fst <$> (simulateQ (RegistrationNativeKemReservation.reserved baseImpl kem (other baseImpl kem)
        (List.ofFn (selected.insertNth chosen others))) work).run (∅, PqxdhLiveKemBirth.empty)) := by
    simpa only [normal, StateT.run'_eq, map_bind, PqxdhLiveKemBirth.empty, List.nil_append] using reserved
  refine staged.trans ?_
  unfold RegistrationNativeKemTotalSource.source
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro chosen _generated
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro others _sampled
  simp only [pure_bind]
  have step := congrArg (fun distribution => (fun result => result.1.getD false) <$> distribution)
    (RegistrationNativeKemPoolSource.program_source baseImpl kem (other baseImpl kem) selected.val
      (List.ofFn (selected.insertNth chosen others)) work count bounded noReveal
      (∅, PqxdhDynamicKemRouter.empty) rfl (by simp [PqxdhDynamicKemRouter.empty]))
  simp only [Functor.map_map, Prod.map_def, id_eq, Option.getD_some,
    RegistrationNativeKemPoolSource.project, PqxdhDynamicKemRouter.sourcePool,
    PqxdhDynamicKemRouter.empty, List.take_zero] at step
  have observed : Prod.fst <$>
      (simulateQ (RegistrationNativeKemReservation.reserved baseImpl kem (other baseImpl kem)
        (List.ofFn (selected.insertNth chosen others))) work).run (∅, PqxdhLiveKemBirth.empty) = (do
      let result ← (((simulateQ (RegistrationNativeKemGame.stopped baseImpl kem (other baseImpl kem) selected.val
        (List.ofFn (selected.insertNth chosen others))) work).run).run (∅, PqxdhDynamicKemRouter.empty))
      pure (result.1.getD false)) := by
    simpa only [bind_pure_comp, PqxdhLiveKemBirth.empty, PqxdhDynamicKemRouter.empty] using step.symm
  rw [observed]

/-- The whole actual open G2 client pays one ordinary KEM CCA advantage and correctness error, with no target-mark or challenge-admissibility premise. -/
theorem normal_close (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (work : OracleComp (NativeSpec KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := Ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := Ambient) (KemSK := KemSK)) 0) :
    (normal baseImpl kem work).boolDistance (uniform baseImpl kem work count selected index) ≤
      (kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (adversary baseImpl kem work count selected index).toINDCCA).toReal +
      RegistrationNativeKemTotalCorrectness.correctnessError baseImpl kem := by
  have original := normal_source baseImpl kem work count selected bounded noReveal
  have reconstructed := RegistrationNativeKemTotalSource.source_real baseImpl kem (other baseImpl kem) (pure ∅) work count selected index
  have event := (original.trans reconstructed.symm).prEvent_eq (fun result => result = true)
  have bound := RegistrationNativeKemTotalCorrectness.source_close baseImpl kem functional (other baseImpl kem)
    (pure ∅) work count selected index
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton, event, uniform, adversary] using bound

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame.normal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame.normal_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame.normal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemGame.normal_close
