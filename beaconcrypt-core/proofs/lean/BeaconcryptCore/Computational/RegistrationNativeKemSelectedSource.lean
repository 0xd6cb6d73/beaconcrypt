-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-! The native on-demand private generated-key service has the exact complete selected-first stopped-source distribution. Actual creation bounds and the native zero-reveal certificate discharge reservation exhaustion and selected-disclosure stopping; no accepted-packet honesty or whole-game simulation is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSelectedSource
open PqxdhKemIndCca (MlKemScheme)
open RegistrationNativeKemInterface (Spec source)
open RegistrationNativeKemReservation (IsCreate)
open RegistrationNativeKemPoolSource (IsReveal project program_source)
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- Actual native generation may be selected first only through this full execution equality, retaining every local field, actual generated pair and callback history. -/
theorem selected_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (work : OracleComp (Spec ambient KemSK) Result)
    (count : Nat) (selected : Fin (count + 1))
    (bounded : work.IsQueryBoundP (IsCreate (ambient := ambient) (KemSK := KemSK)) (count + 1))
    (noReveal : work.IsQueryBoundP (IsReveal (ambient := ambient) (KemSK := KemSK)) 0) (localState : Auxiliary) :
    EvalDistEq
      ((fun result => (some result.1, result.2)) <$>
        (simulateQ (source baseImpl kem ambient other) work).run (localState, PqxdhLiveKemBirth.empty))
      (do let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
          let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
          let pairs := List.ofFn (selected.insertNth chosen others)
          Prod.map id (project pairs) <$>
            (((simulateQ (RegistrationNativeKemGame.stopped baseImpl kem other selected.val pairs) work).run).run
              (localState, PqxdhDynamicKemRouter.empty))) := by
  have same := (RegistrationNativeKemReservation.target_first baseImpl kem other work count selected bounded
      (localState, PqxdhLiveKemBirth.empty)).map
    (fun result => (some result.1, result.2))
  refine same.trans ?_
  simp only [map_bind, PqxdhLiveKemBirth.empty, List.nil_append]
  refine EvalDistEq.bind_right _ fun chosen => ?_
  refine EvalDistEq.bind_right _ fun others => ?_
  have equal := (program_source baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)) work
    (count + 1) bounded noReveal (localState, PqxdhDynamicKemRouter.empty) rfl
    (by simp [PqxdhDynamicKemRouter.empty])).symm
  simp only [project, PqxdhDynamicKemRouter.sourcePool, PqxdhDynamicKemRouter.empty, List.take_zero] at equal ⊢
  rw [equal]

end BeaconcryptCore.Computational.RegistrationNativeKemSelectedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSelectedSource.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSelectedSource.selected_source
