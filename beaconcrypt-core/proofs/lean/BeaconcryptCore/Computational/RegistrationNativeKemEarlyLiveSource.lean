-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyCandidateSource
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateReservedProgram

/-! The early ordinary CCA experiment has a total live-pool source under the original actual create/no-reveal caps. Candidate substitution is already active before the first getter; every absent-handle reply and every private history entry is retained. Artificial router stopping is eliminated by the derived per-prefix capacity bill, rather than by an event hypothesis. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyLiveSource
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  (simulateQ (RegistrationNativeKemCandidateReserved.reserved baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) pair.1 candidate)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 candidate work)).run' (localState, PqxdhLiveKemBirth.empty)

/-- Both actual early CCA branches are their explicit total live-pool source on the original bounded non-revealing client. -/
theorem branch_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (real : Bool)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemReservation.IsCreate (ambient := ambient) (KemSK := KemSK)) count)
    (noReveal : work.IsQueryBoundP (RegistrationNativeKemPoolSource.IsReveal (ambient := ambient) (KemSK := KemSK)) 0) :
    RegistrationNativeKemEarlyGame.branch baseImpl kem other initial work count selected real =
      source baseImpl kem other initial work count selected real := by
  rw [RegistrationNativeKemEarlyCandidateSource.branch_source]
  unfold RegistrationNativeKemEarlyCandidateSource.source source
  simp only [RegistrationNativeKemTotalChallenge.sourcePrepare, RegistrationNativeKemEarlySource.empty_prepare,
    bind_assoc, pure_bind]
  apply bind_congr
  intro chosen
  apply bind_congr
  intro others
  apply bind_congr
  intro localState
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  have actual := RegistrationNativeKemCandidateReservedProgram.program_source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) pair.1 (if real then pair.2 else uniform)
    (RegistrationNativeKemEarlyGame.intercept chosen.1 pair.1 (if real then pair.2 else uniform) work) count
    (RegistrationNativeKemEarlyBudget.create_bound _ _ _ work count bounded)
    (RegistrationNativeKemEarlyBudget.reveal_bound _ _ _ work 0 noReveal)
    (localState, PqxdhDynamicKemRouter.empty) rfl (by simp [PqxdhDynamicKemRouter.empty])
  have mapped := congrArg (Functor.map (fun result => result.1.getD false)) actual
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map_def, id_eq,
    RegistrationNativeKemPoolSource.project, PqxdhDynamicKemRouter.sourcePool, PqxdhDynamicKemRouter.empty,
    PqxdhLiveKemBirth.empty, List.take_zero, Option.getD_some, bind_pure_comp] using mapped

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyLiveSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyLiveSource.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyLiveSource.branch_source
