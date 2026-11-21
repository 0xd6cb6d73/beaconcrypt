-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCutMap

/-! The candidate hybrid retains its original result, literal ledger, reached prefix, native poststate and genuine private reservation before applying any Boolean event. The candidate draw follows the entire actual prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State expose)
open RegistrationNativeKemCut (Cut)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

structure Record (ambient : OracleSpec κ) (KemSK Auxiliary Value : Type) where
  cut : Option (Cut ambient KemSK Value)
  reached : State Auxiliary KemSK
  encapsulation : MlKem768Ciphertext × MlKemSharedSecret
  uniform : MlKemSharedSecret
  value : Option Value
  finalState : State Auxiliary KemSK

def Record.candidate (record : Record ambient KemSK Auxiliary Value) (real : Bool) : MlKemSharedSecret :=
  if real then record.encapsulation.2 else record.uniform

def Record.observe (decision : Value → Bool) (record : Record ambient KemSK Auxiliary Value) : Bool :=
  RegistrationNativeKemCutMap.observe decision record.value

noncomputable def run (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) (index : Nat) (real : Bool) :
    ProbComp (Record ambient KemSK Auxiliary Value) := do
  let prefixResult ← (((simulateQ (RegistrationNativeKemGame.stopped baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others))) (expose work index)).run).run before)
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) pair.1 candidate)
    (RegistrationNativeKemCutMap.resume chosen.1 pair.1 candidate prefixResult.1)).run).run prefixResult.2)
  pure ⟨prefixResult.1, prefixResult.2, pair, uniform, result.1.join, result.2⟩

/-- The actual prefix retains the original cut and complete state before a later Boolean decision is mapped onto it. -/
theorem prefix_map {S : Type}
    (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT S ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value) (decision : Value → Bool) (index : Nat) (before : S) :
    (((simulateQ implementation (expose (decision <$> work) index)).run).run before) =
      (fun result => (result.1.map (RegistrationNativeKemCutMap.map decision), result.2)) <$>
        (((simulateQ implementation (expose work index)).run).run before) := by
  simp only [expose, RegistrationNativeKemCutMap.scan_map, simulateQ_map,
    OptionT.run_map, StateT.run_map]

/-- Observing the original optional result commutes with the complete candidate postphase and retains its entire native private state. -/
theorem post_map {S : Type}
    (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT S ProbComp)))
    (decision : Value → Bool) (publicKey : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (cut : Option (Cut ambient KemSK Value)) (before : S) :
    (fun result => (result.1.getD false, result.2)) <$>
      (((simulateQ implementation (RegistrationNativeKemTotalGame.continuation publicKey ciphertext candidate
        (cut.map (RegistrationNativeKemCutMap.map decision)))).run).run before) =
    (fun result => (RegistrationNativeKemCutMap.observe decision result.1.join, result.2)) <$>
      (((simulateQ implementation (RegistrationNativeKemCutMap.resume publicKey ciphertext candidate cut)).run).run before) := by
  rw [RegistrationNativeKemCutMap.resume_observe]
  simp only [simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨none | (none | value), after⟩ <;> rfl

noncomputable def boolRun (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Bool) (before : State Auxiliary KemSK) (index : Nat) (real : Bool) : ProbComp Bool := do
  let prefixResult ← (((simulateQ (RegistrationNativeKemGame.stopped baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others))) (expose work index)).run).run before)
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected.val
    (List.ofFn (selected.insertNth chosen others)) pair.1 candidate)
    (RegistrationNativeKemTotalGame.continuation chosen.1 pair.1 candidate prefixResult.1)).run).run prefixResult.2)
  pure (result.1.getD false)

/-- Applying an arbitrary original-ledger decision after the full observation gives exactly the existing total native candidate continuation. -/
theorem run_observe (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) (index : Nat) (real : Bool)
    (decision : Value → Bool) :
    Record.observe decision <$> run baseImpl kem other selected chosen others work before index real =
      boolRun baseImpl kem other selected chosen others (decision <$> work) before index real := by
  unfold run boolRun
  rw [prefix_map]
  simp only [map_bind, map_pure, bind_map_left]
  apply bind_congr
  intro prefixResult
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  have point := congrArg (Functor.map Prod.fst) (post_map
    (RegistrationNativeKemCandidateSource.source baseImpl kem other selected.val
      (List.ofFn (selected.insertNth chosen others)) pair.1 (if real then pair.2 else uniform))
    decision chosen.1 pair.1 (if real then pair.2 else uniform) prefixResult.1 prefixResult.2)
  simpa only [Functor.map_map, bind_pure_comp, Record.observe, Function.comp_def] using point.symm

structure Outcome (ambient : OracleSpec κ) (KemSK Auxiliary Value : Type) (count : Nat) where
  chosen : MlKem768PublicKey × KemSK
  others : Fin count → MlKem768PublicKey × KemSK
  record : Record ambient KemSK Auxiliary Value

noncomputable def total (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    ProbComp (Outcome ambient KemSK Auxiliary Value count) := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl baseImpl) kem.keygen) count
  let localState ← initial
  let record ← run baseImpl kem other selected chosen others work (localState, PqxdhDynamicKemRouter.empty) index real
  pure ⟨chosen, others, record⟩

/-- The complete genuine-reservation observation projects to the entire candidate source, rather than to an assumed intermediary event. -/
theorem total_observe (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool)
    (decision : Value → Bool) :
    (fun result => result.record.observe decision) <$> total baseImpl kem other initial work count selected index real =
      RegistrationNativeKemCandidateSource.total baseImpl kem other initial (decision <$> work) count selected index real := by
  simp only [total, RegistrationNativeKemCandidateSource.total,
    RegistrationNativeKemTotalChallenge.sourcePrepare, RegistrationNativeKemChallenge.sourcePrepare,
    map_bind, map_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro chosen
  apply bind_congr
  intro others
  apply bind_congr
  intro localState
  simpa only [boolRun, bind_pure_comp] using
    run_observe baseImpl kem other selected chosen others work (localState, PqxdhDynamicKemRouter.empty) index real decision

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.prefix_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.prefix_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.post_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.post_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.run_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.run_observe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.total_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation.total_observe
