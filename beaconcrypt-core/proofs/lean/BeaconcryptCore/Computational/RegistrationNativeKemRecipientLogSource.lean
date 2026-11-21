-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource
import BeaconcryptCore.Computational.RegistrationNativeRecipientLog

/-! The complete adaptive recipient experiment retains its literal counted capability log. Erasure drops only this analysis log, the same resource cap gives the honest-recipient failure bound, and bad logged replies trigger that execution's marker. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativeKemCountedRecipient (Charged)
open RegistrationNativeKemCountedRecipientSample (Draw)
open RegistrationNativeKemCountedReservation (reserved IsCreate)
open RegistrationNativeKemCountedRecipientFamily (AnyBad)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
abbrev Log (KemSK : Type) := (Spec KemSK).QueryLog
abbrev Result (KemSK Value : Type) (count : Nat) :=
  (Fin count → Draw KemSK) × ((((Value × Log KemSK) × Pool KemSK)) × Bool)

def erase {count : Nat} (result : Result KemSK Value count) :
    (Fin count → Draw KemSK) × ((Value × Pool KemSK) × Bool) :=
  (result.1, ((result.2.1.1.1, result.2.1.2), result.2.2))

noncomputable def experiment (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) : ProbComp (Result KemSK Value count) :=
  RegistrationNativeKemCountedRecipientSource.experiment setup functional work.withQueryLog count

/-- Erasing only the capability log retains the genuine family, actual complete output and pool, and actual sticky marker. -/
theorem erasure (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) :
    erase <$> experiment setup functional work count =
      RegistrationNativeKemCountedRecipientSource.experiment setup functional work count := by
  simp only [experiment, RegistrationNativeKemCountedRecipientSource.experiment, map_bind, bind_pure_comp]
  apply bind_congr
  intro rows
  have same := congrArg (fun program => (simulateQ (RegistrationNativeRecipientQueryBound.handler
      (reserved setup (List.ofFn rows)) (AnyBad setup functional rows)) program).run (PqxdhLiveKemBirth.empty, false))
    (loggingOracle.fst_map_run_simulateQ work)
  simp only [simulateQ_map, StateT.run_map] at same
  have packed := congrArg (fun distribution =>
    (fun value => (rows, ((value.1, value.2.1), value.2.2))) <$> distribution) same
  simp only [Functor.map_map] at packed ⊢
  exact packed

/-- Logging is syntactically transparent to the actual encapsulation cap and its finite honest-recipient failure bill. -/
theorem bound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count cap : Nat)
    (bounded : work.IsQueryBoundP (Charged (KemSK := KemSK)) cap) :
    Pr{let result ← experiment setup functional work count}[result.2.2 = true] ≤
      count * cap * RegistrationNativeRecipientFailure.failureRate setup := by
  apply RegistrationNativeKemCountedRecipientSource.bound
  exact (isQueryBoundP_iff_of_map_eq (p := Charged) (loggingOracle.fst_map_run_simulateQ work)).mpr bounded

/-- Every bad actual entry in the retained log sets this same experiment's final sticky marker. -/
theorem sound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) (result : Result KemSK Value count)
    (supported : result ∈ support (experiment setup functional work count))
    (entry : (query : (Spec KemSK).Domain) × (Spec KemSK).Range query)
    (member : entry ∈ result.2.1.1.2) (bad : AnyBad setup functional result.1 entry.1 entry.2) :
    result.2.2 = true := by
  simp only [experiment, RegistrationNativeKemCountedRecipientSource.experiment,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨rows, _sampled, marked, reached, returned⟩ := supported
  cases returned
  exact (RegistrationNativeRecipientLog.sound (reserved setup (List.ofFn rows))
    (AnyBad setup functional rows) work (PqxdhLiveKemBirth.empty, false)
    marked.1.1 marked.1.2 marked.2 reached).2 entry member bad

/-- Every actual returned handle is still attributed to an exact sampled family row after retaining the capability log. -/
theorem handle (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) count)
    (result : Result KemSK Value count) (supported : result ∈ support (experiment setup functional work count))
    (handle : Nat) (pair : RegistrationNativeKemCountedReservedRows.Pair KemSK)
    (found : result.2.1.2.keys[handle]? = some pair) : ∃ target, (result.1 target).1 = pair := by
  apply RegistrationNativeKemCountedRecipientSource.handle setup functional work.withQueryLog count
    ((isQueryBoundP_iff_of_map_eq (p := IsCreate) (loggingOracle.fst_map_run_simulateQ work)).mpr bounded)
    result supported handle pair found

end BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.sound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource.handle
