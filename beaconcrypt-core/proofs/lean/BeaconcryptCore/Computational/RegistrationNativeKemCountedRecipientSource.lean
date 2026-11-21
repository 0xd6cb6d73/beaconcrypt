-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedReservedRows

/-! The bounded actual counted source has one complete private analysis execution retaining the genuine finite row/cost family and same-reply recipient-error marker. Erasing only that analysis metadata preserves the original source law. Its marker probability has the finite primitive correctness bill, and every reached private handle is attributed to an exact reserved row. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedProgram (Spec evaluate)
open RegistrationNativeKemCountedRecipient (Charged)
open RegistrationNativeKemCountedRecipientSample (Draw)
open RegistrationNativeKemCountedReservation (family reserved IsCreate)
open RegistrationNativeKemCountedRecipientFamily (AnyBad)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def experiment (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) :
    ProbComp ((Fin count → Draw KemSK) × ((Value × Pool KemSK) × Bool)) := do
  let rows ← family setup count
  let result ← (simulateQ (RegistrationNativeRecipientQueryBound.handler (reserved setup (List.ofFn rows))
    (AnyBad setup functional rows)) work).run (PqxdhLiveKemBirth.empty, false)
  pure (rows, ((result.1, result.2.1), result.2.2))

/-- Forgetting only the private reserved family and error flag leaves the complete actual source distribution, including exact costs and private pool. -/
theorem source (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) count) :
    EvalDistEq (evaluate setup.baseImpl setup.kem work PqxdhLiveKemBirth.empty)
      ((fun result => result.2.1) <$> experiment setup functional work count) := by
  have prior := RegistrationNativeKemCountedReservation.complete setup work count bounded PqxdhLiveKemBirth.empty [] rfl
  simp only [RegistrationNativeKemCountedReservation.sample, List.nil_append, bind_map_left] at prior
  have erasure : (family setup count >>= fun rows =>
      (simulateQ (reserved setup (List.ofFn rows)) work).run PqxdhLiveKemBirth.empty) =
      (fun result => result.2.1) <$> experiment setup functional work count := by
    simp only [experiment, map_bind, bind_pure_comp]
    apply bind_congr
    intro rows
    have law := RegistrationNativeRecipientQueryBound.erase (reserved setup (List.ofFn rows))
      (AnyBad setup functional rows) work (PqxdhLiveKemBirth.empty, false)
    simp only [Functor.map_map] at law ⊢
    exact law.symm
  rw [erasure] at prior
  exact prior

/-- The actual same-reply primitive marker is bounded by the finite creation allowance and actual encapsulation allowance. -/
theorem bound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count cap : Nat)
    (bounded : work.IsQueryBoundP (Charged (KemSK := KemSK)) cap) :
    Pr{let result ← experiment setup functional work count}[result.2.2 = true] ≤
      count * cap * RegistrationNativeRecipientFailure.failureRate setup := by
  simpa only [experiment, prEvent_norm] using
    RegistrationNativeKemCountedRecipientFamily.bound setup functional count cap (fun _ => work) (fun _ => bounded)
      (fun _ => PqxdhLiveKemBirth.empty)

/-- A returned actual private handle denotes one genuine row of this very analysis execution, with no public-key injectivity premise. -/
theorem handle (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat) (bounded : work.IsQueryBoundP (IsCreate (KemSK := KemSK)) count)
    (result : (Fin count → Draw KemSK) × ((Value × Pool KemSK) × Bool))
    (supported : result ∈ support (experiment setup functional work count))
    (handle : Nat) (pair : RegistrationNativeKemCountedReservedRows.Pair KemSK)
    (found : result.2.1.2.keys[handle]? = some pair) : ∃ target, (result.1 target).1 = pair := by
  simp only [experiment, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨rows, _sampled, marked, markedSupport, returned⟩ := supported
  cases returned
  have erased : (marked.1, marked.2.1) ∈ support ((simulateQ (reserved setup (List.ofFn rows)) work).run PqxdhLiveKemBirth.empty) := by
    rw [← RegistrationNativeRecipientQueryBound.erase (reserved setup (List.ofFn rows)) (AnyBad setup functional rows)
      work (PqxdhLiveKemBirth.empty, false), support_map]
    exact Set.mem_image_of_mem _ markedSupport
  exact RegistrationNativeKemCountedReservedRows.handle setup count rows work bounded (marked.1, marked.2.1) erased handle pair found
end BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource.handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSource.handle
