-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemRecipientLogSource

/-! Every reserved genuine row/cost is an actual source key-generation support point. The same complete lower capability log and private pool remain reachable in the actual counted source, including every adaptive continuation and fallback creation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemCountedProgram (Spec handler)
open RegistrationNativeKemCountedReservation (reserved family)
open RegistrationNativeKemCountedRecipientSample (Draw generation)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

def Genuine (setup : Setup base KemSK) (tape : List (Draw KemSK)) : Prop :=
  ∀ drawn ∈ tape, drawn ∈ support (generation setup)

/-- Every member of the actual finite row/cost sample is a genuine primitive generation reply with its original cost. -/
theorem sampled (setup : Setup base KemSK) (count : Nat) (rows : Fin count → Draw KemSK)
    (supported : rows ∈ support (family setup count)) : Genuine setup (List.ofFn rows) := by
  have coordinate : ∀ target, rows target ∈ support (generation setup) := by
    induction count with
    | zero => exact fun target => Fin.elim0 target
    | succ count ih =>
      simp only [family, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨drawn, generated, rest, remaining, rfl⟩ := supported
      intro target
      exact Fin.cases generated (fun index => ih rest remaining index) target
  intro drawn member
  obtain ⟨target, rfl⟩ := List.mem_ofFn.mp member
  exact coordinate target

/-- Every reserved query reply, entire reached private pool and draw cost also belong to the literal actual counted source query. -/
theorem query (setup : Setup base KemSK) (tape : List (Draw KemSK)) (genuine : Genuine setup tape)
    (request : (Spec KemSK).Domain) (before : Pool KemSK)
    (result : (Spec KemSK).Range request × Pool KemSK)
    (supported : result ∈ support ((reserved setup tape request).run before)) :
    result ∈ support ((handler setup.baseImpl setup.kem request).run before) := by
  rcases request with uniform | (pool | key) <;> try exact supported
  cases pool with
  | decapsulate handle ciphertext => exact supported
  | reveal handle => exact supported
  | create =>
    cases found : tape[before.keys.length]? with
    | none => simpa only [reserved, StateT.run, found] using supported
    | some drawn =>
      simp only [reserved, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rw [handler, RegistrationNativeKemCountedRecipientSample.actual_create, support_map]
      exact ⟨drawn, genuine drawn (List.mem_of_getElem? found), rfl⟩

/-- The exact complete result and private pool of any adaptive reserved execution remain reachable in the actual source. This also applies when the returned value retains the full query/reply log. -/
theorem program (setup : Setup base KemSK) (tape : List (Draw KemSK)) (genuine : Genuine setup tape)
    (work : OracleComp (Spec KemSK) Value) (before : Pool KemSK) (result : Value × Pool KemSK)
    (supported : result ∈ support ((simulateQ (reserved setup tape) work).run before)) :
    result ∈ support (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work before) := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value => exact supported
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨reply, middle⟩, head, tail⟩ := supported
    simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff]
    exact ⟨(reply, middle), query setup tape genuine request before (reply, middle) head,
      ih reply middle result tail⟩

/-- Every initialized analysis sample retains a capability log of one literal actual counted source execution with the same output and entire final private pool. -/
theorem logged (setup : Setup base KemSK) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (work : OracleComp (Spec KemSK) Value) (count : Nat)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK Value count)
    (supported : result ∈ support (RegistrationNativeKemRecipientLogSource.experiment setup functional work count)) :
    (result.2.1.1, result.2.1.2) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work.withQueryLog PqxdhLiveKemBirth.empty) := by
  simp only [RegistrationNativeKemRecipientLogSource.experiment, RegistrationNativeKemCountedRecipientSource.experiment,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨rows, sampledRows, marked, reached, returned⟩ := supported
  cases returned
  have erased : (marked.1, marked.2.1) ∈ support
      ((simulateQ (reserved setup (List.ofFn rows)) work.withQueryLog).run PqxdhLiveKemBirth.empty) := by
    rw [← RegistrationNativeRecipientQueryBound.erase (reserved setup (List.ofFn rows))
      (RegistrationNativeKemCountedRecipientFamily.AnyBad setup functional rows) work.withQueryLog
      (PqxdhLiveKemBirth.empty, false), support_map]
    exact Set.mem_image_of_mem _ reached
  exact program setup (List.ofFn rows) (sampled setup count rows sampledRows) work.withQueryLog
    PqxdhLiveKemBirth.empty (marked.1, marked.2.1) erased

end BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.sampled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.sampled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport.logged
