-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedHistorySchedule

/-! Successful seed disclosures at native and ordinary generated indices are the same events. Rejected future-index requests do not compromise identities created later, and caller-known imports do not become ordinary target disclosures. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals
open PqxdhJointIdentity PqxdhDynamicIdentityPool
open PqxdhRegistrationJointIdentityRouting (Ref Registry State)
open PqxdhRegistrationJointRoutedHistory (Tracked lookup_append)

def revealAt (index : Nat) (observation : Observation) : Bool :=
  match observation with
  | ⟨.inr (.reveal selected), some _⟩ => selected == index
  | _ => false

def revealedAt (index : Nat) (transcript : List Observation) : Bool :=
  transcript.any (revealAt index)

/-- Chronological disclosures remain recorded through all later observations. -/
theorem append (index : Nat) (before after : List Observation) :
    revealedAt index (before ++ after) = (revealedAt index before || revealedAt index after) := by
  simp [revealedAt]

structure Recorded (state : State) : Prop where
  sourceFuture : ∀ index, state.1.refs.length ≤ index → revealedAt index state.1.transcript = false
  targetFuture : ∀ index, state.2.seeds.length ≤ index → revealedAt index state.2.transcript = false
  generated : ∀ index target, state.1.refs[index]? = some (.generated target) →
    revealedAt index state.1.transcript = revealedAt target state.2.transcript

/-- No identity is disclosed in the actual empty initial states. -/
theorem initial : Recorded (⟨[], []⟩, initialState) := by
  constructor <;> simp [revealedAt, initialState]

/-- Actual creation preserves prior disclosure state and does not inherit rejected guesses of the new handle. -/
theorem created (joint : Primitives) (state : State) (seed : IdentitySeed) (before : Recorded state) :
    Recorded (PqxdhRegistrationJointIdentityRouting.record (.inr .create)
      (some (state.1.refs.length, joint.publicKeys seed))
      { state.1 with refs := state.1.refs ++ [.generated state.2.seeds.length] },
      (createdReply joint state.2 seed).2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro index future
    simpa [PqxdhRegistrationJointIdentityRouting.record, revealedAt, revealAt] using
      before.sourceFuture index (by
        simp only [PqxdhRegistrationJointIdentityRouting.record, List.length_append, List.length_singleton] at future
        omega)
  · intro index future
    simpa [createdReply, record, revealedAt, revealAt] using before.targetFuture index (by
      simp only [createdReply, record, List.length_append, List.length_singleton] at future
      omega)
  · intro index target found
    rcases (lookup_append state.1.refs (.generated state.2.seeds.length) (.generated target) index).mp found with
      previous | ⟨rfl, same⟩
    · simpa [PqxdhRegistrationJointIdentityRouting.record, createdReply, record, revealedAt, revealAt]
        using before.generated index target previous
    · have equal := Ref.generated.inj same
      subst target
      simpa [PqxdhRegistrationJointIdentityRouting.record, createdReply, record, revealedAt, revealAt]
        using (before.sourceFuture state.1.refs.length (Nat.le_refl _)).trans
          (before.targetFuture state.2.seeds.length (Nat.le_refl _)).symm

/-- Caller-known imports leave all generated disclosure histories unchanged. -/
theorem imported (joint : Primitives) (state : State) (seed : IdentitySeed) (before : Recorded state) :
    Recorded ((PqxdhRegistrationJointIdentityRouting.imported joint seed state.1).2, state.2) := by
  refine ⟨?_, before.targetFuture, ?_⟩
  · intro index future
    exact before.sourceFuture index (by
      simp only [PqxdhRegistrationJointIdentityRouting.imported, List.length_append, List.length_singleton] at future
      omega)
  · intro index target found
    exact before.generated index target (by
      simpa [PqxdhRegistrationJointIdentityRouting.imported, lookup_append] using found)

/-- Retain both complete audit tails while checking their disclosure projections. -/
theorem audit (state : State) (before : Recorded state) (sourceTail targetTail : List Observation)
    (sourceFuture : ∀ index, state.1.refs.length ≤ index → revealedAt index sourceTail = false)
    (targetFuture : ∀ index, state.2.seeds.length ≤ index → revealedAt index targetTail = false)
    (generated : ∀ index target, state.1.refs[index]? = some (.generated target) →
      revealedAt index sourceTail = revealedAt target targetTail) :
    Recorded ({ state.1 with transcript := state.1.transcript ++ sourceTail },
      { state.2 with transcript := state.2.transcript ++ targetTail }) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun index future => by simp only [append, before.sourceFuture index future, sourceFuture index future, Bool.or_false]
  · exact fun index future => by simp only [append, before.targetFuture index future, targetFuture index future, Bool.or_false]
  · exact fun index target found => by rw [append, append, before.generated index target found, generated index target found]

/-- Forwarded reveals disclose exactly the mapped identity in both audits, including optional rejection. -/
theorem generated_reveal (state : State) (tracked : Tracked state) (before : Recorded state)
    (index target : Nat) (found : state.1.refs[index]? = some (.generated target))
    (answer : Option IdentitySeed) :
    Recorded (PqxdhRegistrationJointIdentityRouting.record (.inr (.reveal index)) answer state.1,
      record (.inr (.reveal target)) answer state.2) := by
  refine audit state before [⟨.inr (.reveal index), answer⟩] [⟨.inr (.reveal target), answer⟩] ?_ ?_ ?_
  case refine_3 =>
    intro other otherTarget otherFound
    have same : index = other ↔ target = otherTarget := by
      constructor
      · intro equal
        subst other
        simpa [found] using otherFound
      · intro equal
        subst otherTarget
        exact tracked.unique index other target found otherFound
    cases answer <;> simp [revealedAt, revealAt, same]
  case refine_1 =>
    intro other future
    have earlier : index < state.1.refs.length := (List.getElem?_eq_some_iff.mp found).1
    have different : index ≠ other := by omega
    cases answer <;> simp [revealedAt, revealAt, different]
  case refine_2 =>
    intro other future
    have earlier := tracked.valid target (List.mem_of_getElem? found)
    have different : target ≠ other := by omega
    cases answer <;> simp [revealedAt, revealAt, different]

/-- Coins, signing, DH and rejected disclosures preserve the revelation relation while retaining their full audit entries. -/
theorem silent (state : State) (before : Recorded state) (sourceTail targetTail : List Observation)
    (sourceSilent : ∀ index, revealedAt index sourceTail = false)
    (targetSilent : ∀ index, revealedAt index targetTail = false) :
    Recorded ({ state.1 with transcript := state.1.transcript ++ sourceTail },
      { state.2 with transcript := state.2.transcript ++ targetTail }) :=
  audit state before sourceTail targetTail (fun index _ => sourceSilent index)
    (fun index _ => targetSilent index)
    (fun index target _ => (sourceSilent index).trans (targetSilent target).symm)

/-- Revealing a caller-known import never discloses a distinct generated handle. -/
theorem known_reveal (state : State) (before : Recorded state) (index : Nat) (seed : IdentitySeed)
    (found : state.1.refs[index]? = some (.known seed)) (answer : Option IdentitySeed) :
    Recorded (PqxdhRegistrationJointIdentityRouting.record (.inr (.reveal index)) answer state.1, state.2) := by
  suffices extended : Recorded ({ state.1 with transcript := state.1.transcript ++ [⟨.inr (.reveal index), answer⟩] },
      { state.2 with transcript := state.2.transcript ++ [] }) by
    simp only [List.append_nil] at extended
    cases state with
    | mk registry source => cases source; exact extended
  refine audit state before [⟨.inr (.reveal index), answer⟩] [] ?_ (by simp [revealedAt]) ?_
  · intro other future
    have earlier : index < state.1.refs.length := (List.getElem?_eq_some_iff.mp found).1
    have different : index ≠ other := by omega
    cases answer <;> simp [revealedAt, revealAt, different]
  · intro other target otherFound
    have different : index ≠ other := by
      intro equal
      subst other
      simp [found] at otherFound
    cases answer <;> simp [revealedAt, revealAt, different]

/-- An ordinary native audit entry with no disclosure leaves all generated freshness flags unchanged. -/
theorem source_silent (state : State) (before : Recorded state)
    (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (quiet : ∀ index, revealAt index ⟨query, answer⟩ = false) :
    Recorded (PqxdhRegistrationJointIdentityRouting.record query answer state.1, state.2) := by
  have extended := silent state before [⟨query, answer⟩] []
    (by simp [revealedAt, quiet]) (by simp [revealedAt])
  rcases state with ⟨registry, ⟨seeds, transcript⟩⟩
  simpa only [List.append_nil, PqxdhRegistrationJointIdentityRouting.record, record] using extended

/-- An ambient ordinary query that discloses no identity leaves the native freshness state intact. -/
theorem target_silent (state : State) (before : Recorded state)
    (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query)
    (quiet : ∀ index, revealAt index ⟨query, answer⟩ = false) :
    Recorded (state.1, record query answer state.2) := by
  have extended := silent state before [] [⟨query, answer⟩]
    (by simp [revealedAt]) (by simp [revealedAt, quiet])
  rcases state with ⟨⟨refs, transcript⟩, source⟩
  simpa only [List.append_nil, PqxdhRegistrationJointIdentityRouting.record, record] using extended

end BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.initial

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.created

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.imported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.imported

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.audit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.audit

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.generated_reveal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.generated_reveal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.silent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.silent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.known_reveal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.known_reveal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.source_silent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.source_silent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.target_silent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointRoutedReveals.target_silent
