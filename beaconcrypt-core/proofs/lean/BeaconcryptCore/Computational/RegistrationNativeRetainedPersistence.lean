-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRetainedSource

/-! Successful private root memos are persistent. Repeating the same descriptor hits its already cached root; preparing another descriptor cannot erase it. These are actual service receipts for later retained native tokens, rather than an eligibility assumption. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedRoots (Cached)
open RegistrationNativeRetainedSource (State implementation)
open RegistrationNativeRetainedService (Spec)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle RootOutput)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {Value : Type}

def Good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (before : State) : Prop :=
  ∀ message root, before.1 message = some root → Cached source hmac input inside before.2 message root

/-- A successful retained root is exactly the next reply at that descriptor, without another draw or cache change. -/
theorem root_cached (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (root : RootOutput) (cache : HmacOracle.QueryCache)
    (cached : Cached source hmac input inside cache message root) :
    (RegistrationNativeRetainedRoots.root source hmac input inside message).run cache = pure (some root, cache) := by
  obtain ⟨bytes, actual, cached⟩ := cached
  simp only [RegistrationNativeRetainedRoots.root, actual]
  cases selected : inside bytes
  · simp only [selected, Bool.false_eq_true, ite_false] at cached ⊢
    rw [cached]
    rfl
  · simp only [selected, ite_true] at cached ⊢
    obtain ⟨prk, stored, rootValue⟩ := cached
    rw [StateT.run_map, LazyOracleDiscard.query_of_some stored]
    simp only [map_pure, rootValue]

/-- Every actual root callback extends the existing private cache. -/
theorem root_extends (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (before : HmacOracle.QueryCache) (result : Option RootOutput × HmacOracle.QueryCache)
    (reached : result ∈ support ((RegistrationNativeRetainedRoots.root source hmac input inside message).run before)) :
    ∀ bytes prk, before bytes = some prk → result.2 bytes = some prk := by
  simp only [RegistrationNativeRetainedRoots.root] at reached
  cases actual : input message with
  | none =>
      simp only [actual, StateT.run_pure, support_pure] at reached
      subst result
      exact fun _ _ stored => stored
  | some bytes =>
      cases selected : inside bytes
      · simp only [actual, selected, Bool.false_eq_true, ite_false, StateT.run_pure, support_pure] at reached
        subst result
        exact fun _ _ stored => stored
      · simp only [actual, selected, ite_true, StateT.run_map, support_map] at reached
        obtain ⟨queried, possible, equal⟩ := reached
        cases equal
        exact (RegistrationNativeRetainedRoots.query_receipts bytes before queried possible).2

/-- Every successful actual root reply is readable from the reached persistent private cache. -/
theorem root_receipt (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message : Message) (root : RootOutput) (before after : HmacOracle.QueryCache)
    (reached : (some root, after) ∈ support ((RegistrationNativeRetainedRoots.root source hmac input inside message).run before)) :
    Cached source hmac input inside after message root := by
  simp only [RegistrationNativeRetainedRoots.root] at reached
  cases actual : input message with
  | none => simp [actual, StateT.run_pure] at reached
  | some bytes =>
      refine ⟨bytes, actual, ?_⟩
      cases selected : inside bytes
      · simp only [actual, selected, Bool.false_eq_true, ite_false, StateT.run_pure, support_pure] at reached
        rcases reached with ⟨rfl, rfl⟩
        simp []
      · simp only [actual, selected, ite_true, StateT.run_map, support_map] at reached
        obtain ⟨queried, possible, equal⟩ := reached
        simp only [Prod.mk.injEq, Option.some.injEq] at equal
        rcases equal with ⟨rfl, rfl⟩
        simp only [ite_true]
        exact ⟨queried.1, (RegistrationNativeRetainedRoots.query_receipts bytes before queried possible).1, rfl⟩

/-- Successful actual preparation installs precisely its public descriptor's private root receipt. -/
theorem prepared (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (message reference : Message) (before after : State)
    (reached : (some reference, after) ∈ support
      ((implementation source hmac input inside (.inr (.prepare message))).run before)) :
    reference = message ∧ ∃ root, after.1 message = some root ∧ Cached source hmac input inside after.2 message root := by
  simp only [implementation, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨queried, possible, equal⟩ := reached
  change queried ∈ support ((RegistrationNativeRetainedRoots.root source hmac input inside message).run before.2) at possible
  cases rootValue : queried.1 with
  | none => simp [rootValue] at equal
  | some root =>
      simp only [rootValue, Option.map_some, Prod.mk.injEq] at equal
      have same : message = reference := Option.some.inj equal.1
      subst reference
      have afterEq := equal.2
      subst after
      refine ⟨rfl, root, ?_, ?_⟩
      · simp only [Function.update_self]
      · apply root_receipt source hmac input inside message root before.2 queried.2
        have pair : queried = (some root, queried.2) := by
          calc
            queried = (queried.1, queried.2) := Prod.mk.eta.symm
            _ = _ := by rw [rootValue]
        rw [← pair]
        exact possible

/-- Every actual service step preserves all earlier successful descriptor roots, including repeated preparations. -/
theorem query_receipts (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : State) (good : Good source hmac input inside before)
    (result : Spec.Range query × State)
    (reached : result ∈ support ((implementation source hmac input inside query).run before)) :
    Good source hmac input inside result.2 ∧
      ∀ message root, before.1 message = some root → result.2.1 message = some root := by
  cases query with
  | inl coin =>
      simp only [implementation, StateT.run_lift, bind_pure_comp, support_map] at reached
      obtain ⟨reply, _possible, equal⟩ := reached
      cases equal
      exact ⟨good, fun _ _ stored => stored⟩
  | inr query => cases query with
    | demand message =>
        simp only [implementation, StateT.run, support_pure] at reached
        subst result
        exact ⟨good, fun _ _ stored => stored⟩
    | prepare message =>
        simp only [implementation, StateT.run, bind_pure_comp, support_map] at reached
        obtain ⟨queried, possible, equal⟩ := reached
        change queried ∈ support ((RegistrationNativeRetainedRoots.root source hmac input inside message).run before.2) at possible
        cases equal
        constructor
        · intro old root stored
          by_cases same : old = message
          · subst old
            have actual : queried.1 = some root := by simpa only [Function.update_self] using stored
            apply root_receipt source hmac input inside message root before.2 queried.2
            have pair : queried = (some root, queried.2) := by
              calc
                queried = (queried.1, queried.2) := Prod.mk.eta.symm
                _ = _ := by rw [actual]
            rw [← pair]
            exact possible
          · have oldStored : before.1 old = some root := by simpa only [Function.update_of_ne same] using stored
            exact RegistrationNativeRetainedRoots.Cached.mono source hmac input inside before.2 queried.2
              (root_extends source hmac input inside message before.2 queried possible) old root (good old root oldStored)
        · intro old root stored
          by_cases same : old = message
          · subst old
            rw [root_cached source hmac input inside message root before.2 (good message root stored), support_pure] at possible
            cases possible
            exact Function.update_self _ _ _
          · simpa only [Function.update_of_ne same] using stored

/-- Complete adaptive prepare/material programs retain every previously issued private root receipt. -/
theorem program_receipts (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) (before : State) (good : Good source hmac input inside before)
    (result : Value × State)
    (reached : result ∈ support ((simulateQ (implementation source hmac input inside) work).run before)) :
    Good source hmac input inside result.2 ∧
      ∀ message root, before.1 message = some root → result.2.1 message = some root := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure] at reached
      subst result
      exact ⟨good, fun _ _ stored => stored⟩
  | query_bind query next ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query,
        monadLift_self, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨first, possible, later⟩ := reached
      have initial := query_receipts source hmac input inside query before good first possible
      have completed := ih first.1 first.2 initial.1 later
      exact ⟨completed.1, fun message root stored => completed.2 message root (initial.2 message root stored)⟩

/-- The generated empty private memo satisfies the service receipt invariant without an external premise. -/
theorem initial_good (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    Good source hmac input inside RegistrationNativeRetainedSource.initial := by
  intro message root impossible
  simp [RegistrationNativeRetainedSource.initial] at impossible

/-- Actual initialized adaptive execution derives all retained memo/cache receipts. -/
theorem initialized_program (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Value) (result : Value × State)
    (reached : result ∈ support ((simulateQ (implementation source hmac input inside) work).run
      RegistrationNativeRetainedSource.initial)) : Good source hmac input inside result.2 :=
  (program_receipts source hmac input inside work _ (initial_good source hmac input inside) result reached).1

end BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.root_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.root_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.root_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.root_extends
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.root_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.root_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.prepared
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.query_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.query_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.program_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.program_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.initial_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.initial_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.initialized_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRetainedPersistence.initialized_program
