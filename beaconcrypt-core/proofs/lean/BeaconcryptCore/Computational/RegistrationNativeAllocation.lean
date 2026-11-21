-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWire

/-! Allocation-aware output publication. The two callbacks share arbitrary state and randomness, so failed reservations and failed serializations retain their effects and later attempts continue from them. This is a supplementary semantics for `wire::encode_record`; the actual Rust wrapper/codec source correspondence and its integration into `RegistrationNativeExperiment` remain separate obligations. -/

open OracleComp
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.RegistrationNativeAllocation

variable {σ : Type}
abbrev Bytes := Pqxdh.Bytes
abbrev M (σ : Type) := StateT σ ProbComp

/-- Reserve before zero initialization and serialization; publish only a nonzero serializer result, with the same truncation rule as `Vec::truncate`. -/
def encodeRecord (reserve : Nat → M σ Bool) (serialize : Bytes → M σ (Nat × Bytes))
    (capacity : Nat) : M σ (Option Bytes) := do
  let admitted ← reserve capacity
  if !admitted then return none
  let result ← serialize (List.replicate capacity 0)
  return if result.1 = 0 then none else some (result.2.take result.1)

/-- The complete joint distribution keeps the post-reservation state on rejection and passes that same state to serialization on success. -/
theorem run (reserve : Nat → M σ Bool) (serialize : Bytes → M σ (Nat × Bytes))
    (capacity : Nat) (before : σ) :
    (encodeRecord reserve serialize capacity).run before = (do
      let allocation ← (reserve capacity).run before
      if !allocation.1 then pure (none, allocation.2)
      else do
        let result ← (serialize (List.replicate capacity 0)).run allocation.2
        pure ((if result.1.1 = 0 then none else some (result.1.2.take result.1.1)), result.2)) := by
  simp only [encodeRecord, StateT.run_bind]
  congr 1
  funext allocation
  cases allocation.1 <;> rfl

/-- Allocation failure publishes nothing while retaining all allocator effects; serialization is not run. -/
theorem reservation_failure (reserve : Nat → M σ Bool) (serialize : Bytes → M σ (Nat × Bytes))
    (capacity : Nat) (before after : σ)
    (rejected : (reserve capacity).run before = pure (false, after)) :
    (encodeRecord reserve serialize capacity).run before = pure (none, after) := by
  simp [run, rejected]

/-- Random allocator effects are retained jointly with failure; no fixed deterministic reply function is required. -/
theorem reservation_failure_distribution (reserve : Nat → M σ Bool)
    (serialize : Bytes → M σ (Nat × Bytes)) (capacity : Nat) (before : σ)
    (effects : ProbComp σ)
    (rejected : (reserve capacity).run before = (fun after => (false, after)) <$> effects) :
    (encodeRecord reserve serialize capacity).run before = (fun after => (none, after)) <$> effects := by
  simp [run, rejected]

/-- Even a serializer that reports failure can update shared platform state; the failed buffer is discarded, while those effects remain. -/
theorem serialization_failure_distribution (reserve : Nat → M σ Bool)
    (serialize : Bytes → M σ (Nat × Bytes)) (capacity : Nat) (before allocated : σ)
    (effects : ProbComp (Bytes × σ))
    (accepted : (reserve capacity).run before = pure (true, allocated))
    (failed : (serialize (List.replicate capacity 0)).run allocated =
      (fun result => ((0, result.1), result.2)) <$> effects) :
    (encodeRecord reserve serialize capacity).run before = (fun result => (none, result.2)) <$> effects := by
  simp [run, accepted, failed]

/-- The old deterministic successful-allocation interpretation is recovered as a special case. -/
theorem pure_compatibility (serialize : Bytes → Nat × Bytes) (capacity : Nat) (before : σ) :
    (encodeRecord (fun _ => pure true) (fun bytes => pure (serialize bytes)) capacity).run before =
      pure ((let result := serialize (List.replicate capacity 0)
        if result.1 = 0 then none else some (result.2.take result.1)), before) := by
  simp [run, StateT.run_pure]

/-- A concrete platform schedule for demonstrating retries; each reservation is recorded whether or not it succeeds. -/
structure Schedule where
  outcomes : List Bool
  reservations : List Nat
  serializations : Nat

def scheduledReserve (capacity : Nat) : M Schedule Bool := fun before =>
  pure (before.outcomes.headD false,
    { before with outcomes := before.outcomes.tail, reservations := before.reservations ++ [capacity] })

def fixedSerialize (written : Nat) (bytes : Bytes) (_ : Bytes) : M Schedule (Nat × Bytes) := fun before =>
  pure ((written, bytes), { before with serializations := before.serializations + 1 })

theorem scheduledReserve_run (capacity : Nat) (before : Schedule) :
    (scheduledReserve capacity).run before = pure (before.outcomes.headD false,
      { before with outcomes := before.outcomes.tail, reservations := before.reservations ++ [capacity] }) := rfl

theorem fixedSerialize_run (written : Nat) (bytes input : Bytes) (before : Schedule) :
    (fixedSerialize written bytes input).run before =
      pure ((written, bytes), { before with serializations := before.serializations + 1 }) := rfl

/-- One admitted message may fail allocation and then succeed on retry. Both reservations and all earlier history survive; serialization occurs exactly once. -/
theorem retry (capacity written : Nat) (bytes : Bytes) (remaining : List Bool)
    (history : List Nat) (used : Nat) :
    ((do
      let first ← encodeRecord scheduledReserve (fixedSerialize written bytes) capacity
      let second ← encodeRecord scheduledReserve (fixedSerialize written bytes) capacity
      pure (first, second) : M Schedule (Option Bytes × Option Bytes)).run
        ⟨false :: true :: remaining, history, used⟩) =
      pure ((none, if written = 0 then none else some (bytes.take written)),
        ⟨remaining, (history ++ [capacity]) ++ [capacity], used + 1⟩) := by
  simp [StateT.run_bind, run, scheduledReserve_run, fixedSerialize_run]

end BeaconcryptCore.Computational.RegistrationNativeAllocation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.run' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.reservation_failure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.reservation_failure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.reservation_failure_distribution' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.reservation_failure_distribution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.serialization_failure_distribution' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.serialization_failure_distribution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.pure_compatibility' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.pure_compatibility

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.scheduledReserve_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.scheduledReserve_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.fixedSerialize_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.fixedSerialize_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAllocation.retry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAllocation.retry
