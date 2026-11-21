-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedChoice
import BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation

/-! The concrete post-key-hop service exposes only material44 and an allocated reference for a protected input. Its state contains no hidden seed, concrete record kernel, World lens or secrecy ledger. Slots are allocated by the full literal source input and retained across descriptor aliases. Overflow is explicit until the whole client's actual demand cap discharges it. Reusing an installation role is not silently turned into a native refusal by this service. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenService
open RegistrationNativeRelatedFamily (Message)
open PqxdhRecordLiftInterface (Slot EnvEffects)
open PqxdhDeploymentHiddenLayout (Material)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat}

structure State (n : Nat) where
  prepared : Message → Bool
  slots : Pqxdh.Bytes → Option (Slot n)
  next : Nat
  demands : Nat
  materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache

def initial : State n := ⟨fun _ => false, fun _ => none, 0, 0, ∅⟩

def coins : QueryImpl unifSpec (OracleComp (EnvEffects n)) := fun query =>
  (EnvEffects n).query (.inl query)

def prepare (input : Message → Option Pqxdh.Bytes) (message : Message) :
    StateT (State n) (OracleComp (EnvEffects n)) (Option Message) := fun before =>
  let successful := (input message).isSome
  pure ((input message).map (fun _ => message), { before with prepared := Function.update before.prepared message successful })

def reserve (bytes : Pqxdh.Bytes) (before : State n) : Option (Slot n) × State n :=
  match before.slots bytes with
  | some slot => (some slot, before)
  | none => if room : before.next < n then
      let slot : Slot n := ⟨before.next, room⟩
      (some slot, { before with slots := Function.update before.slots bytes (some slot), next := before.next + 1 })
    else (none, before)

noncomputable def material (slot : Slot n) : StateT (State n) (OracleComp (EnvEffects n)) Material := fun before =>
  match before.materials slot with
  | some value => pure (value, before)
  | none => (fun value => (value, { before with materials := before.materials.cacheQuery slot value })) <$>
      simulateQ coins ($ᵗ Material)

noncomputable def demand (source : FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    StateT (State n) (OracleComp (EnvEffects n)) (Option (RegistrationNativePairedChoice.Choice n)) := fun before =>
  let counted := { before with demands := before.demands + 1 }
  if before.prepared message then
    match input message with
    | none => pure (none, counted)
    | some bytes =>
        if inside bytes then
          match reserve bytes counted with
          | (none, after) => pure (none, after)
          | (some slot, after) => (fun result => (some (.hidden ⟨slot, result.1⟩), result.2)) <$>
              (material slot).run after
        else pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source
          (RegistrationNativeRelatedRoot.nativeRoot source bytes))), counted)
  else pure (none, counted)

/-- Successful preparation exposes its actual descriptor and records only its success flag. -/
theorem prepare_run (input : Message → Option Pqxdh.Bytes) (message : Message) (before : State n) :
    (prepare input message).run before =
      pure ((input message).map (fun _ => message),
        { before with prepared := Function.update before.prepared message (input message).isSome }) := rfl

/-- A literal input alias keeps its original slot without consuming capacity. -/
theorem reserve_hit (bytes : Pqxdh.Bytes) (before : State n) (slot : Slot n)
    (found : before.slots bytes = some slot) : reserve bytes before = (some slot, before) := by
  simp only [reserve, found]

/-- New allocations use the next actual free index and preserve every existing slot assignment. -/
theorem reserve_retains (bytes previous : Pqxdh.Bytes) (before : State n) (slot : Slot n)
    (found : before.slots previous = some slot) : (reserve bytes before).2.slots previous = some slot := by
  unfold reserve
  split
  · exact found
  · rename_i missing
    split
    · have different : previous ≠ bytes := by
        intro same
        subst previous
        rw [missing] at found
        cases found
      exact (Function.update_of_ne different _ _).trans found
    · exact found

/-- Repeat material reads retain the entire public service state and make no new probability query. -/
theorem material_hit (slot : Slot n) (before : State n) (value : Material)
    (found : before.materials slot = some value) : (material slot).run before = pure (value, before) := by
  simp only [material, StateT.run, found]

/-- A fresh material read samples only its44 public bytes through the actual environment coin surface. -/
theorem material_miss (slot : Slot n) (before : State n)
    (missing : before.materials slot = none) :
    (material slot).run before =
      (fun value => (value, { before with materials := before.materials.cacheQuery slot value })) <$>
        simulateQ coins ($ᵗ Material) := by
  simp only [material, StateT.run, missing]

/-- Off-protected inputs preserve their actual deterministic source108 reply, after the same successful prepare check. -/
theorem demand_known (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (message : Message) (before : State n) (bytes : Pqxdh.Bytes)
    (prepared : before.prepared message = true) (realized : input message = some bytes) (outside : inside bytes = false) :
    (demand source input inside message).run before = pure
      (some (.known (PqxdhServerAuthKeySchedule.fromRoot source (RegistrationNativeRelatedRoot.nativeRoot source bytes))),
        { before with demands := before.demands + 1 }) := by
  simp only [demand, StateT.run, prepared, ite_true, realized, outside, Bool.false_eq_true, ite_false]

/-- A protected demand returns only its persistent slot and material44. The private64 seed is neither sampled nor inspected by this service. -/
theorem demand_hidden (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (message : Message) (before after : State n) (bytes : Pqxdh.Bytes) (slot : Slot n)
    (prepared : before.prepared message = true) (realized : input message = some bytes) (protectedInput : inside bytes = true)
    (allocated : reserve bytes { before with demands := before.demands + 1 } = (some slot, after)) :
    (demand source input inside message).run before =
      (fun result => (some (.hidden ⟨slot, result.1⟩), result.2)) <$> (material slot).run after := by
  simp only [demand, StateT.run, prepared, ite_true, realized, protectedInput, allocated]

end BeaconcryptCore.Computational.RegistrationNativeHiddenService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.reserve_hit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.reserve_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.reserve_retains' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.reserve_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.material_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.material_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.material_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.material_miss
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.demand_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.demand_known
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenService.demand_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenService.demand_hidden
