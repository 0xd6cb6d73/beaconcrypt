-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant

/-! The actual selective material service returns a hidden reference only for its realized selected full input. Its allocator retains every earlier address association across all later demand branches. Equal retained slots therefore identify the same full input by the original allocator invariant, independently of material values or record outcomes. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeSelectiveHiddenService (State onHidden demand)
open PqxdhRecordLiftInterface (Slot)
variable {n : Nat}

private theorem old_receipt (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : State n) (reference : RegistrationNativePairedDemand.Reference n)
    (supported : (some (.hidden reference), after) ∈ support
      ((onHidden (RegistrationNativeHiddenService.demand source input inside message)).run before)) :
    ∃ bytes, input message = some bytes ∧ inside bytes = true ∧ after.1.slots bytes = some reference.slot := by
  simp only [onHidden, StateT.run, support_map] at supported
  obtain ⟨⟨reply, final⟩, actual, equal⟩ := supported
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  obtain ⟨bytes, formed, selected, assigned, _material⟩ :=
    RegistrationNativeHiddenServiceDemand.hidden_receipt source input inside message before.1 final reference actual
  exact ⟨bytes, formed, selected, assigned⟩

/-- An actual hidden response identifies its selected full input and its actual retained allocator entry. -/
theorem hidden_receipt (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before after : State n) (reference : RegistrationNativePairedDemand.Reference n)
    (supported : (some (.hidden reference), after) ∈ support ((demand source input inside candidate message).run before)) :
    ∃ bytes, input message = some bytes ∧ RegistrationNativeSelectiveHiddenService.selected inside candidate bytes = true ∧
      after.1.slots bytes = some reference.slot := by
  simp only [demand, StateT.run] at supported
  split at supported
  · cases realized : input message with
    | none =>
        simp only [realized] at supported
        simpa only [realized] using old_receipt source input _ message before after reference supported
    | some bytes =>
        simp only [realized] at supported
        split at supported
        · simp only [support_map] at supported
          obtain ⟨reached, _actual, impossible⟩ := supported
          cases impossible
        · simpa only [realized] using old_receipt source input _ message before after reference supported
  · exact old_receipt source input _ message before after reference supported

private theorem hidden_retains (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : RegistrationNativeHiddenService.State n) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (previous : Pqxdh.Bytes) (slot : Slot n) (assigned : before.slots previous = some slot)
    (supported : (reply, after) ∈ support ((RegistrationNativeHiddenService.demand source input inside message).run before)) :
    after.slots previous = some slot := by
  simp only [RegistrationNativeHiddenService.demand, StateT.run] at supported
  split at supported
  · cases realized : input message with
    | none =>
        simp only [realized, mem_support_pure_iff] at supported
        cases supported
        exact assigned
    | some bytes =>
        simp only [realized] at supported
        split at supported
        · let counted := { before with demands := before.demands + 1 }
          have retained := RegistrationNativeHiddenService.reserve_retains bytes previous counted slot assigned
          cases allocated : RegistrationNativeHiddenService.reserve bytes counted with
          | mk selected reached =>
              change _ ∈ support (match RegistrationNativeHiddenService.reserve bytes counted with
                | (none, final) => pure (none, final)
                | (some selected, final) => (fun result : PqxdhDeploymentHiddenLayout.Material × RegistrationNativeHiddenService.State n =>
                    (some (RegistrationNativePairedChoice.Choice.hidden ⟨selected, result.1⟩), result.2)) <$>
                      (RegistrationNativeHiddenService.material selected).run final) at supported
              rw [allocated] at supported retained
              cases selected with
              | none =>
                  simp only [mem_support_pure_iff] at supported
                  cases supported
                  exact retained
              | some selected =>
                  simp only [support_map] at supported
                  obtain ⟨⟨value, final⟩, actual, equal⟩ := supported
                  simp only [Prod.mk.injEq] at equal
                  obtain ⟨rfl, rfl⟩ := equal
                  have fields := RegistrationNativeHiddenServiceDemand.material_fields selected reached final value actual
                  exact (congrFun fields.2.1 previous).trans retained
        · simp only [mem_support_pure_iff] at supported
          cases supported
          exact assigned
  · simp only [mem_support_pure_iff] at supported
    cases supported
    exact assigned

private theorem old_retains (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message)
    (before after : State n) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (previous : Pqxdh.Bytes) (slot : Slot n) (assigned : before.1.slots previous = some slot)
    (supported : (reply, after) ∈ support
      ((onHidden (RegistrationNativeHiddenService.demand source input inside message)).run before)) :
    after.1.slots previous = some slot := by
  simp only [onHidden, StateT.run, support_map] at supported
  obtain ⟨⟨found, final⟩, actual, equal⟩ := supported
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  exact hidden_retains source input inside message before.1 final found previous slot assigned actual

/-- Every actual later demand retains every earlier descriptor address assignment, including failures and nonselected known-cache replies. -/
theorem demand_retains (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before after : State n) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (previous : Pqxdh.Bytes) (slot : Slot n) (assigned : before.1.slots previous = some slot)
    (supported : (reply, after) ∈ support ((demand source input inside candidate message).run before)) :
    after.1.slots previous = some slot := by
  simp only [demand, StateT.run] at supported
  split at supported
  · cases realized : input message with
    | none =>
        simp only [realized] at supported
        exact old_retains source input _ message before after reply previous slot assigned supported
    | some bytes =>
        simp only [realized] at supported
        split at supported
        · simp only [support_map] at supported
          obtain ⟨⟨value, final⟩, actual, equal⟩ := supported
          simp only [Prod.mk.injEq] at equal
          obtain ⟨rfl, rfl⟩ := equal
          have fields := RegistrationNativeSelectiveHiddenServiceInvariant.known_fields bytes
            ({ before.1 with demands := before.1.demands + 1 }, before.2) final value actual
          rw [fields.1]
          exact assigned
        · exact old_retains source input _ message before after reply previous slot assigned supported
  · exact old_retains source input _ message before after reply previous slot assigned supported

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary.hidden_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary.hidden_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary.demand_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDictionary.demand_retains
