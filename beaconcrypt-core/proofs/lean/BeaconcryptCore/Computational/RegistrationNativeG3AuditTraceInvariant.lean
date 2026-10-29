-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedDictionary
import BeaconcryptCore.Computational.RegistrationNativePairedEvents

/-! The actual used-role audit is linked to chronological native descriptor events through the persistent full-input dictionary. An earlier successful use and a later matching-slot attempt identify the same selected input by allocator injectivity. The ordered repetition witness survives arbitrary later events, including callback refusal. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant
open PqxdhRecordLiftInterface (Slot Role)
open RegistrationNativeG2Trace (Event RepeatedRoleAttempt)
variable {n : Nat} {KemSK ProviderState : Type}

def Seen (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (keys : RegistrationNativeHiddenService.State n) (used : Slot n → Role → Bool) (events : List Event) : Prop :=
  ∀ slot role, used slot role = true → ∃ message bytes,
    Event.install role message ∈ events ∧ input message = some bytes ∧ inside bytes = true ∧ keys.slots bytes = some slot

def Good (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (trace : RegistrationNativePairedTrace.State n) (privateState : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State n × Bool) : Prop :=
  (RegistrationNativeSelectiveHiddenDictionaryRun.Good privateState ∧
    RegistrationNativePairedDictionary.Current input inside trace privateState.1.keys) ∧
  Seen input inside privateState.1.keys world.1.used trace.trace.events ∧
  (world.2 = true → RepeatedRoleAttempt input inside trace.trace.events)

variable (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)

/-- Ordinary actual callbacks retain every earlier successful-slot receipt and any already marked ordered repetition witness. -/
theorem ordinary (before after : RegistrationNativePairedTrace.State n)
    (old new : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world final : PqxdhRecordLiftWorld.State n × Bool) (valid : Good input inside before old world)
    (dictionary : RegistrationNativeSelectiveHiddenDictionaryRun.Good new ∧
      RegistrationNativePairedDictionary.Current input inside after new.1.keys)
    (keeps : ∀ bytes slot, old.1.keys.slots bytes = some slot → new.1.keys.slots bytes = some slot)
    (suffix : List Event) (events : after.trace.events = before.trace.events ++ suffix)
    (used : final.1.used = world.1.used) (flag : final.2 = world.2) : Good input inside after new final := by
  refine ⟨dictionary, ?_, ?_⟩
  · intro slot role active
    rw [used] at active
    obtain ⟨message, bytes, installed, formed, protectedInput, assigned⟩ := valid.2.1 slot role active
    exact ⟨message, bytes, by rw [events]; exact List.mem_append_left _ installed, formed, protectedInput, keeps bytes slot assigned⟩
  · intro active
    rw [events]
    exact RegistrationNativePairedEvents.repeat_append input inside _ suffix (valid.2.2 (flag.symm.trans active))

/-- One actual hidden installation update derives a same-input ordered repeat from its real current demand and persistent allocator receipt. -/
theorem installed (before after : RegistrationNativePairedTrace.State n)
    (old new : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world final : PqxdhRecordLiftWorld.State n × Bool) (valid : Good input inside before old world)
    (dictionary : RegistrationNativeSelectiveHiddenDictionaryRun.Good new ∧
      RegistrationNativePairedDictionary.Current input inside after new.1.keys)
    (keeps : ∀ bytes slot, old.1.keys.slots bytes = some slot → new.1.keys.slots bytes = some slot)
    (role : Role) (slot : Slot n) (reply : Bool) (message : RegistrationNativeRelatedFamily.Message)
    (reference : RegistrationNativePairedDemand.Reference n)
    (current : before.trace.current = some message) (choice : before.choice = some (.hidden reference))
    (sameSlot : slot = reference.slot)
    (events : after.trace.events = before.trace.events ++ [.installAttempt role message] ++ if reply then [.install role message] else [])
    (used : final.1.used = if reply then Function.update world.1.used slot (Function.update (world.1.used slot) role true) else world.1.used)
    (flag : final.2 = (world.2 || world.1.used slot role)) : Good input inside after new final := by
  obtain ⟨bytes, formed, protectedInput, assigned⟩ := valid.1.2 message reference current choice
  have sourceSlot : old.1.keys.slots bytes = some slot := by rw [sameSlot]; exact assigned
  refine ⟨dictionary, ?_, ?_⟩
  · intro selected actual active
    have prior : world.1.used selected actual = true ∨ (selected = slot ∧ actual = role ∧ reply = true) := by
      rw [used] at active
      cases reply <;> by_cases selectedSlot : selected = slot <;> by_cases selectedRole : actual = role <;> simp_all
    rcases prior with prior | ⟨rfl, rfl, successful⟩
    · obtain ⟨earlier, previous, installed, built, protectedPrevious, retained⟩ := valid.2.1 selected actual prior
      exact ⟨earlier, previous, by rw [events]; exact List.mem_append_left _ (List.mem_append_left _ installed),
        built, protectedPrevious, keeps previous selected retained⟩
    · exact ⟨message, bytes, by rw [events, successful]; simp, formed, protectedInput, keeps bytes _ sourceSlot⟩
  · intro active
    rw [flag, Bool.or_eq_true] at active
    rcases active with prior | usedBefore
    · rw [events]
      simpa only [List.append_assoc] using RegistrationNativePairedEvents.repeat_append input inside
        before.trace.events ([.installAttempt role message] ++ if reply then [.install role message] else []) (valid.2.2 prior)
    · obtain ⟨earlier, previous, installed, built, _protectedPrevious, retained⟩ := valid.2.1 slot role usedBefore
      have sameBytes : previous = bytes := valid.1.1.2 previous bytes slot retained sourceSlot
      subst previous
      obtain ⟨left, right, split⟩ := List.mem_iff_append.mp installed
      refine ⟨left, right, if reply then [.install role message] else [], role, earlier, message, bytes, ?_, built, formed, protectedInput⟩
      rw [events, split]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

end BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant.ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant.installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceInvariant.installed
