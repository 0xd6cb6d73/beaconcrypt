-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory

/-! The actual guarded audit flag has an ordered successful-installation/later-attempt witness in its own private slot/role trace. The used-map/history invariant is proved through every actual callback and adaptive continuation from unused initial roles. No descriptor provenance or probability estimate is assumed by this World-level result. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun
open PqxdhRecordLiftInterface (Slot Role)
open PqxdhRecordLiftWorld (State)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedWorld (Request Spec Seeds repeated)
open RegistrationNativeG3AuditHistory (Event events updateUsed handler)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def Repeated (history : List (Event n)) : Prop :=
  ∃ earlier middle later slot role,
    history = earlier ++ [.success slot role] ++ middle ++ [.attempt slot role] ++ later

def Good (world : State n × Bool) (history : List (Event n)) : Prop :=
  (∀ slot role, world.1.used slot role = true → Event.success slot role ∈ history) ∧
    (world.2 = true → Repeated history)

private theorem repeated_append (history extra : List (Event n)) (bad : Repeated history) :
    Repeated (history ++ extra) := by
  obtain ⟨earlier, middle, later, slot, role, rfl⟩ := bad
  refine ⟨earlier, middle, later ++ extra, slot, role, ?_⟩
  simp only [List.append_assoc]

private theorem repeated_attempt (history : List (Event n)) (slot : Slot n) (role : Role)
    (extra : List (Event n)) (earlier : Event.success slot role ∈ history) :
    Repeated (history ++ .attempt slot role :: extra) := by
  obtain ⟨left, right, split⟩ := List.mem_iff_append.mp earlier
  refine ⟨left, right, extra, slot, role, ?_⟩
  rw [split]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

private theorem role_good (before after : State n × Bool) (history : List (Event n))
    (slot : Slot n) (role : Role) (reply : Bool) (valid : Good before history)
    (used : after.1.used = if reply then Function.update before.1.used slot (Function.update (before.1.used slot) role true) else before.1.used)
    (flag : after.2 = (before.2 || before.1.used slot role)) :
    Good after (history ++ .attempt slot role :: if reply then [.success slot role] else []) := by
  constructor
  · intro selected actual active
    have source : before.1.used selected actual = true ∨ (selected = slot ∧ actual = role ∧ reply = true) := by
      rw [used] at active
      cases reply <;> by_cases sameSlot : selected = slot <;> by_cases sameRole : actual = role <;>
        simp_all
    rcases source with old | ⟨rfl, rfl, successful⟩
    · exact List.mem_append_left _ (valid.1 selected actual old)
    · simp only [successful, ite_true]
      exact List.mem_append_right _ (by simp)
  · intro active
    rw [flag, Bool.or_eq_true] at active
    rcases active with old | used
    · exact repeated_append history _ (valid.2 old)
    · exact repeated_attempt history slot role _ (valid.1 slot role used)

private theorem flag_update (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : Request n)
    (before : State n × Bool) (result : (Spec n).Range query × (State n × Bool))
    (supported : result ∈ support ((RegistrationNativeG3GuardedWorld.marked setup codec route seeds true query).run before)) :
    result.2.2 = (before.2 || repeated query before.1) := by
  simp only [RegistrationNativeG3GuardedWorld.marked, StateT.run, support_map] at supported
  obtain ⟨reached, _actual, rfl⟩ := supported
  rfl

/-- Every actual known-side audit callback preserves the full used-role and ordered repetition history invariant. -/
theorem query_good (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : Request n)
    (before : (State n × Bool) × List (Event n)) (valid : Good before.1 before.2)
    (result : (Spec n).Range query × ((State n × Bool) × List (Event n)))
    (supported : result ∈ support ((handler setup codec route seeds query).run before)) :
    Good result.2.1 result.2.2 := by
  simp only [handler, StateT.run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  have used := RegistrationNativeG3AuditHistory.query_used setup codec route seeds query before.1 reached actual
  have flag := flag_update setup codec route seeds query before.1 reached actual
  cases query with
  | ordinary query allowed =>
      simp only [updateUsed] at used
      simp only [repeated, Bool.or_false] at flag
      simp only [events, List.append_nil]
      constructor
      · intro slot role active
        rw [used] at active
        exact valid.1 slot role active
      · intro active
        exact valid.2 (flag.symm.trans active)
  | server keyId binding slot => exact role_good before.1 reached.2 before.2 slot .server reached.1 valid used flag
  | beacon owner shell slot => exact role_good before.1 reached.2 before.2 slot .beacon reached.1 valid used flag

/-- The exact guarded adaptive program retains the derived ordered repetition witness through all later callbacks and failures. -/
theorem program_good (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : (State n × Bool) × List (Event n))
    (valid : Good before.1 before.2) (result : Value × ((State n × Bool) × List (Event n)))
    (supported : result ∈ support ((simulateQ (handler setup codec route seeds) work).run before)) :
    Good result.2.1 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reached, first, later⟩ := supported
      exact ih reached.1 reached.2 (query_good setup codec route seeds query before valid reached first) later

/-- A true literal marked audit from unused initial roles has a chronological same-slot/role successful installation followed by a later attempt, on the same actual output. -/
theorem marked_repeat (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n)
    (unused : ∀ slot role, before.used slot role = false) (value : Value) (after : State n)
    (supported : (value, (after, true)) ∈ support
      ((simulateQ (RegistrationNativeG3GuardedWorld.marked setup codec route seeds true) work).run (before, false))) :
    ∃ history, (value, ((after, true), history)) ∈ support
      ((simulateQ (handler setup codec route seeds) work).run ((before, false), [])) ∧ Repeated history := by
  rw [← RegistrationNativeG3AuditHistory.program_source setup codec route seeds work ((before, false), []), support_map] at supported
  obtain ⟨result, actual, equal⟩ := supported
  have valid : Good (before, false) [] := by
    constructor
    · intro slot role active
      rw [unused] at active
      cases active
    · intro impossible
      cases impossible
  have final := program_good setup codec route seeds work ((before, false), []) valid result actual
  rcases result with ⟨found, ⟨⟨world, flag⟩, history⟩⟩
  simp only [Prod.map_def, id_eq, Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl, rfl⟩ := equal
  exact ⟨history, actual, final.2 rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun.marked_repeat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun.marked_repeat
