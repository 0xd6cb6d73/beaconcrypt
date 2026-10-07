-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters

/-! Actual local source callbacks preserve the allowed slots of every table entry. This is an operational write-footprint result for complete executions, including failed-opening rollback and retained native state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftTableScope
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler
open PqxdhFullSecretInputKdf
variable {Slot Context Plaintext PrimitiveState : Type}

/-- Every populated table coordinate names a slot admitted by the supplied predicate. -/
def TableAllowed (allowed : Slot → Prop) (table : Table Slot) : Prop :=
  ∀ coordinate value, table coordinate = some value → allowed coordinate.slot

/-- Empty state requires no seed or slot to be present. -/
theorem tableAllowed_empty (allowed : Slot → Prop) : TableAllowed allowed (∅ : Table Slot) := by
  simp [TableAllowed]

/-- Enlarging the set of admitted slots preserves the same complete table's provenance. -/
theorem tableAllowed_mono (before after : Slot → Prop) (inclusion : ∀ slot, before slot → after slot)
    (table : Table Slot) (permitted : TableAllowed before table) : TableAllowed after table :=
  fun coordinate value found => inclusion coordinate.slot (permitted coordinate value found)

/-- A supported callback may populate its requested coordinate or retain an already populated coordinate, but cannot introduce another coordinate. -/
def LookupWritesOnly (lookup : Lookup Slot PrimitiveState) : Prop :=
  ∀ coordinate state result, result ∈ support ((lookup coordinate).run state) →
    ∀ other value, result.2.1 other = some value →
      other = coordinate ∨ ∃ previous, state.1 other = some previous

/-- A lookup's actual supported write footprint retains allowed slots while preserving every arbitrary native effect. -/
theorem lookup_allowed (allowed : Slot → Prop) (lookup : Lookup Slot PrimitiveState)
    (footprint : LookupWritesOnly lookup) (coordinate : Label Slot) (permitted : allowed coordinate.slot)
    (state : Execution Slot PrimitiveState) (before : TableAllowed allowed state.1)
    (result : FullOutput × Execution Slot PrimitiveState)
    (supported : result ∈ support ((lookup coordinate).run state)) :
    TableAllowed allowed result.2.1 :=
  fun other value found => match footprint coordinate state result supported other value found with
    | .inl same => same ▸ permitted
    | .inr ⟨previous, old⟩ => before other previous old

/-- Every actual recursive receive preserves the allowed table slots, even if its opening fails after several persistent writes. -/
theorem receive_allowed (allowed : Slot → Prop) (seeds : Seeds Slot)
    (lookup : Lookup Slot PrimitiveState) (footprint : LookupWritesOnly lookup)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (allowedReceive : allowed entry.receive_chain.slot) (effect : Effect Slot Context)
    (tracked : Tracked entry context effect) (state : Execution Slot PrimitiveState)
    (before : TableAllowed allowed state.1)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    TableAllowed allowed result.2.1 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected original prior =>
      rcases (show result = ((original, .None), state) from by
        simpa only [StateT.run, receive, support_pure, Set.mem_singleton_iff] using supported) with rfl
      exact before
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      rcases supported with ⟨reply, _, rfl⟩
      exact before
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      exact match supported with
      | ⟨reply, member, continued⟩ =>
        ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
          _ (resume_tracked entry context pending pending.request tracked) reply.2
          (lookup_allowed allowed lookup footprint pending.request
            (by simpa only [tracked.2.2, advance] using allowedReceive) state before reply member)
          result continued rfl

/-- Original receive admission derives the callback-origin premise for all targets, without a selected trace or successful opening. -/
theorem admitted_receive_allowed (allowed : Slot → Prop) (seeds : Seeds Slot)
    (lookup : Lookup Slot PrimitiveState) (footprint : LookupWritesOnly lookup)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (target : Std.U64) (allowedReceive : allowed entry.receive_chain.slot)
    (state : Execution Slot PrimitiveState) (before : TableAllowed allowed state.1)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening
      (RawCtxChainReceive.normalBegin entry target context)).run state)) :
    TableAllowed allowed result.2.1 :=
  receive_allowed allowed seeds lookup footprint opening entry context allowedReceive _
    (begin_tracked entry context target) state before result supported

/-- An actual send writes only at its own source direction, including writer failure after advancement. -/
theorem send_allowed {Output : Type} (allowed : Slot → Prop) (seeds : Seeds Slot)
    (lookup : Lookup Slot PrimitiveState) (footprint : LookupWritesOnly lookup)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (allowedSend : allowed entry.send_chain.slot) (start : Start Slot Context)
    (tracked : SendTracked entry context start) (state : Execution Slot PrimitiveState)
    (before : TableAllowed allowed state.1)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing start).run state)) :
    TableAllowed allowed result.2.1 := by
  cases start with
  | exhausted original prior =>
    rcases (show result = ((original, none), state) from by
      simpa only [StateT.run, send, support_pure, Set.mem_singleton_iff] using supported) with rfl
    exact before
  | requested pending =>
    simp only [StateT.run, send, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    rcases supported with ⟨reply, member, sealed, _, rfl⟩
    exact lookup_allowed allowed lookup footprint pending.request
      (by simpa only [tracked.2.2.1] using allowedSend) state before reply member

/-- Literal send admission supplies provenance on both ordinary and exhausted-counter paths. -/
theorem admitted_send_allowed {Output : Type} (allowed : Slot → Prop) (seeds : Seeds Slot)
    (lookup : Lookup Slot PrimitiveState) (footprint : LookupWritesOnly lookup)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (allowedSend : allowed entry.send_chain.slot) (state : Execution Slot PrimitiveState)
    (before : TableAllowed allowed state.1)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing
      (RawCtxChainSend.normalBegin entry context)).run state)) :
    TableAllowed allowed result.2.1 :=
  send_allowed allowed seeds lookup footprint sealing entry context allowedSend _
    (send_begin_tracked entry context) state before result supported

/-- Carrying the existing writer log alongside native state preserves the exact same table write footprint. -/
theorem liftLookup_writesOnly (lookup : Lookup Slot PrimitiveState) (footprint : LookupWritesOnly lookup) :
    LookupWritesOnly (PqxdhRecordLiftLoggedAdapters.liftLookup lookup) := by
  intro coordinate state result supported
  simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, support_map] at supported
  rcases supported with ⟨reply, member, rfl⟩
  exact footprint coordinate (state.1, state.2.1) reply member

end BeaconcryptCore.Computational.PqxdhRecordLiftTableScope

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.tableAllowed_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.tableAllowed_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.tableAllowed_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.tableAllowed_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.lookup_allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.lookup_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.receive_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.receive_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.admitted_receive_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.admitted_receive_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.send_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.send_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.admitted_send_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.admitted_send_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.liftLookup_writesOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftTableScope.liftLookup_writesOnly
