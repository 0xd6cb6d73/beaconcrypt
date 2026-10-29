-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenTargetCall
import BeaconcryptCore.Computational.RegistrationNativeKemStoppedSdk

/-! Optional native source executions retain their actual first-getter suspension and actual provider reply. Completed SDK sessions cannot come from a completed cut; that fact is discharged from the literal generated callback program, rather than added as a selected-event premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemCut (Cut scan finish)
open PqxdhKemIndCca
variable {κ KemSK Value S : Type} {ambient : OracleSpec κ}

/-- A completed optional source cut is supported by the exact original abort-at-first-getter syntax. -/
theorem completed_support (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT S ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value) (value : Value) (before after : S)
    (supported : (some (Cut.complete value), after) ∈ support (((scan implementation work 0).run).run before)) :
    some value ∈ support ((simulateQ (RegistrationNativeKemCutStop.stop (fun query =>
      ((Spec ambient KemSK).query query : OracleComp (Spec ambient KemSK) _))) work).run) := by
  have original : Cut.complete value ∈ support
      (scan (fun query => ((Spec ambient KemSK).query query : OracleComp (Spec ambient KemSK) _)) work 0) := by
    apply RegistrationNativeOptionalSupport.completed_support implementation _ (Cut.complete value) before after
    simpa only [RegistrationNativeKemCutStop.scan_simulate] using supported
  rw [← RegistrationNativeKemCutStop.scan_stop, support_map]
  exact Set.mem_image_of_mem RegistrationNativeKemCutStop.complete original

/-- Successful optional execution exposes its actual first provider query whenever the original stopped syntax cannot produce that result. -/
theorem pending_reply (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT S ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value) (value : Value) (before after : S)
    (noComplete : some value ∉ support ((simulateQ (RegistrationNativeKemCutStop.stop (fun query =>
      ((Spec ambient KemSK).query query : OracleComp (Spec ambient KemSK) _))) work).run))
    (supported : (some value, after) ∈ support (((simulateQ implementation work).run).run before)) :
    ∃ key next reached reply replied,
      (some (Cut.pending key next), reached) ∈ support (((scan implementation work 0).run).run before) ∧
      (some reply, replied) ∈ support (((implementation (.inr (.inr key))).run).run reached) ∧
      (some value, after) ∈ support (((simulateQ implementation (next reply)).run).run replied) := by
  have execution := congrArg (fun program : OptionT (StateT S ProbComp) Value => (program.run).run before)
    (RegistrationNativeKemCut.scan_finish implementation work 0)
  rw [← execution, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨cut, reached⟩, prefixSupport, tail⟩ := supported
  cases cut with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some cut =>
      cases cut with
      | complete actual =>
          simp only [Option.elim_some, finish, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff,
            Prod.mk.injEq, Option.some.injEq] at tail
          obtain ⟨rfl, rfl⟩ := tail
          exact False.elim (noComplete (completed_support implementation work value before after prefixSupport))
      | pending key next =>
          simp only [Option.elim_some, finish, OptionT.run_bind, Option.elimM,
            StateT.run_bind, mem_support_bind_iff] at tail
          obtain ⟨⟨reply, replied⟩, called, rest⟩ := tail
          cases reply with
          | none =>
              simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
                reduceCtorEq, false_and] at rest
          | some reply => exact ⟨key, next, reached, reply, replied, prefixSupport, called, rest⟩

variable {ι : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

/-- A literal successful open SDK typed accept has an actual getter-zero suspension and provider reply under any optional native interpreter. -/
theorem sdk_pending_reply (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (packet : registration.InitPacket)
    (implementation : QueryImpl (RegistrationNativeKemParsedRouting.Spec n mlSource KemSK) (OptionT (StateT S ProbComp)))
    (session : Nat) (before after : S)
    (supported : (some (.ok (some session)), after) ∈ support
      (((simulateQ implementation (simulateQ (RegistrationNativeKemOpenFrame.lower true)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet))).run).run before)) :
    ∃ key next reached reply replied,
      (some (Cut.pending key next), reached) ∈ support
        (((scan implementation (simulateQ (RegistrationNativeKemOpenFrame.lower true)
          (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) 0).run).run before) ∧
      (some reply, replied) ∈ support (((implementation (.inr (.inr key))).run).run reached) ∧
      (some (.ok (some session)), after) ∈ support (((simulateQ implementation (next reply)).run).run replied) := by
  apply pending_reply implementation _ (.ok (some session) : RustM (Option Nat)) before after _ supported
  intro impossible
  have stopped : some (.ok (some session)) ∈ support
      ((simulateQ (RegistrationNativeKemStoppedSdk.lower (n := n) (mlSource := mlSource))
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet)).run) := by
    simpa only [RegistrationNativeKemStoppedSdk.lower, RegistrationNativeKemOpenFrame.lower,
      QueryImpl.simulateQ_compose, RegistrationNativeKemStoppedGetter.stop] using impossible
  apply RegistrationNativeKemStoppedSdk.typed_no_session (n := n) (mlSource := mlSource) setup checks packet session
  rw [OptionT.run_map, support_map]
  exact Set.mem_image_of_mem (Option.map RegistrationNativeKemStoppedSdk.sessionResult) stopped

end BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut.completed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut.completed_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut.pending_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut.pending_reply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut.sdk_pending_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut.sdk_pending_reply
