-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementRoot
import BeaconcryptCore.Computational.RegistrationNativeKemCutStop

/-! Optional native root collection cannot return a root input when its literal encapsulation callback aborts or returns None. These local support lemmas retain every earlier effect and will be instantiated with the actual first-getter-aborting compiler. No successful-session or whole-game reachability premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKemNoInput
variable {Query Value Next Prefix Reader E Shared : Type} {spec : OracleSpec Query}

def NoSome (work : OptionT (OracleComp spec) (Option Value)) : Prop :=
  ∀ value, some (some value) ∉ support work.run

private theorem pure_none : NoSome (pure none : OptionT (OracleComp spec) (Option Value)) := by
  intro value
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq, reduceCtorEq, not_false_eq_true]

/-- Arbitrary earlier effects cannot make a failing optional continuation return an input. -/
theorem prefix_no_some (work : OptionT (OracleComp spec) Prefix)
    (next : Prefix → OptionT (OracleComp spec) (Option Value)) (following : ∀ value, NoSome (next value)) :
    NoSome (work >>= next) := by
  intro value supported
  simp only [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at supported
  obtain ⟨reply, _, tail⟩ := supported
  cases reply with
  | none => simp only [Option.elim_none, support_pure, Set.mem_singleton_iff, reduceCtorEq] at tail
  | some answer => exact following answer value (by simpa only [Option.elim_some] using tail)

/-- Both an outer abort and an inner None terminate native optional collection before its later successful continuation. -/
theorem optional_no_some (work : OptionT (OracleComp spec) (Option Value)) (stopped : NoSome work)
    (next : Option Value → OptionT (OracleComp spec) (Option Next)) (onNone : NoSome (next none)) :
    NoSome (work >>= next) := by
  intro value supported
  simp only [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at supported
  obtain ⟨reply, selected, tail⟩ := supported
  cases reply with
  | none => simp only [Option.elim_none, support_pure, Set.mem_singleton_iff, reduceCtorEq] at tail
  | some answer =>
      cases answer with
      | none => exact onNone value (by simpa only [Option.elim_some] using tail)
      | some answer => exact stopped answer selected

/-- The actual normalized root collector cannot yield an input without its requested KEM result, including every earlier optional rejection. -/
theorem collect_no_some
    (implementation : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (OptionT (OracleComp spec)))
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (encapsulation : NoSome (implementation (.encapsulate verified.keys.pqKey))) :
    NoSome (simulateQ implementation (PqxdhServerRootPreparation.collectVerified verified)) := by
  simp only [PqxdhServerRootPreparation.collectVerified, OptionT.run_bind, OptionT.run_monadLift,
    Option.elimM, Option.elim_some, bind_map_left, bind_pure_comp, simulateQ_bind, simulateQ_spec_query]
  apply prefix_no_some
  intro status
  cases status with
  | Consumed => exact pure_none
  | Fresh =>
      change NoSome (implementation .reserveRegistration >>= _)
      apply prefix_no_some
      intro reserved
      cases reserved
      · exact pure_none
      · change NoSome (implementation (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.prekey)) >>= _)
        apply prefix_no_some
        intro validPrekey
        cases validPrekey
        · exact pure_none
        · change NoSome (implementation (.parseDh (PqxdhRootTableInitialization.rootArray verified.keys.oneTime)) >>= _)
          apply prefix_no_some
          intro validOneTime
          cases validOneTime
          · exact pure_none
          · change NoSome (implementation .generate >>= _)
            apply prefix_no_some
            intro ephemeral
            cases ephemeral with
            | none => exact pure_none
            | some ephemeral =>
                change NoSome (implementation (.parseKem verified.keys.pqKey) >>= _)
                apply prefix_no_some
                intro validKem
                cases validKem
                · exact pure_none
                · change NoSome (implementation (.encapsulate verified.keys.pqKey) >>= _)
                  apply optional_no_some _ encapsulation
                  exact pure_none

end BeaconcryptCore.Computational.RegistrationNativeKemNoInput

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemNoInput.prefix_no_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemNoInput.prefix_no_some

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemNoInput.optional_no_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemNoInput.optional_no_some

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemNoInput.collect_no_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemNoInput.collect_no_some
