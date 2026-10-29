-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOptionalCut
import BeaconcryptCore.Computational.RegistrationNativeKemGetterKey

/-! First-getter key provenance for optional native providers. The full source state and failure branches survive the cut; key restrictions follow the actual authenticated collector syntax. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemCut (Cut scan)
open RegistrationNativeKemCutKey (hasKey)
open PqxdhKemIndCca
variable {κ KemSK Value Result S : Type} {ambient : OracleSpec κ}

/-- Every first getter reached under an optional source has the exact key constrained by its literal program. -/
theorem pending_key (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT S ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value) (key : MlKem768PublicKey)
    (allowed : work.AllQueriesSatisfy (hasKey (ambient := ambient) (KemSK := KemSK) key))
    (actual : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Value)
    (before after : S)
    (supported : (some (Cut.pending actual next), after) ∈ support (((scan implementation work 0).run).run before)) :
    actual = key := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
      change (some (Cut.pending actual next), after) ∈ support
        (pure (some (Cut.complete value), before) : ProbComp (Option (Cut ambient KemSK Value) × S)) at supported
      simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported
  | query_bind query resume ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      rcases query with query | (query | requested)
      · simp only [RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM,
          StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨⟨reply, reached⟩, _prefix, tail⟩ := supported
        cases reply with
        | none =>
            simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
              reduceCtorEq, false_and] at tail
        | some reply => exact ih reply (allowed.2 reply) reached after tail
      · simp only [RegistrationNativeKemCut.scan_pool, OptionT.run_bind, Option.elimM,
          StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨⟨reply, reached⟩, _prefix, tail⟩ := supported
        cases reply with
        | none =>
            simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
              reduceCtorEq, false_and] at tail
        | some reply => exact ih reply (allowed.2 reply) reached after tail
      · simp only [RegistrationNativeKemCut.scan_target, OptionT.run_pure, StateT.run_pure,
          mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq, Cut.pending.injEq] at supported
        exact supported.1.1.trans allowed.1

/-- Exact continuation composition preserves first-getter key provenance through optional source failures. -/
theorem pending_bind (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT S ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value)
    (following : Value → OracleComp (Spec ambient KemSK) Result) (key : MlKem768PublicKey)
    (first : ∀ actual resume before after,
      (some (Cut.pending actual resume), after) ∈ support (((scan implementation work 0).run).run before) → actual = key)
    (last : ∀ value, (following value).AllQueriesSatisfy (hasKey (ambient := ambient) (KemSK := KemSK) key))
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Result)
    (before after : S)
    (supported : (some (Cut.pending actual resume), after) ∈ support
      (((scan implementation (work >>= following) 0).run).run before)) : actual = key := by
  rw [RegistrationNativeKemCutKey.scan_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨cut, reached⟩, prefixSupport, tail⟩ := supported
  cases cut with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some cut =>
      cases cut with
      | complete value => exact pending_key implementation _ key (last value) actual resume reached after tail
      | pending requested next =>
          simp only [Option.elim_some, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff,
            Prod.mk.injEq, Option.some.injEq, Cut.pending.injEq] at tail
          exact tail.1.1.trans (first requested next before reached prefixSupport)

variable {ι : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec)

private theorem collect_complete_impossible (setup : Setup base KemSK) (checks : Checks)
    (implementation : QueryImpl (Spec n mlSource KemSK) (OptionT (StateT S ProbComp)))
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhBeaconPhase2Preparation.Word32)
    (before after : S)
    (supported : (some (Cut.complete (some input)), after) ∈ support
      (((scan implementation (simulateQ (RegistrationNativeKemGetterKey.callbacks setup checks)
        (PqxdhServerRootPreparation.collectVerified verified)) 0).run).run before)) : False := by
  have stopped := RegistrationNativeKemOptionalCut.completed_support implementation _ (some input) before after supported
  apply RegistrationNativeKemStoppedGetter.collect_no_input setup checks verified input
  simp only [RegistrationNativeKemStoppedGetter.callbacks, QueryImpl.simulateQ_compose]
  change some (some input) ∈ support (simulateQ
    (RegistrationNativeKemStoppedGetter.stop ∘ₛ RegistrationNativeKemGetterKey.node setup checks)
    (simulateQ RegistrationAgreementRoot.callbacks (PqxdhServerRootPreparation.collectVerified verified))).run
  rw [QueryImpl.simulateQ_compose]
  simpa only [RegistrationNativeKemGetterKey.callbacks, QueryImpl.simulateQ_compose,
    RegistrationNativeKemStoppedGetter.stop] using stopped

/-- The actual open native agreement's first getter uses the authenticated PQ coordinate under any optional candidate provider. -/
theorem agreement_pending_key (setup : Setup base KemSK) (checks : Checks)
    (implementation : QueryImpl (Spec n mlSource KemSK) (OptionT (StateT S ProbComp)))
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (history : RegistrationReplaySchedule.State)
    (actual : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM agreement.AgreementEffect))
    (before after : S)
    (supported : (some (Cut.pending actual next), after) ∈ support
      (((scan implementation (simulateQ (RegistrationNativeKemGetterKey.node setup checks)
        (RegistrationReplaySchedule.begin control authenticated history)) 0).run).run before)) :
    actual = RegistrationRootInput.pqKey authenticated.registration.beacon_pq_public_key := by
  rw [RegistrationReplaySchedule.begin_eq] at supported
  split at supported
  · simp only [simulateQ_pure] at supported
    change (some (Cut.pending actual next), after) ∈ support
      (pure (some (Cut.complete (.ok (.Rejected .None))), before) : ProbComp _) at supported
    simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported
  · rw [RegistrationAgreementRoot.server_normalized control packet authenticated] at supported
    simp only [RegistrationAgreementRoot.normalized, simulateQ_bind, ← QueryImpl.simulateQ_compose] at supported
    change (some (Cut.pending actual next), after) ∈ support
      (((scan implementation (simulateQ (RegistrationNativeKemGetterKey.callbacks setup checks)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) >>= _) 0).run).run before) at supported
    rw [RegistrationNativeKemCutKey.scan_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
      mem_support_bind_iff] at supported
    obtain ⟨⟨cut, reached⟩, prefixSupport, tail⟩ := supported
    cases cut with
    | none =>
        simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
          reduceCtorEq, false_and] at tail
    | some cut =>
        cases cut with
        | complete input =>
            cases input with
            | some input => exact False.elim (collect_complete_impossible setup checks implementation _ input before reached prefixSupport)
            | none =>
                simp only [] at tail
                change (some (Cut.pending actual next), after) ∈ support
                  (pure (some (Cut.complete (.ok (.Rejected .None))), reached) : ProbComp _) at tail
                simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at tail
        | pending key resume =>
            simp only [Option.elim_some, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff,
              Prod.mk.injEq, Option.some.injEq, Cut.pending.injEq] at tail
            have selected := pending_key implementation _ _
              (RegistrationNativeKemGetterKey.collect_queries setup checks (RegistrationRootInput.verified packet authenticated))
              key resume before reached prefixSupport
            exact tail.1.1.trans selected

end BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey.pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey.pending_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey.pending_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey.pending_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey.agreement_pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey.agreement_pending_key
