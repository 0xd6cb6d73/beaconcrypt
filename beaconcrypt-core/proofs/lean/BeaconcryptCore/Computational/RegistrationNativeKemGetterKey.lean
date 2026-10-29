-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCutKey
import BeaconcryptCore.Computational.RegistrationNativeKemStoppedGetter

/-! The authenticated native root collector can expose only its verified PQ key. Its optional early exits and actual logged primitive callbacks remain in their literal order. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemGetterKey
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemCutKey (hasKey)
open PqxdhKemIndCca (MlKem768PublicKey)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def node (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (OracleComp (Spec n mlSource KemSK)) := fun query =>
  simulateQ (RegistrationNativeKemRouting.route true)
    (simulateQ RegistrationNativeKemFrontendInterface.lift
      (RegistrationNativeKemServerInterface.agreement setup checks query))

noncomputable def callbacks (setup : Setup base KemSK) (checks : Checks) :=
  node (n := n) (mlSource := mlSource) setup checks ∘ₛ RegistrationAgreementRoot.callbacks

def preparationKey (key : MlKem768PublicKey) :
    (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhBeaconPhase2Preparation.Word32).Domain → Prop
  | .encapsulate actual => actual = key
  | _ => True

private theorem preparation_queries (verified : PqxdhServerRootPreparation.Verified registration.InitPacket) :
    (PqxdhServerRootPreparation.collectVerified (E := Unit)
      (Shared := PqxdhBeaconPhase2Preparation.Word32) verified).AllQueriesSatisfy (preparationKey verified.keys.pqKey) := by
  unfold PqxdhServerRootPreparation.collectVerified
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | (simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, OptionT.run_failure,
        OptionT.run_pure, Option.elimM, Option.elim_some, Option.elim_none, bind_map_left,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false])
    | exact allQueriesSatisfy_pure _ _
    | (rw [allQueriesSatisfy_query_bind_iff]; constructor)
    | (intro answer; cases answer)
    | rfl
    | trivial

def agreementKey (key : MlKem768PublicKey) : RegistrationAgreementExecutor.Spec.Domain → Prop
  | .encapsulate actual => actual = .Some (RegistrationAgreementRoot.pqArray key)
  | _ => True

private theorem core_queries (setup : Setup base KemSK) (checks : Checks)
    (key : MlKem768PublicKey) (query : RegistrationAgreementExecutor.Spec.Domain)
    (allowed : agreementKey key query) :
    (RegistrationNativeKemServerInterface.agreementCore (n := n) (mlSource := mlSource) setup checks query).AllQueriesSatisfy
      (hasKey (ambient := RegistrationNativeKemServerInterface.Ambient n mlSource) (KemSK := KemSK) key) := by
  cases query with
  | encapsulate actual =>
      change actual = .Some (RegistrationAgreementRoot.pqArray key) at allowed
      subst actual
      simp only [RegistrationNativeKemServerInterface.agreementCore,
        RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
        RegistrationNativeKemInterface.server]
      split
      · simp only [RegistrationNativeKemInterface.encapsulate,
          simulateQ_map, simulateQ_spec_query, RegistrationNativeKemServerInterface.lift]
        apply (isQueryBound_map_iff _ _ () _ _).mpr
        change OracleComp.AllQueriesSatisfy (((RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query
          (.inr (.inr (RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray key))))) :
            OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) _)
            (hasKey (ambient := RegistrationNativeKemServerInterface.Ambient n mlSource) (KemSK := KemSK) key)
        rw [allQueriesSatisfy_query_iff]
        change RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray key) = key
        apply Subtype.ext
        simp [RegistrationRootInput.pqKey, RegistrationAgreementRoot.pqArray, absBytes,
          List.map_map, Function.comp_def]
      · exact allQueriesSatisfy_pure _ _
  | _ =>
      simp only [RegistrationNativeKemServerInterface.agreementCore,
        RegistrationNativeKemServerInterface.primitive, QueryImpl.apply_compose,
        RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other,
        RegistrationNativeKemServerInterface.lift, simulateQ_spec_query, simulateQ_pure,
        allQueriesSatisfy_query_iff, allQueriesSatisfy_pure, hasKey]

private theorem agreement_queries (setup : Setup base KemSK) (checks : Checks)
    (key : MlKem768PublicKey) (query : RegistrationAgreementExecutor.Spec.Domain)
    (allowed : agreementKey key query) :
    (RegistrationNativeKemServerInterface.agreement (n := n) (mlSource := mlSource) setup checks query).AllQueriesSatisfy
      (hasKey (ambient := RegistrationNativeKemServerInterface.Ambient n mlSource) (KemSK := KemSK) key) := by
  unfold RegistrationNativeKemServerInterface.agreement
  apply allQueriesSatisfy_bind
  · unfold RegistrationNativeKemServerInterface.modify
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro before
      exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · intro ignored
    exact core_queries setup checks key query allowed

private theorem node_queries (setup : Setup base KemSK) (checks : Checks)
    (key : MlKem768PublicKey) (query : RegistrationAgreementExecutor.Spec.Domain)
    (allowed : agreementKey key query) :
    (node (n := n) (mlSource := mlSource) setup checks query).AllQueriesSatisfy
      (hasKey (ambient := RegistrationNativeKemParsedRouting.Ambient n mlSource) (KemSK := KemSK) key) := by
  unfold node
  apply RegistrationNativeKemCutKey.simulate_allowed _
    (hasKey (ambient := RegistrationNativeKemFrontendInterface.Ambient n mlSource) (KemSK := KemSK) key) key
  · intro request admitted
    rcases request with request | (request | actual)
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · simpa only [RegistrationNativeKemRouting.route, ite_true, allQueriesSatisfy_query_iff,
        hasKey] using admitted
  · apply RegistrationNativeKemCutKey.simulate_allowed _
      (hasKey (ambient := RegistrationNativeKemServerInterface.Ambient n mlSource) (KemSK := KemSK) key) key
    · intro request admitted
      rcases request with request | (request | actual)
      · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
      · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
      · simpa only [RegistrationNativeKemFrontendInterface.lift, allQueriesSatisfy_query_iff,
          hasKey] using admitted
    · exact agreement_queries setup checks key query allowed

private theorem callback_queries (setup : Setup base KemSK) (checks : Checks)
    (key : MlKem768PublicKey)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhBeaconPhase2Preparation.Word32).Domain)
    (allowed : preparationKey key query) :
    (callbacks (n := n) (mlSource := mlSource) setup checks query).AllQueriesSatisfy
      (hasKey (ambient := RegistrationNativeKemParsedRouting.Ambient n mlSource) (KemSK := KemSK) key) := by
  cases query <;> simp only [callbacks, QueryImpl.apply_compose, RegistrationAgreementRoot.callbacks,
    simulateQ_pure, simulateQ_map, simulateQ_spec_query]
  all_goals first
    | exact allQueriesSatisfy_pure _ _
    | exact node_queries setup checks key _ (by trivial)
    | apply (isQueryBound_map_iff _ _ () _ _).mpr
  exact node_queries setup checks key _ (congrArg (fun actual => core.option.Option.Some
    (RegistrationAgreementRoot.pqArray actual)) allowed)

/-- The actual authenticated native collector's first getter uses precisely its verified PQ coordinate. -/
theorem collect_queries (setup : Setup base KemSK) (checks : Checks)
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket) :
    (simulateQ (callbacks (n := n) (mlSource := mlSource) setup checks)
      (PqxdhServerRootPreparation.collectVerified verified)).AllQueriesSatisfy
      (hasKey (ambient := RegistrationNativeKemParsedRouting.Ambient n mlSource) (KemSK := KemSK) verified.keys.pqKey) :=
  RegistrationNativeKemCutKey.simulate_allowed _ (preparationKey verified.keys.pqKey) verified.keys.pqKey
    (callback_queries setup checks verified.keys.pqKey) _ (preparation_queries verified)

attribute [local irreducible] PqxdhServerRootPreparation.collectVerified

/-- A successful collector input cannot be obtained before the literal getter is answered. -/
theorem collect_complete_impossible {S : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (implementation : QueryImpl (Spec n mlSource KemSK) (StateT S ProbComp))
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhBeaconPhase2Preparation.Word32)
    (before after : S)
    (supported : (RegistrationNativeKemCut.Cut.complete (some input), after) ∈ support
      ((RegistrationNativeKemCut.scan implementation
        (simulateQ (callbacks setup checks) (PqxdhServerRootPreparation.collectVerified verified)) 0).run before)) : False := by
  have stopped := RegistrationNativeKemCutStop.completed_support implementation _ (some input) before after supported
  apply RegistrationNativeKemStoppedGetter.collect_no_input setup checks verified input
  simp only [RegistrationNativeKemStoppedGetter.callbacks, QueryImpl.simulateQ_compose]
  change some (some input) ∈ support (simulateQ (RegistrationNativeKemStoppedGetter.stop ∘ₛ node setup checks)
    (simulateQ RegistrationAgreementRoot.callbacks (PqxdhServerRootPreparation.collectVerified verified))).run
  rw [QueryImpl.simulateQ_compose]
  simpa only [callbacks, QueryImpl.simulateQ_compose,
    RegistrationNativeKemStoppedGetter.stop] using stopped

/-- The first getter reached by the full native Server agreement carries the authenticated PQ key; arbitrary post-root controllers remain after the suspended getter. -/
theorem agreement_pending_key {S : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (implementation : QueryImpl (Spec n mlSource KemSK) (StateT S ProbComp))
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (history : RegistrationReplaySchedule.State)
    (actual : MlKem768PublicKey)
    (next : (PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret) →
      OracleComp (Spec n mlSource KemSK) (RustM agreement.AgreementEffect)) (before after : S)
    (supported : (RegistrationNativeKemCut.Cut.pending actual next, after) ∈ support
      ((RegistrationNativeKemCut.scan implementation (simulateQ (node setup checks)
        (RegistrationReplaySchedule.begin control authenticated history)) 0).run before)) :
    actual = RegistrationRootInput.pqKey authenticated.registration.beacon_pq_public_key := by
  rw [RegistrationReplaySchedule.begin_eq] at supported
  split at supported
  · simp only [simulateQ_pure] at supported
    change (RegistrationNativeKemCut.Cut.pending actual next, after) ∈
      support (pure (RegistrationNativeKemCut.Cut.complete (.ok (.Rejected .None)), before) :
        ProbComp (RegistrationNativeKemCut.Cut (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK
          (RustM agreement.AgreementEffect) × S)) at supported
    simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  · rw [RegistrationAgreementRoot.server_normalized control packet authenticated] at supported
    simp only [RegistrationAgreementRoot.normalized, simulateQ_bind,
      ← QueryImpl.simulateQ_compose] at supported
    change (RegistrationNativeKemCut.Cut.pending actual next, after) ∈ support
      ((RegistrationNativeKemCut.scan implementation
        (simulateQ (callbacks setup checks) (PqxdhServerRootPreparation.collectVerified
          (RegistrationRootInput.verified packet authenticated)) >>= _) 0).run before) at supported
    rw [RegistrationNativeKemCutKey.scan_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨cut, reached⟩, prefixSupport, tail⟩ := supported
    cases cut with
    | complete input =>
        cases input with
        | some input => exact False.elim (collect_complete_impossible setup checks implementation _ input before reached prefixSupport)
        | none =>
            simp only [simulateQ_pure] at tail
            change (RegistrationNativeKemCut.Cut.pending actual next, after) ∈
              support (pure (RegistrationNativeKemCut.Cut.complete (.ok (.Rejected .None)), reached) :
                ProbComp (RegistrationNativeKemCut.Cut (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK
                  (RustM agreement.AgreementEffect) × S)) at tail
            simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at tail
    | pending key resume =>
        simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
          RegistrationNativeKemCut.Cut.pending.injEq] at tail
        have selected := RegistrationNativeKemCutKey.pending_key implementation _ _
          (collect_queries setup checks (RegistrationRootInput.verified packet authenticated))
          key resume before reached prefixSupport
        exact tail.1.1.trans selected

end BeaconcryptCore.Computational.RegistrationNativeKemGetterKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemGetterKey.collect_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemGetterKey.collect_queries
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemGetterKey.collect_complete_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemGetterKey.collect_complete_impossible
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemGetterKey.agreement_pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemGetterKey.agreement_pending_key
