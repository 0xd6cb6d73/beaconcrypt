import BeaconcryptCore.Computational.PqxdhServerAuthPublicationReference

/-! Complete all-reply resource bounds for the selected-writer publication reference. Changed source replies do not justify reusing a trace budget; these bounds follow its actual callbacks and resource potential. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthSourceCosts PqxdhServerAuthPendingBudget
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhServerAuthPublicationReference
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- Every mixed reference route fits the actual complete source-work potential, including all queries before writer failure or component refusal. -/
theorem route_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (caps : KemCaps) (bounded : KemBound setup caps) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((route setup codec checks context rest select query).run.run state).IsTotalQueryBound
      (entryBill caps query state.1.1) := by
  cases query with
  | inl coin => exact PqxdhServerAuthCtxResources.route_total setup codec checks context rest caps bounded select (.inl coin) state
  | inr query =>
      cases query with
      | build session payload =>
          simpa only [route, entryBill] using
            (build_bills setup.source codec checks rest session payload state).1.mono
              (show slotWeight (state.1.1.pending session) ≤ 64 * slotWeight (state.1.1.pending session) by omega)
      | accept raw => exact PqxdhServerAuthCtxResources.route_total setup codec checks context rest caps bounded select (.inr (.accept raw)) state
      | finish raw => exact PqxdhServerAuthCtxResources.route_total setup codec checks context rest caps bounded select (.inr (.finish raw)) state
      | hmac key message => exact PqxdhServerAuthCtxResources.route_total setup codec checks context rest caps bounded select (.inr (.hmac key message)) state
      | hash bytes => exact PqxdhServerAuthCtxResources.route_total setup codec checks context rest caps bounded select (.inr (.hash bytes)) state
      | reveal keyId => exact PqxdhServerAuthCtxResources.route_total setup codec checks context rest caps bounded select (.inr (.reveal keyId)) state

/-- Actual designation and sticky-refusal settlement add no component query to the full route bill. -/
theorem handler_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (caps : KemCaps) (bounded : KemBound setup caps) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j query).run.run state).IsTotalQueryBound
      (entryBill caps query state.1.1) := by
  simpa only [PqxdhServerAuthPublicationReference.handler, OptionT.run_mk, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff] using
    route_total setup codec checks context rest caps bounded
      (!state.2 && hiddenDesignated Q j query state.1) query state


/-- The complete adaptive optional compiler pays every component request using the actual source potential and concrete callback footprints. -/
theorem stopped_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (caps : KemCaps) (bounded : KemBound setup caps) (Q : Nat) (j : Fin (Q + 1))
    (client : OracleComp ServerAuthSpec Result) (budget : Fin 4 → Nat)
    (queries : ∀ i, client.IsQueryBoundP (entryClasses i) (budget i))
    (state : Local KemSK × Option Nat) (valid : ResourceValid state.1.1.1) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthPublicationReference.handler setup codec checks context rest Q j)) client).run.run state).IsTotalQueryBound
      (entryPotential caps budget state.1.1.1) := by
  rw [← isQueryBoundP_true_iff]
  apply optional_potential_invariant _ (fun state => ResourceValid state.1.1.1) entryClasses
    (fun _ => True) (fun budget state => entryPotential caps budget state.1.1.1)
    _ client budget queries state valid
  intro query before available invariant positive
  refine ⟨entryBill caps query before.1.1.1, ?_, entryBill_le caps query before.1.1.1 invariant available positive, ?_⟩
  · rw [PqxdhServerAuthCtxReserve.stopped, stopped_step, isQueryBoundP_map_iff]
    exact (handler_total setup codec checks context rest caps bounded Q j query before.1).isQueryBoundP
  intro result supported answer continues
  rw [PqxdhServerAuthCtxReserve.stopped, stopped_step] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨original, originalSupported, rfl⟩ := supported
  cases reply : original.1 with
  | none =>
      simp only [observe, reply] at continues
      cases continues
  | some value =>
      simp only [observe, reply] at continues ⊢
      have footprint := (PqxdhServerAuthPublicationReference.handler_footprint setup codec checks context rest Q j
        query before.1 original originalSupported value reply).1
      exact ⟨ResourceStep.valid query before.1.1.1 original.2.1.1 invariant footprint,
        entry_potential_step caps query before.1.1.1 original.2.1.1 invariant footprint available positive⟩


/-- The literal adaptive continuation pays every component call from the four original adversary budgets and the actual empty initial state. -/
theorem execution_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    (PqxdhServerAuthPublicationReference.execution setup codec checks adversary Q j context rest).IsTotalQueryBound
      (entryRunBudget caps qCoin Q qHash qH) := by
  simp only [PqxdhServerAuthPublicationReference.execution, IsTotalQueryBound,
    PqxdhServerAuthPublicationReference.stopped]
  apply (stopped_total setup codec checks context rest caps bounded Q j
    _ ![qCoin, Q, qHash, qH] ?_ _ ?_).mono
      (entry_initial_potential setup context caps qCoin Q qHash qH)
  · intro i
    fin_cases i
    · exact coins _
    · exact accepts _
    · exact hashes _
    · exact rom _
  · intro index token found
    cases found


/-- The complete executable client charges the real context sampler, all adaptive callbacks and the residual76 sampler. -/
theorem client_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  unfold PqxdhServerAuthPublicationReference.client
  simp only [bind_pure_comp]
  apply (isTotalQueryBound_bind
    (PqxdhServerAuthCtxAmbient.coin_bound _ _ (context_uniform setup codec caps bounded))
    (n₂ := 76 + entryRunBudget caps qCoin Q qHash qH) ?_).mono
      (show 128 + caps.keygenCost + (76 + entryRunBudget caps qCoin Q qHash qH) ≤
        entryReductionBudget caps qCoin Q qHash qH + 76 by unfold entryReductionBudget; omega)
  intro context
  apply isTotalQueryBound_bind
    (PqxdhServerAuthCtxAmbient.coin_bound _ _ PqxdhServerAuthCtxMaterial.residual_bound)
  intro rest
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    execution_total setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j context rest



/-- Both original samplers add no selected record request; retaining their full values and complete result does not add one either. -/
theorem client_record_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (client setup codec checks adversary Q j).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
    (client setup codec checks adversary Q j).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  unfold client
  simp only [bind_pure_comp]
  constructor
  · apply (isQueryBoundP_bind (PqxdhServerAuthCtxAmbient.coin_other _).2.1 (m := 1) ?_).mono (by omega)
    intro context _
    apply (isQueryBoundP_bind (PqxdhServerAuthCtxAmbient.coin_other _).2.1 (m := 1) ?_).mono (by omega)
    intro rest _
    simpa only [isQueryBoundP_map_iff] using (execution_record_bills setup codec checks adversary Q j context rest).1
  · apply (isQueryBoundP_bind (PqxdhServerAuthCtxAmbient.coin_other _).2.2 (m := 1) ?_).mono (by omega)
    intro context _
    apply (isQueryBoundP_bind (PqxdhServerAuthCtxAmbient.coin_other _).2.2 (m := 1) ?_).mono (by omega)
    intro rest _
    simpa only [isQueryBoundP_map_iff] using (execution_record_bills setup codec checks adversary Q j context rest).2

/-- The actual client has explicit conservative uniform/hash route bills alongside its sharp selected-seal/raw caps. -/
theorem client_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    let client := PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j
    client.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      client.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  have total := client_total setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP,
    client_record_bills setup codec checks adversary Q j⟩


end BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.route_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.route_total

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.handler_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.handler_total

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.stopped_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.stopped_total

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.execution_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.execution_total

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.client_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.client_total

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.client_record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.client_record_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.client_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceResources.client_bills
