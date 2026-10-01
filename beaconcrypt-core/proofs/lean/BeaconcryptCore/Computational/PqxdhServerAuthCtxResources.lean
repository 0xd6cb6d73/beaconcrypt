import BeaconcryptCore.Computational.PqxdhServerAuthCtxExperiment
import BeaconcryptCore.Computational.PqxdhServerAuthStopResources

/-! Complete source and reduction query accounting for the actual sampled ordinary CTX authentication client. -/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxResources
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthSourceCosts PqxdhServerAuthPendingBudget
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Every actual compiler route fits the complete source-work bill, retaining all pre-refusal calls. This is a conservative total component-query cap, not a zero-cost ambient interface. -/
theorem route_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (caps : KemCaps) (bounded : KemBound setup caps) (select : Bool)
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthCtxHandler.route setup codec checks context rest select query).run.run state).IsTotalQueryBound
      (entryBill caps query state.1.1) := by
  cases query
  case inr query =>
    cases query
    case finish raw =>
      simpa only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp,
        StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff, entryBill] using
        (PqxdhServerAuthCtxFinishBounds.finish_total setup codec context rest select caps bounded raw state).mono
          (Nat.mul_le_mul_right _ (Nat.add_le_add_left (by decide : 65 ≤ 128) _))
    case build session payload =>
      simpa only [PqxdhServerAuthCtxHandler.route, entryBill] using
        ((PqxdhServerAuthCtxBuildBounds.build_bills setup.source codec checks rest session payload state).1).mono
          (show slotWeight (state.1.1.pending session) ≤ 64 * slotWeight (state.1.1.pending session) by omega)
    case accept raw =>
      simpa only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp,
        StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff, entryBill] using
        PqxdhServerAuthCtxStateBounds.accept_total setup codec checks context select caps bounded raw state
    case hmac key message =>
      simpa only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp,
        StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff, entryBill] using
        PqxdhServerAuthCtxStateBounds.hmac_total setup context key message state
    case hash bytes =>
      simp [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp,
        StateT.run_map, IsTotalQueryBound, PqxdhServerAuthCtxState.hash,
        PqxdhServerAuthCtxAmbient.hash, entryBill, StateT.run_lift]
    case reveal keyId =>
      simpa only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp,
        StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff, entryBill] using
        PqxdhServerAuthCtxStateBounds.reveal_total keyId state
  case inl coin =>
    simpa only [PqxdhServerAuthCtxHandler.route, OptionT.run_lift, bind_pure_comp,
      StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff, entryBill] using
      (PqxdhServerAuthCtxStateBounds.coin_bills coin state).1

/-- Actual designation and sticky-refusal settlement add no component query to the full route bill. -/
theorem handler_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (caps : KemCaps) (bounded : KemBound setup caps) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state).IsTotalQueryBound
      (entryBill caps query state.1.1) := by
  simpa only [PqxdhServerAuthCtxHandler.handler, OptionT.run_mk, StateT.run,
    IsTotalQueryBound, isQueryBound_map_iff] using
    route_total setup codec checks context rest caps bounded
      (!state.2 && hiddenDesignated Q j query state.1) query state

/-- The complete adaptive optional compiler pays every component request using the actual source potential and concrete callback footprints. -/
theorem stopped_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (caps : KemCaps) (bounded : KemBound setup caps) (Q : Nat) (j : Fin (Q + 1))
    (client : OracleComp ServerAuthSpec Result) (budget : Fin 4 → Nat)
    (queries : ∀ i, client.IsQueryBoundP (entryClasses i) (budget i))
    (state : Local KemSK × Option Nat) (valid : ResourceValid state.1.1.1) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) client).run.run state).IsTotalQueryBound
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
      have footprint := (PqxdhServerAuthCtxHandlerBounds.handler_footprint setup codec checks context rest Q j
        query before.1 original originalSupported value reply).1
      exact ⟨ResourceStep.valid query before.1.1.1 original.2.1.1 invariant footprint,
        entry_potential_step caps query before.1.1.1 original.2.1.1 invariant footprint available positive⟩

/-- The literal adaptive continuation pays every component call from the four original adversary budgets and the actual empty initial state. -/
theorem continuation_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) :
    (PqxdhServerAuthCtxExperiment.continuation setup codec checks adversary Q j context rest).IsTotalQueryBound
      (entryRunBudget caps qCoin Q qHash qH) := by
  simp only [PqxdhServerAuthCtxExperiment.continuation, IsTotalQueryBound, isQueryBound_map_iff,
    PqxdhServerAuthCtxExperiment.execution]
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
theorem client_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  unfold PqxdhServerAuthCtxExperiment.client
  have combined := isTotalQueryBound_bind
    (PqxdhServerAuthCtxAmbient.coin_bound _ _ (context_uniform setup codec caps bounded))
    (fun context => isTotalQueryBound_bind
      (PqxdhServerAuthCtxAmbient.coin_bound _ _ PqxdhServerAuthCtxMaterial.residual_bound)
      (fun rest => continuation_total setup codec checks caps bounded adversary qCoin Q qHash qH
        coins accepts hashes rom j context rest))
  exact combined.mono (by unfold entryReductionBudget; omega)

/-- Exact interpreted-program equality transfers the actual full source uniform bill, including its component poststate, without using a distributional resource shortcut. -/
theorem client_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (key : RootOutput) :
    ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)).run
      AdaptiveCtxDynamicKnownKeys.initialSource).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  have charged := isTotalQueryBound_bind (context_uniform setup codec caps bounded)
    (fun context => isTotalQueryBound_bind PqxdhServerAuthCtxMaterial.residual_bound
      (fun rest => stopped_distinguisher_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
        coins accepts hashes rom false j context (PqxdhServerAuthCtxMaterial.output key rest)))
  have paid := charged.mono (show 128 + caps.keygenCost + (76 + entryRunBudget caps qCoin Q qHash qH) ≤
      entryReductionBudget caps qCoin Q qHash qH + 76 by unfold entryReductionBudget; omega)
  rw [← PqxdhServerAuthCtxExperiment.client_source setup codec checks adversary Q j key] at paid
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using paid

/-- The whole ordinary source game adds the challenger's 32-byte selected key to the exact U+76 interpreted client bill. -/
theorem source_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 108) := by
  unfold AdaptiveCtxDynamicKnownKeys.sourceGame
  exact (isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun key => client_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins accepts hashes rom j key)).mono (by omega)

/-- The actual client has explicit conservative uniform/hash route bills alongside its sharp selected-seal/raw caps. -/
theorem client_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    let client := PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j
    client.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      client.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  have total := client_total setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP,
    IsQueryBoundP.of_imp (fun _ _ => True.intro) total.isQueryBoundP,
    PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j⟩

/-- The actual all-attempt authentication observer adds no request and keeps the full four-class client ledger. -/
theorem observer_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    let observer := RawCtxSelectedAuthenticationObserver.decision
      (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)
    observer.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      observer.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      observer.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      observer.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  simp only [RawCtxSelectedAuthenticationObserver.decision_queries]
  exact client_bills setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j

/-- The concrete final CTX integrity consumer receives a discharged shared-hash-route bound for the exact original client. -/
theorem client_hash (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute (entryReductionBudget caps qCoin Q qHash qH + 76) :=
  (client_bills setup codec checks caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j).2.1

/-- The same constructed ordinary ReceiveSpec reduction retains explicit uniform, shared-hash, selected-seal and raw-attempt bounds after real known-key simulation. -/
theorem reduction_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    let observer := RawCtxSelectedAuthenticationObserver.decision
      (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j)
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient setup.source.crypto observer
    reduction.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      reduction.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash
        (entryReductionBudget caps qCoin Q qHash qH + 76) ∧
      reduction.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 ∧
      reduction.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 1 := by
  have bills := observer_bills setup codec checks caps bounded adversary qCoin Q qHash qH
    coins accepts hashes rom j
  exact AdaptiveCtxDynamicKnownBounds.decision_budgets setup.source.crypto _ _ _ 1 1
    bills.1 bills.2.1 bills.2.2.1 bills.2.2.2

end BeaconcryptCore.Computational.PqxdhServerAuthCtxResources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.route_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.route_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.handler_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.handler_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.stopped_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.stopped_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.continuation_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.continuation_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.source_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.source_game_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.observer_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.observer_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.client_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.reduction_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxResources.reduction_bills
