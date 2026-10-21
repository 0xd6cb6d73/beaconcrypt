import BeaconcryptCore.Computational.PqxdhInitialSourceSecrecyResources

/-!
The original stopped source continuation may run arbitrary later records and permitted descendant reveals. This module bounds its actual known-input candidate event on the original publication/freshness event, through the existing target-input-free interpreter. The independent child is one complete76 response; later public and private fallback HKDF work stays real. Retained predecessor retries and global send-origin attribution remain separate events and are not called guesses of the hidden input.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhInitialCommonSecrecy
variable {ι Context M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (view : View Context extra M P I D K X Response Shared A N C S B)

noncomputable def clearBad (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool := by
  classical
  exact match context.1 with
  | .inl _ => pure false
  | .inr pending => (fun result => decide (target ∈ result.2.1.2 ∧ result.2.2 = false)) <$>
      PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode view.continuation
        (pending, context.2) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)

noncomputable def freshBad (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool := by
  classical
  exact match context.1 with
  | .inl _ => pure false
  | .inr pending => (fun result => decide (target ∈ result.2.1.2 ∧
      PqxdhInitialPrivateCheckedFreshness.actualDecision target (view.earlier pending) view.disclosed
        (fun result => PqxdhInitialPublishedEvent.Gate view.selected view.number result.1.1) result = true)) <$>
      PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode view.continuation
        (pending, context.2) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)

set_option backward.isDefEq.respectTransparency false in
/-- The source clear-disclosure candidate probability pays two copies of the same full target-input-free candidate event, including every later callback and saved candidate. -/
theorem clear_bound (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) :
    Pr[= true | clearBad source writer mark sender route decode view context target output] ≤
      2 * Pr[= true | PqxdhInitialCommonSecrecy.bad source writer mark sender route decode view context target output] := by
  rcases context with ⟨common | pending, entry⟩
  · simp [clearBad]
  · have bound := PqxdhInitialPrivateCheckedFreshness.good_alias_bound source writer mark sender route decode
      view.continuation (pending, entry) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)
    have lifted := ENNReal.ofReal_le_ofReal bound
    simpa only [clearBad, PqxdhInitialCommonSecrecy.bad, observed, Functor.map_map, Function.comp_def,
      candidates, PqxdhInitialParentStoppedHop.candidates, ← probEvent_eq_eq_probOutput, probEvent_map,
      decide_eq_true_eq, PqxdhInitialCheckedFreshness.maskedRun, PqxdhInitialPrivateCheckedFreshness.maskedRun,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_toReal probEvent_ne_top] using lifted

/-- The original native publication and byte freshness event excludes direct target disclosure; it does not exclude later descendant revelations. -/
theorem fresh_le_clear (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) :
    Pr[= true | freshBad source writer mark sender route decode view context target output] ≤
      Pr[= true | clearBad source writer mark sender route decode view context target output] := by
  classical
  rcases context with ⟨common | pending, entry⟩
  · simp [freshBad, clearBad]
  · simp only [freshBad, clearBad, ← probEvent_eq_eq_probOutput, probEvent_map]
    apply probEvent_mono
    intro result reached event
    have event := of_decide_eq_true event
    apply decide_eq_true
    have actual : PqxdhInitialPublishedEvent.Gate view.selected view.number result.1.1 ∧
        RawCtxLiveLineage.Fresh
          (result.1.2.map (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) ++ view.earlier pending)
          view.disclosed result.1.1.2.1.roles.2 := by
      simpa only [PqxdhInitialPrivateCheckedFreshness.actualDecision, decide_eq_true_eq] using event.2
    have fresh := (PqxdhInitialPrivateCheckedFreshness.checked_fresh source writer mark sender route decode
      view.continuation (pending, entry) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)
      (view.earlier pending) view.remaining (view.depth pending) result reached).mp actual.2
    exact ⟨event.1, RawCtxFamilyFreshnessProxy.fresh_clear _ _ view.disclosed _ _
      (PqxdhInitialPrivateCheckedFreshness.checked_invariant source writer mark sender route decode
        view.continuation (pending, entry) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)
        result reached).1 fresh⟩

/-- Original Fresh gates the source event; no future-compromise restriction is added. -/
theorem fresh_bound (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) :
    Pr[= true | freshBad source writer mark sender route decode view context target output] ≤
      2 * Pr[= true | PqxdhInitialCommonSecrecy.bad source writer mark sender route decode view context target output] :=
  (fresh_le_clear source writer mark sender route decode view context target output).trans
    (clear_bound source writer mark sender route decode view context target output)

noncomputable def childSample (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  let output ← $ᵗ FullOutput
  pure (pair, output)

noncomputable def future (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool :=
  childSample sample address >>= fun value =>
    freshBad source writer mark sender route decode view value.1.1 value.1.2 value.2

noncomputable def masked (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool :=
  childSample sample address >>= fun value =>
    PqxdhInitialCommonSecrecy.bad source writer mark sender route decode view value.1.1 value.1.2 value.2

/-- The original joint parent draw and complete child draw are averaged together, retaining the factor two without conditioning on source success. -/
theorem future_masked (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    Pr[= true | future source writer mark sender route decode view sample address] ≤
      2 * Pr[= true | masked source writer mark sender route decode view sample address] := by
  rw [future, masked, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simpa only [mul_left_comm, ← ENNReal.tsum_mul_left] using
    (ENNReal.tsum_le_tsum fun value => mul_le_mul' (le_refl (Pr[= value | childSample sample address]))
      (fresh_bound source writer mark sender route decode view value.1.1 value.1.2 value.2))

/-- The masked continuation has exactly the existing delayed-input candidate distribution, with all public evaluations and future source operations retained. -/
theorem masked_probability (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    Pr[= true | masked source writer mark sender route decode view sample address] =
      Pr[fun pair => pair.1 ∈ candidates pair.2 |
        RawCtxSelectedParentCandidates.uniform sample address (observed source writer mark sender route decode view)] := by
  simp only [masked, childSample, RawCtxSelectedParentCandidates.sample, RawCtxSelectedParentCandidates.uniform,
    RawCtxSelectedParentSampler.original, PqxdhInitialCommonSecrecy.bad,
    bind_assoc, pure_bind]
  simp only [bind_pure_comp]
  simp only [← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, decide_eq_true_eq]

/-- Known-input aliases anywhere in the original fresh source suffix pay the complete candidate cap. Only the already justified independent parent/child comparison uses this statistical bound. -/
theorem future_bound (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress)
    (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (observed source writer mark sender route decode view context output) →
        (candidates result).length ≤ qCandidates) :
    Pr[= true | future source writer mark sender route decode view sample address] ≤
      2 * ((qCandidates : ENNReal) / (2 ^ 256 : ENNReal)) := by
  have compared := future_masked source writer mark sender route decode view sample address
  rw [masked_probability] at compared
  exact compared.trans (mul_le_mul_right (RawCtxSelectedParentCandidates.uniform_bound_vcvioLegacy sample address
    (observed source writer mark sender route decode view) candidates qCandidates bounded) 2)

set_option maxRecDepth 2048 in
/-- The target-free candidate computation pays the original sampler, both full76 draws and every continuation query. No work is inferred free from distributional equality. -/
theorem masked_uniform (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output,
      (observed source writer mark sender route decode view context output).IsTotalQueryBound qObserve) :
    (masked source writer mark sender route decode view sample address).IsTotalQueryBound
      (qSample + (76 + (76 + qObserve))) := by
  simp only [masked, childSample, RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  apply isTotalQueryBound_bind sampleBound
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
  intro parent
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
  intro child
  simpa only [PqxdhInitialCommonSecrecy.bad, IsTotalQueryBound, isQueryBound_map_iff] using
    observeBound (context, fromOutput (address context) parent) child

end BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.clear_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.clear_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.fresh_le_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.fresh_le_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.fresh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.fresh_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.future_masked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.future_masked

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.masked_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.masked_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.future_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.future_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.masked_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates.masked_uniform
