-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAverage
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability
open RegistrationNativeStageTrace (Call)
open RegistrationNativePlatformOriginCallbackCut (Cut Outcome scan resume markedResume)
open RegistrationNativePlatformOriginCallbackTrace (track Result selected)
variable {Q S A : Type} {spec : OracleSpec Q}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : MeasurableSpace (A × S) := ⊤
local instance : DiscreteMeasurableSpace (A × S) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Outcome spec S A) := ⊤
local instance : DiscreteMeasurableSpace (Outcome spec S A) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Option (Call spec S) × (A × S)) := ⊤
local instance : DiscreteMeasurableSpace (Option (Call spec S) × (A × S)) := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Result spec S A) := ⊤
local instance : DiscreteMeasurableSpace (Result spec S A) := ⟨fun _=>trivial⟩
/-- An ordinal contributes only when that cut exists; the event sees its complete cut and original final source result. -/
def SelectedEvent (event : Call spec S → A × S → Prop)
    (result : Option (Call spec S) × (A × S)) : Prop :=
  match result.1 with
  | none => False
  | some cut => event cut result.2

/-- Completion before the selected callback contributes probability zero. -/
theorem marked_complete (service : QueryImpl spec (StateT S ProbComp))
    (event : Call spec S → A × S → Prop) (value : A × S) :
    𝒟[markedResume service (.inl value)] {result | SelectedEvent event result} = 0 := by
  classical
  simp only [markedResume]
  rw [← prEvent_eq_evalDist_of_discrete, prEvent_pure]
  simp [SelectedEvent]

/-- The selected continuation bound is averaged over the complete unchanged supported prefix, without conditioning on a later result. -/
theorem selected_bound (counted : spec.Domain → Prop) (service : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (index : Nat) (state : S)
    (event : Call spec S → A × S → Prop) (cap : ℝ≥0∞)
    (bounded : ∀ cut, Sum.inr cut ∈ support (scan counted service work index state) →
      𝒟[markedResume service (.inr cut)] {result | SelectedEvent event result} ≤ cap) :
    𝒟[track counted service work state] {result | SelectedEvent event (selected index result)} ≤ cap := by
  have mapped : 𝒟[selected index <$> track counted service work state] {result | SelectedEvent event result} =
      𝒟[track counted service work state] {result | SelectedEvent event (selected index result)} := by
    rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  rw [← mapped, RegistrationNativePlatformOriginCallbackTrace.track_selected]
  apply PqxdhRecordFactsOriginAverage.bind_le
  intro outcome supported
  cases outcome with
  | inl value => rw [marked_complete]; exact bot_le
  | inr cut => exact bounded cut supported

/-- A finite union over attempted ordinals is taken in the same complete original source trace. -/
theorem finite_union_bound (counted : spec.Domain → Prop) (service : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (state : S)
    (event : Call spec S → A × S → Prop) (count : Nat) (cap : ℝ≥0∞)
    (bounded : ∀ index : Fin count, ∀ cut,
      Sum.inr cut ∈ support (scan counted service work index.val state) →
        𝒟[markedResume service (.inr cut)] {result | SelectedEvent event result} ≤ cap) :
    𝒟[track counted service work state]
      {result | ∃ index : Fin count, SelectedEvent event (selected index.val result)} ≤ count * cap := by
  have cover : {result : Result spec S A | ∃ index : Fin count, SelectedEvent event (selected index.val result)} =
      ⋃ index : Fin count, {result | SelectedEvent event (selected index.val result)} := by
    ext result
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [cover]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun index =>
    selected_bound counted service work index.val state event cap (bounded index)).trans ?_)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]

/-- Every cut in a supported trace is covered by one of the original charged callback ordinals. -/
theorem trace_event_cover (counted : spec.Domain → Prop) (service : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (state : S)
    (event : Call spec S → A × S → Prop) (count : Nat)
    (bounded : work.IsQueryBoundP counted count)
    (result : Result spec S A) (supported : result ∈ support (track counted service work state))
    (hit : ∃ cut ∈ result.1, event cut result.2) :
    ∃ index : Fin count, SelectedEvent event (selected index.val result) := by
  obtain ⟨cut, member, hit⟩ := hit
  obtain ⟨index, within, same⟩ := List.mem_iff_getElem.mp member
  have length := RegistrationNativePlatformOriginCallbackTrace.track_length counted service work count bounded state result supported
  refine ⟨⟨index, Nat.lt_of_lt_of_le within length⟩, ?_⟩
  have chosen : result.1[index]? = some cut := List.getElem?_eq_some_iff.mpr ⟨within, same⟩
  simpa only [selected, SelectedEvent, chosen] using hit

/-- The actual finite attempted-callback allowance multiplies a pointwise selected continuation bound once, without independence between ordinal events. -/
theorem any_callback_bound (counted : spec.Domain → Prop) (service : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (state : S)
    (event : Call spec S → A × S → Prop) (count : Nat) (cap : ℝ≥0∞)
    (billed : work.IsQueryBoundP counted count)
    (bounded : ∀ index : Fin count, ∀ cut,
      Sum.inr cut ∈ support (scan counted service work index.val state) →
        𝒟[markedResume service (.inr cut)] {result | SelectedEvent event result} ≤ cap) :
    𝒟[track counted service work state] {result | ∃ cut ∈ result.1, event cut result.2} ≤ count * cap := by
  refine le_trans ?_ (finite_union_bound counted service work state event count cap bounded)
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  intro result supported hit
  exact trace_event_cover counted service work state event count billed result supported hit

/-- An original source event inherits the attempted-callback union bound after its explicit supported-trace inclusion and local callback bound have been proved. -/
theorem source_event_bound (counted : spec.Domain → Prop) (service : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (state : S)
    (sourceEvent : A × S → Prop) (event : Call spec S → A × S → Prop)
    (count : Nat) (cap : ℝ≥0∞)
    (billed : work.IsQueryBoundP counted count)
    (covered : ∀ result ∈ support (track counted service work state), sourceEvent result.2 →
      ∃ cut ∈ result.1, event cut result.2)
    (bounded : ∀ index : Fin count, ∀ cut,
      Sum.inr cut ∈ support (scan counted service work index.val state) →
        𝒟[markedResume service (.inr cut)] {result | SelectedEvent event result} ≤ cap) :
    𝒟[(simulateQ service work).run state] {result | sourceEvent result} ≤ count * cap := by
  have original : 𝒟[(simulateQ service work).run state] {result | sourceEvent result} =
      𝒟[track counted service work state] {result | sourceEvent result.2} := by
    rw [← RegistrationNativePlatformOriginCallbackTrace.track_drop counted service work state]
    rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete, prEvent_map]
  rw [original]
  refine le_trans ?_ (any_callback_bound counted service work state event count cap billed bounded)
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  exact covered

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.marked_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.marked_complete


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.selected_bound


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.finite_union_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.finite_union_bound


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.trace_event_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.trace_event_cover


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.any_callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.any_callback_bound


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.source_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackProbability.source_event_bound
