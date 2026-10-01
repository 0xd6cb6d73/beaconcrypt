import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView

/-! Unconditional tag guessing after the exact ordinary random first-seal view. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open PqxdhServerAuthPublicationPrivateView
variable {Result : Type}

set_option maxRecDepth 100000 in
set_option linter.deprecated false in
/-- A fixed optional candidate equals a freshly sampled tag with at most its exact point mass. -/
theorem fixed_guess (candidate : Option (FixedBytes 16)) :
    Pr[fun tag => candidate = some tag | $ᵗ (FixedBytes 16)] ≤
      (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
  cases candidate <;> simp

set_option linter.deprecated false in
/-- A complete probabilistic continuation not given the tag has the same unconditional guessing bound, even when its reply is adaptive or absent. -/
theorem independent_guess (work : ProbComp Result) (guess : Result → Option (FixedBytes 16)) :
    Pr[fun result => guess result.2 = some result.1 |
      (do let tag ← $ᵗ (FixedBytes 16)
          let result ← work
          pure (tag, result))] ≤
      (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
  have same := OracleComp.DeferredSampling.evalSPMF_bind_comm
    ($ᵗ (FixedBytes 16)) work (fun tag result => pure (tag, result))
  rw [OracleComp.probEvent_congr' (fun _ _ => Iff.rfl) same]
  refine probEvent_bind_le_of_forall_le fun result _ => ?_
  simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using fixed_guess (guess result)

/-- Compare the chosen candidate with the actual optional selected record; no record means no hit. -/
def Hit (guess : Result → Option (FixedBytes 16)) : Option CtxRomRecord × (Result × State) → Prop
  | (none, _) => False
  | (some record, result) => guess result.1 = some ⟨record.tag, record.tagLength⟩

set_option linter.deprecated false in
/-- The exact first-seal/source-suffix law bounds a withheld-tag guess without any predicate on a writer outcome. -/
theorem first_seal_guess (decode : AdaptiveCtxReceive.RawDecoder) (input : CtxSealInput) (state : State)
    (unused : Unused state) (work : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : work.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 0)
    (guess : Result → Option (FixedBytes 16)) :
    Pr[Hit guess | (do
      let sealed ← step decode (.inl (.inr (.inr input))) state
      let final ← Prod.map id project <$> (simulateQ (impl decode) work).run sealed.2
      pure (sealed.1, final))] ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [first_seal_suffix decode input state unused work noSeal noRaw, ← ctxValidationTag_card]
  refine probEvent_bind_le_of_forall_le fun body _ => ?_
  convert independent_guess (do
    let _ ← $ᵗ CtxDigest
    Prod.map id project <$> (simulateQ (impl decode) work).run (afterSeal input state))
    (fun result => guess result.1) using 1
  simp only [bind_assoc, probEvent_bind_eq_tsum, probEvent_pure, Hit, List.Vector.mk_toList]

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag.fixed_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag.fixed_guess

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag.independent_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag.independent_guess

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag.first_seal_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag.first_seal_guess

