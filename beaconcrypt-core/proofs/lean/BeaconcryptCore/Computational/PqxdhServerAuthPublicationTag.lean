import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivateView

/-! Unconditional tag guessing after the exact ordinary random first-seal view. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationTag
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open PqxdhServerAuthPublicationPrivateView
variable {Result : Type}

set_option maxRecDepth 100000 in
/-- A fixed optional candidate equals a freshly sampled tag with at most its exact point mass. -/
theorem fixed_guess (candidate : Option (FixedBytes 16)) :
    Pr{let tag ← $ᵗ (FixedBytes 16)}[candidate = some tag] ≤
      (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
  cases candidate with
  | none =>
      exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun tag impossible => Option.some_ne_none tag impossible.symm)
        zero_le
  | some value =>
      rw [prEvent_congr _ (fun tag => some value = some tag) (fun tag => tag = value)
        fun tag => ⟨fun same => (Option.some.inj same).symm, fun same => same ▸ rfl⟩]
      exact (SampleableType.prEvent_uniformSample_eq_singleton value).le

/-- A complete probabilistic continuation not given the tag has the same unconditional guessing bound, even when its reply is adaptive or absent. -/
theorem independent_guess (work : ProbComp Result) (guess : Result → Option (FixedBytes 16)) :
    Pr{let result ← (do
          let tag ← $ᵗ (FixedBytes 16)
          let result ← work
          pure (tag, result))}[guess result.2 = some result.1] ≤
      (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
  have same := OracleComp.EvalDistEq.bind_bind_swap
    ($ᵗ (FixedBytes 16)) work (fun tag result => pure (tag, result))
  rw [same.prEvent_eq (fun result => guess result.2 = some result.1)]
  refine prEvent_bind_le_of_forall_le _ _ _ fun result => ?_
  rw [bind_pure_comp _ ($ᵗ (FixedBytes 16)), prEvent_map]
  exact fixed_guess (guess result)

/-- Compare the chosen candidate with the actual optional selected record; no record means no hit. -/
def Hit (guess : Result → Option (FixedBytes 16)) : Option CtxRomRecord × (Result × State) → Prop
  | (none, _) => False
  | (some record, result) => guess result.1 = some ⟨record.tag, record.tagLength⟩

/-- The exact first-seal/source-suffix law bounds a withheld-tag guess without any predicate on a writer outcome. -/
theorem first_seal_guess (decode : AdaptiveCtxReceive.RawDecoder) (input : CtxSealInput) (state : State)
    (unused : Unused state) (work : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (noRaw : work.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 0)
    (guess : Result → Option (FixedBytes 16)) :
    Pr{let x ← (do
      let sealed ← step decode (.inl (.inr (.inr input))) state
      let final ← Prod.map id project <$> (simulateQ (impl decode) work).run sealed.2
      pure (sealed.1, final) : ProbComp (Option CtxRomRecord × (Result × State)))}[(Hit guess) x] ≤
      ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [first_seal_suffix decode input state unused work noSeal noRaw, ← ctxValidationTag_card]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun body _ => ?_
  convert independent_guess (do
    let _ ← $ᵗ CtxDigest
    Prod.map id project <$> (simulateQ (impl decode) work).run (afterSeal input state))
    (fun result => guess result.1) using 1
  simp only [bind_assoc, pure_bind, Hit, List.Vector.mk_toList]

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

