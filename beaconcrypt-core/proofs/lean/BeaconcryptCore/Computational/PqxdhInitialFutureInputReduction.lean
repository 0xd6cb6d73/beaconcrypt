import BeaconcryptCore.Computational.PqxdhInitialFutureInputCandidates

/-!
The same actual future known-input candidate event is charged with the real correlated child. Its target-input-free full-output tester evaluates the original fixed public HKDF on the actual adaptive candidate list; no independence of those candidates from a real child is assumed. The extra Extract and ordinary HMAC advantages, finite-image term and candidate evaluation count remain explicit.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhInitialCommonSecrecy PqxdhInitialFutureInputCandidates
variable {ι Context M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (view : View Context extra M P I D K X Response Shared A N C S B)


noncomputable def realFuture (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool :=
  RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
    freshBad source writer mark sender route decode view pair.1 pair.2 (RawCtxFullPreimageTester.production source pair.2)

noncomputable def realMasked (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool :=
  RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
    PqxdhInitialCommonSecrecy.bad source writer mark sender route decode view pair.1 pair.2 (RawCtxFullPreimageTester.production source pair.2)

/-- The real child's complete continuation pays the same factor two on its actual candidate event; no uniform-input guessing bound is used here. -/
theorem real_masked (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    Pr{let x ← realFuture source writer mark sender route decode view sample address}[x = true] ≤
      2 * Pr{let x ← realMasked source writer mark sender route decode view sample address}[x = true] := by
  rw [realFuture, realMasked, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  simpa only [mul_left_comm, ← ENNReal.tsum_mul_left] using
    (ENNReal.tsum_le_tsum fun pair => mul_le_mul' (le_refl (Pr{let x ← RawCtxSelectedParentCandidates.sample sample address}[x = pair]))
      (fresh_bound source writer mark sender route decode view pair.1 pair.2 (RawCtxFullPreimageTester.production source pair.2)))

/-- The mathematical private input test uses the same source sample and complete ordinary observer as the full-preimage reduction. -/
theorem real_masked_probability (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    Pr{let x ← realMasked source writer mark sender route decode view sample address}[x = true] =
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address) (observed source writer mark sender route decode view))}[pair.1 ∈ candidates pair.2] := by
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  rw [realMasked, RawCtxFullPreimageTester.actual]
  refine bindCongr _ _ _ _ _ fun pair => ?_
  obtain ⟨context, target⟩ := pair
  dsimp only
  rw [PqxdhInitialCommonSecrecy.bad, prEvent_map, prEvent_map]
  exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]

/-- The ordinary tester retains the exact joint parent/input sampler and the full original continuation, with coefficient one per primitive endpoint. -/
noncomputable def testerLoss (hmac : HmacSha512) (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) : ℝ :=
  RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer mark sender route decode view) +
    RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer mark sender route decode view)

/-- Real correlated-child known-input aliases on the original source Fresh event pay two full-preimage tests, with the explicit fixed-function image term and ordinary Extract/HMAC games. -/
theorem real_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    Pr{let x ← realFuture source writer mark sender route decode view sample address}[x = true] ≤
      2 * ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (testerLoss source writer mark sender route decode view hmac sample address)) := by
  have compared := real_masked source writer mark sender route decode view sample address
  rw [real_masked_probability] at compared
  exact compared.trans (mul_le_mul_right (RawCtxSelectedParentCandidates.real_bound source hmac correct sample address
    (observed source writer mark sender route decode view) candidates) 2)

end BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction.real_masked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction.real_masked

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction.real_masked_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction.real_masked_probability

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFutureInputReduction.real_bound
