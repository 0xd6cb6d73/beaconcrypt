import BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources
import BeaconcryptCore.Computational.PqxdhInitialSampledSourceLater
import BeaconcryptCore.Computational.PqxdhComposition

/-!
The first initial-half transition and every later parent-child transition are composed in one original sampled protocol experiment. Every stage retains the same preparation, shared64 initializer, complete source schedule, target publication and byte-level freshness event. Finite hybrid arithmetic is applied only to these proved adjacent source simulations. All main/tester reductions and collision/cache charges remain explicit.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhEvolvingChainComposition
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy PqxdhInitialSampledResources
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def statisticalCost (qPost : Nat) : ENNReal :=
  2 * (((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹) +
    ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹

/-- The two parent-collision charges and complete chronological cache-normalization sum are finite for every original source request allowance. -/
theorem statistical_finite (qPost : Nat) : statisticalCost qPost ≠ ⊤ := by
  simp only [statisticalCost, ENNReal.add_ne_top, ENNReal.sum_ne_top]
  constructor
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp))
  · intro j present
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by simp)

/-- The first transition's checker allowance follows from the chosen positive record position; every other resource field is the same supported original source contract. -/
theorem first_caps (input : Input extra M P I D K X Response A N S B)
    (qPost qPre qApplication qSelector qAux qKnown n : Nat)
    (caps : Caps input qPost qPre qApplication qSelector qAux qKnown)
    (position : input.number.val = n + 1) :
    PqxdhInitialSourceFirstResources.Caps input qPost (n + 1) qKnown qPre qApplication qSelector qAux := by
  exact ⟨caps.postBound, by omega, caps.knownBound, caps.preBound,
    caps.applicationBound, caps.selectorBound, caps.auxBound⟩

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (prior : ProbComp (Context extra M P I D K X Response A N S B))

/-- Every displayed later primitive loss is nonnegative; no cancellation is used when converting the explicit probability accounting. -/
theorem later_loss_nonnegative (depth remaining qPost qKnown : Nat) (hmac : HmacSha512) :
    0 ≤ PqxdhInitialSampledReduction.loss source writer sender route decode depth remaining prior qPost qKnown hmac := by
  unfold PqxdhInitialSampledReduction.loss RawCtxSelectedParentHop.extractLoss RawCtxSelectedParentHop.hmacLoss ProbComp.boolDistance
  positivity

variable (qPost qPre qApplication qSelector qAux qKnown : Nat)
  (sourceCaps : ∀ input, Sum.inr input ∈ support prior → Caps input qPost qPre qApplication qSelector qAux qKnown)

include sourceCaps in
/-- The proved global later-source transition has its literal real-valued reduction bill and the finite, separately stated collision/cache term. -/
theorem later_bound (depth remaining : Nat) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (position : ∀ input, Sum.inr input ∈ support prior → input.number.val = (depth + 1) + remaining + 1) :
    (PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 1)).boolDistance
      (PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 2)) ≤
      PqxdhInitialSampledReduction.loss source writer sender route decode depth remaining prior qPost qKnown hmac +
        (statisticalCost qPost).toReal := by
  have bound := PqxdhInitialSampledSourceLater.source_bound source writer sender route decode depth remaining prior
    qPost qPre qApplication qSelector qAux qKnown sourceCaps hmac correct position
  rw [add_assoc] at bound
  have finite : ENNReal.ofReal (PqxdhInitialSampledReduction.loss source writer sender route decode depth remaining prior qPost qKnown hmac) +
      statisticalCost qPost ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, statistical_finite qPost⟩
  have realBound := ENNReal.toReal_mono finite bound
  have advantageNonnegative : 0 ≤ (PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 1)).boolDistance
      (PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 2)) := abs_nonneg _
  simpa only [ENNReal.toReal_add ENNReal.ofReal_ne_top (statistical_finite qPost),
    ENNReal.toReal_ofReal (later_loss_nonnegative source writer sender route decode prior depth remaining qPost qKnown hmac),
    ENNReal.toReal_ofReal advantageNonnegative] using realBound

include sourceCaps in
/-- Every selected positive record has one first-half reduction followed by the ordered sum of its actual later-source reductions in the same global experiment. The two collision charges and cache sum are paid once per later hop. -/
theorem ordered_bound (n : Nat) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (position : ∀ input, Sum.inr input ∈ support prior → input.number.val = n + 1) :
    (PqxdhInitialSourceSampled.game source writer sender route decode prior 0).boolDistance
      (PqxdhInitialSourceSampled.game source writer sender route decode prior (n + 1)) ≤
      PqxdhInitialSourceFirstResources.loss source writer sender route decode prior qPost (n + 1) qKnown hmac +
        (∑ depth ∈ Finset.range n, PqxdhInitialSampledReduction.loss source writer sender route decode
          depth (n - 1 - depth) prior qPost qKnown hmac) + n * (statisticalCost qPost).toReal := by
  have first := PqxdhInitialSourceFirstResources.bound source writer sender route decode prior
    qPost (n + 1) qKnown qPre qApplication qSelector qAux
    (fun input supported => first_caps input qPost qPre qApplication qSelector qAux qKnown n
      (sourceCaps input supported) (position input supported)) hmac correct (by
        intro input supported
        rw [position input supported]
        omega)
  have later := PqxdhComposition.finiteHybridBound_of_hop_bounds
    (fun depth => PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 1)) n
    (fun depth => PqxdhInitialSampledReduction.loss source writer sender route decode depth (n - 1 - depth) prior qPost qKnown hmac +
      (statisticalCost qPost).toReal) (by
        intro depth before
        exact later_bound source writer sender route decode prior qPost qPre qApplication qSelector qAux qKnown
          sourceCaps depth (n - 1 - depth) hmac correct (by
            intro input supported
            rw [position input supported]
            omega))
  have triangle := ProbComp.boolDistance_triangle
    (PqxdhInitialSourceSampled.game source writer sender route decode prior 0)
    (PqxdhInitialSourceSampled.game source writer sender route decode prior 1)
    (PqxdhInitialSourceSampled.game source writer sender route decode prior (n + 1))
  have result := triangle.trans (add_le_add first later)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_assoc] using result

noncomputable def initialLoss (hmac : HmacSha512) : ℝ :=
  (extractRealGame hmac (PqxdhInitialSourceInitialSecrecy.sampler prior)
    (fullExtractReduction hmac .ratchet (PqxdhInitialSourceInitialSecrecy.observer source writer sender route decode))).boolDistance
    (extractUniformGame (PqxdhInitialSourceInitialSecrecy.sampler prior)
      (fullExtractReduction hmac .ratchet (PqxdhInitialSourceInitialSecrecy.observer source writer sender route decode))) +
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet (PqxdhInitialSourceInitialSecrecy.sampler prior)
    (PqxdhInitialSourceInitialSecrecy.observer source writer sender route decode))).boolDistance
    (hmacPrfRandomGame (fullExpandReduction .ratchet (PqxdhInitialSourceInitialSecrecy.sampler prior)
      (PqxdhInitialSourceInitialSecrecy.observer source writer sender route decode)))

noncomputable def chainLoss (n : Nat) (hmac : HmacSha512) : ℝ :=
  PqxdhInitialSourceFirstResources.loss source writer sender route decode prior qPost (n + 1) qKnown hmac +
    (∑ depth ∈ Finset.range n, PqxdhInitialSampledReduction.loss source writer sender route decode
      depth (n - 1 - depth) prior qPost qKnown hmac) + n * (statisticalCost qPost).toReal

include sourceCaps in
/-- The exact secret-input initializer reduction precedes the ordered chain reductions in the same source experiment. Both initialized directions, the shared64 prefix, complete76 projections and every repeated evolving derivation retain their actual correlations. -/
theorem initial_evolving_bound (n : Nat) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (position : ∀ input, Sum.inr input ∈ support prior → input.number.val = n + 1) :
    (PqxdhInitialSourceInitialSecrecy.real source writer sender route decode prior).boolDistance
      (PqxdhInitialSourceSampled.game source writer sender route decode prior (n + 1)) ≤
      initialLoss source writer sender route decode prior hmac +
        chainLoss source writer sender route decode prior qPost qKnown n hmac := by
  have initial := PqxdhInitialSourceInitialSecrecy.bound source writer sender route decode prior hmac correct
  rw [← PqxdhInitialSourceSampled.initial source writer sender route decode prior] at initial
  exact (ProbComp.boolDistance_triangle
    (PqxdhInitialSourceInitialSecrecy.real source writer sender route decode prior)
    (PqxdhInitialSourceSampled.game source writer sender route decode prior 0)
    (PqxdhInitialSourceSampled.game source writer sender route decode prior (n + 1))).trans
      (add_le_add initial (ordered_bound source writer sender route decode prior qPost qPre qApplication qSelector qAux qKnown
        sourceCaps n hmac correct position))

end BeaconcryptCore.Computational.PqxdhEvolvingChainComposition

/-- info: 'BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.statistical_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.statistical_finite
/-- info: 'BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.first_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.first_caps
/-- info: 'BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.later_loss_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.later_loss_nonnegative

/-- info: 'BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.later_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.ordered_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.ordered_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.initial_evolving_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhEvolvingChainComposition.initial_evolving_bound
