import BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints
import BeaconcryptCore.Computational.PqxdhInitialSampledReduction

/-!
One adjacent later-chain transition uses the actual preparation, one shared initial64 response and the same selected publication and full-history freshness event. The exact source endpoint comparisons surround a single pair of constructed global main/tester reductions. All statistical costs remain explicit, with no response-selection loss or average of primitive advantages.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSampledSourceLater
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy PqxdhInitialSampledResources
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth remaining : Nat) (prior : ProbComp (Context extra M P I D K X Response A N S B))
  (qPost qPre qApplication qSelector qAux qKnown : Nat)
  (sourceCaps : ∀ input, Sum.inr input ∈ support prior → Caps input qPost qPre qApplication qSelector qAux qKnown)

local notation "sample" => PqxdhInitialSampledParent.sample source writer sender route decode depth prior
local notation "address" => PqxdhInitialSampledParent.address (prior := prior) source writer sender route decode depth
local notation "actualGame" => PqxdhInitialSampledParentSecrecy.actual source writer sender route decode depth remaining sample address
local notation "randomGame" => PqxdhInitialSampledParentSecrecy.random source writer sender route decode depth remaining sample address
local notation "sourceGame" => PqxdhInitialSourceSampled.game source writer sender route decode prior
local notation "primitiveLoss" => PqxdhInitialSampledReduction.loss source writer sender route decode depth remaining prior qPost qKnown
local notation "collision" => ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹
local notation "cacheSum" => ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹

include sourceCaps in
/-- A later source transition has the stated global Extract/HMAC reductions and explicit two-collision/cache bill. Operational resource premises are required only of actually supported preparation results. -/
theorem source_bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (position : ∀ input, Sum.inr input ∈ support prior → input.number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceGame (depth + 1)).boolDistAdvantage (sourceGame (depth + 2))) ≤
      ENNReal.ofReal (primitiveLoss hmac) + 2 * collision + cacheSum := by
  have realBound := PqxdhInitialSampledSourceEndpoints.real_bound source writer sender route decode depth remaining prior qPost
    (fun input supported => (sourceCaps input supported).postBound) position
  have randomBound := PqxdhInitialSampledSourceEndpoints.random_bound source writer sender route decode depth remaining prior qPost
    (fun input supported => (sourceCaps input supported).postBound) position
  have primitive := PqxdhInitialSampledReduction.bound source writer sender route decode depth remaining prior
    qPost qPre qApplication qSelector qAux qKnown sourceCaps hmac correct
  have triangle : (sourceGame (depth + 1)).boolDistAdvantage (sourceGame (depth + 2)) ≤
      (sourceGame (depth + 1)).boolDistAdvantage actualGame + (actualGame).boolDistAdvantage randomGame +
        (randomGame).boolDistAdvantage (sourceGame (depth + 2)) := by
    exact (ProbComp.boolDistAdvantage_triangle (sourceGame (depth + 1)) actualGame (sourceGame (depth + 2))).trans
      (by have bound := ProbComp.boolDistAdvantage_triangle actualGame randomGame (sourceGame (depth + 2)); linarith)
  have forward := ENNReal.ofReal_le_ofReal triangle
  simp only [ProbComp.boolDistAdvantage] at forward
  rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _),
    ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at forward
  have back : ENNReal.ofReal ((randomGame).boolDistAdvantage (sourceGame (depth + 2))) ≤ collision + cacheSum := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using randomBound
  apply forward.trans
  calc
    _ ≤ (collision + ENNReal.ofReal (primitiveLoss hmac)) + (collision + cacheSum) :=
      add_le_add (add_le_add realBound (ENNReal.ofReal_le_ofReal primitive)) back
    _ = _ := by rw [two_mul]; ac_rfl

end BeaconcryptCore.Computational.PqxdhInitialSampledSourceLater

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceLater.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceLater.source_bound
