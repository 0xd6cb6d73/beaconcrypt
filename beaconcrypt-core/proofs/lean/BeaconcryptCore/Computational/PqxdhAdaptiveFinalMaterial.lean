import BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources
import BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints

/-! The concrete final selected-record source endpoint is connected to the actual source-supported full76 sampler. This exposes the existing private continuation for a one-key CTX consumer while retaining every common outcome and the exact final source publication/freshness decision. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial
open PqxdhAdaptiveTargetPost PqxdhAdaptiveAcceptedResult PqxdhAdaptiveCommonResult
open PqxdhAdaptiveGeneratedResult PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhHiddenRoot PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateRootSource
open PqxdhPrivateAcceptedRoot (Ready ready)
variable {ι Choice M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAdaptiveTargetPost.Post Choice program.Selection baseSpec S (B + 1))
    (targets : Choice → Target S (B + 1))

variable [DecidableEq Choice]
variable (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (mapPost post Prod.snd))

variable (selected : Choice)
local notation "sourcePrior" => PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program
  (mapPost post (choose selected)) (Target.owner (targets selected)) (Target.number (targets selected))
  (Target.ancestors (targets selected)) (Target.disclosed (targets selected))

local notation "projected" => certificate env baseImpl kem program post c (choose selected)
local notation "qPost" => PqxdhInitialPreparedSourceCaps.postCap env baseImpl kem program (mapPost post (choose selected)) projected

/-- The later target record keeps the actual preparation, shared64 draw, source-stopped parent context and independent final full76 material. -/
noncomputable def laterIdeal (depth : Nat) : ProbComp Bool :=
  PqxdhInitialSampledParentSecrecy.random env.source env.recordWriter env.senderId env.route env.decode depth 0
    (PqxdhInitialSampledParent.sample env.source env.recordWriter env.senderId env.route env.decode depth sourcePrior)
    (PqxdhInitialSampledParent.address env.source env.recordWriter env.senderId env.route env.decode depth)

/-- Extraction pays one actual prior-input collision charge and the complete cached-prefix collision sum. -/
noncomputable def statistical (budget : Nat) : ENNReal :=
  ((8 + budget * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ +
    ∑ j ∈ Finset.range (7 + budget * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹

/-- The maintained source endpoint reaches the actual complete final-material sampler with its real cache-hit normalization cost and no guessed initializer or source-event equality premise. -/
theorem later_source (depth : Nat) (position : (targets selected).number.val = depth + 2) :
    (PqxdhAdaptiveCoordinateSecrecy.targetIdeal env baseImpl kem attachedVerify primitives program post targets selected).boolDistAdvantage
      (laterIdeal env baseImpl kem attachedVerify primitives program post targets selected depth) ≤ (statistical qPost).toReal := by
  have compared := PqxdhInitialSampledSourceEndpoints.random_bound env.source env.recordWriter env.senderId env.route env.decode depth 0 sourcePrior qPost
    (fun input supported => (PqxdhInitialPreparedSourceCaps.supported_caps env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) projected (targets selected).owner (targets selected).number
      (targets selected).ancestors (targets selected).disclosed input supported).postBound)
    (by
      intro input supported
      rw [PqxdhAuthenticatedEvolvingSecrecy.prior_position env baseImpl kem attachedVerify primitives program
        (mapPost post (choose selected)) (targets selected).owner (targets selected).number
        (targets selected).ancestors (targets selected).disclosed input supported, position])
  have finite : statistical qPost ≠ ⊤ := by
    have inverse : (2 ^ 256 : ENNReal)⁻¹ ≠ ⊤ := by norm_num
    simp only [statistical, ENNReal.add_ne_top, ENNReal.sum_ne_top]
    exact ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) inverse, fun _ _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) inverse⟩
  have converted := ENNReal.toReal_mono finite compared
  simpa only [PqxdhAdaptiveCoordinateSecrecy.targetIdeal, laterIdeal, position, statistical,
    ProbComp.boolDistAdvantage, ENNReal.toReal_ofReal (abs_nonneg _)] using converted

/-- The original generated adaptive-choice execution reaches the actual final full76 material sampler. All primitive losses are inherited from the concrete source theorem; only the explicit final cache/input collision allowance is added. -/
theorem later_bound (depth : Nat) (position : (targets selected).number.val = depth + 2)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (choose selected <$> PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets).boolDistAdvantage
      (laterIdeal env baseImpl kem attachedVerify primitives program post targets selected depth) ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected +
      (statistical qPost).toReal := by
  exact (ProbComp.boolDistAdvantage_triangle _
    (PqxdhAdaptiveCoordinateSecrecy.targetIdeal env baseImpl kem attachedVerify primitives program post targets selected) _).trans
      (add_le_add (PqxdhAdaptiveCoordinateSecrecy.target_bound env baseImpl kem attachedVerify primitives program post targets c
        selected (by omega) compatible adapter functional hmac correct fallback ordinaryFallback)
        (later_source env baseImpl kem attachedVerify primitives program post targets c selected depth position))

end BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial.later_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial.later_source

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial.later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveFinalMaterial.later_bound
