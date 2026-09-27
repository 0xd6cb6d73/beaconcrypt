import BeaconcryptCore.Computational.PqxdhAdaptiveNativeResult
import BeaconcryptCore.Computational.PqxdhAdaptiveTargetPartition

/-! Adaptive final-target source events consume the authenticated root and evolving-chain reductions with the original source schedules and query certificate. The summed endpoint below is an explicit sum of coordinate ideals; it is not asserted to be one all-coordinate randomization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy
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

/-- The concrete maintained ideal for exactly the adversary's final-choice event at this coordinate. Different coordinates remain different experiments. -/
noncomputable def targetIdeal (selected : Choice) : ProbComp Bool :=
  PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) (targets selected).owner (targets selected).number
    (targets selected).ancestors (targets selected).disclosed

/-- Every advantage in this loss has the actual final-choice-filtered source callback and its unchanged source certificate. -/
noncomputable def targetLoss (hmac : HmacSha512) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (selected : Choice) : ℝ :=
  PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) (targets selected).owner (targets selected).number
    (targets selected).ancestors (targets selected).disclosed
    (certificate env baseImpl kem program post c (choose selected)) hmac fallback ordinaryFallback

/-- The fixed-target HB112 theorem is consumed by one actual adaptive-choice source execution, with no per-target simulation premise. -/
theorem target_bound (selected : Choice) (positive : 0 < (targets selected).number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (choose selected <$> PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets).boolDistAdvantage
      (targetIdeal env baseImpl kem attachedVerify primitives program post targets selected) ≤
    targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected := by
  rw [← PqxdhAdaptiveNativeResult.actual_map]
  exact PqxdhAuthenticatedEvolvingSecrecy.bound env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) (targets selected).owner (targets selected).number
    (targets selected).ancestors (targets selected).disclosed
    (certificate env baseImpl kem program post c (choose selected)) positive compatible adapter functional hmac correct fallback ordinaryFallback

/-- Exact adaptive target selection pays the sum of the constructed coordinate reductions. This is a bound against an explicit sum of selected-coordinate ideal probabilities, not a claim that those ideals are one all-session ideal. -/
theorem selection_bound [Fintype Choice] (positive : ∀ selected, 0 < (targets selected).number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    |Pr[= true | PqxdhAdaptiveTargetPartition.wins <$>
        PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets].toReal -
      ∑ selected, Pr[= true | targetIdeal env baseImpl kem attachedVerify primitives program post targets selected].toReal| ≤
    ∑ selected, targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected := by
  rw [PqxdhAdaptiveTargetPartition.partition_real, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
  apply Finset.sum_le_sum
  intro selected _
  simpa only [ProbComp.boolDistAdvantage, evalDist_apply_singleton] using
    target_bound env baseImpl kem attachedVerify primitives program post targets c selected (positive selected)
      compatible adapter functional hmac correct fallback ordinaryFallback

end BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy.target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy.target_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy.selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy.selection_bound
