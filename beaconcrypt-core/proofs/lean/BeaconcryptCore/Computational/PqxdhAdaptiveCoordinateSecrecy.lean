import BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy

/-! The selected-coordinate source endpoint keeps the actual sampled preparation, the shared64 response and ordered private full76 table. It is exposed separately for a raw-record consumer, without claiming that the unavailable message-key projection is already simulated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy
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

noncomputable def targetIdeal (selected : Choice) : ProbComp Bool :=
  PqxdhInitialSourceSampled.game env.source env.recordWriter env.senderId env.route env.decode
    (PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) (targets selected).owner (targets selected).number
      (targets selected).ancestors (targets selected).disclosed) (targets selected).number.val

/-- The same concrete coordinate reductions include all losses except the separate root-initializer alias correction, which this coordinate endpoint does not need. -/
noncomputable def targetLoss (hmac : HmacSha512) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (selected : Choice) : ℝ :=
  let projected := certificate env baseImpl kem program post c (choose selected)
  let prior := PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) (targets selected).owner (targets selected).number
    (targets selected).ancestors (targets selected).disclosed
  let q := PqxdhInitialPreparedSourceCaps.postCap env baseImpl kem program (mapPost post (choose selected)) projected
  let k := PqxdhInitialPreparedSourceCaps.knownCap env baseImpl kem program (mapPost post (choose selected)) projected (targets selected).disclosed
  PqxdhInitialRootEventSecrecy.loss env baseImpl kem attachedVerify primitives program (mapPost post (choose selected))
    (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed q hmac fallback ordinaryFallback +
    PqxdhEvolvingChainComposition.initialLoss env.source env.recordWriter env.senderId env.route env.decode prior hmac +
    PqxdhEvolvingChainComposition.chainLoss env.source env.recordWriter env.senderId env.route env.decode prior q k ((targets selected).number.val - 1) hmac

/-- The original adaptive event reaches the exact sampled source endpoint containing the ordered full76 draws; its retained source continuation is available to a one-key record-security consumer. -/
theorem target_bound (selected : Choice) (positive : 0 < (targets selected).number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (choose selected <$> PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets).boolDistance
      (targetIdeal env baseImpl kem attachedVerify primitives program post targets selected) ≤
    targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected := by
  rw [← PqxdhAdaptiveNativeResult.actual_map]
  exact PqxdhAuthenticatedEvolvingSecrecy.coordinate_bound env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) (targets selected).owner (targets selected).number
    (targets selected).ancestors (targets selected).disclosed
    (certificate env baseImpl kem program post c (choose selected)) positive compatible adapter functional hmac correct fallback ordinaryFallback

/-- Exact adaptive target selection pays the sum of the constructed coordinate reductions. The final coordinate endpoint retains the exact source sampler for a subsequent component-security comparison; common candidate decisions remain present on both sides. -/
theorem selection_bound [Fintype Choice] (positive : ∀ selected, 0 < (targets selected).number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    |Pr{let x ← (PqxdhAdaptiveTargetPartition.wins <$>
        PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets)}[x = true].toReal -
      ∑ selected, Pr{let x ← targetIdeal env baseImpl kem attachedVerify primitives program post targets selected}[x = true].toReal| ≤
    ∑ selected, targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected := by
  rw [PqxdhAdaptiveTargetPartition.partition_real, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
  apply Finset.sum_le_sum
  intro selected _
  rw [prEvent_eq_evalDist_singleton _ true, prEvent_eq_evalDist_singleton _ true]
  exact target_bound env baseImpl kem attachedVerify primitives program post targets c selected (positive selected)
    compatible adapter functional hmac correct fallback ordinaryFallback

end BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy.target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy.target_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy.selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy.selection_bound
