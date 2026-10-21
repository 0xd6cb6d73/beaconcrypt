import BeaconcryptCore.Computational.PqxdhFinalMaterialKeySplit

/-! The final selected record has one ordinary uniform message-key draw independent of its complete retained source preparation, nonce and next chain. This is an exact distribution endpoint; the secret-free CTX simulation is a separate consuming compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource
open PqxdhAdaptiveTargetPost PqxdhAdaptiveAcceptedResult PqxdhAdaptiveCommonResult
open PqxdhAdaptiveGeneratedResult PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
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

abbrev LaterContext (depth : Nat) :=
  ((PqxdhInitialSampledParent.Packet env.source env.recordWriter env.senderId env.route env.decode depth sourcePrior ×
    RawCtxSelectedParentEntry.Entry) × RootOutput) × NonceOutput × RootOutput

/-- The complete source prefix and selected input are retained; only nonce and next chain are sampled here. No selected message key is an argument or result. -/
noncomputable def laterPrepare (depth : Nat) : ProbComp (LaterContext env baseImpl kem attachedVerify primitives program post targets selected depth) := do
  let pair ← RawCtxSelectedParentCandidates.sample
    (PqxdhInitialSampledParent.sample env.source env.recordWriter env.senderId env.route env.decode depth sourcePrior)
    (PqxdhInitialSampledParent.address env.source env.recordWriter env.senderId env.route env.decode depth)
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  pure (pair, nonce, chain)

/-- This is the original native source observer with the same single full response reconstructed. It is a mathematical key-taking endpoint, awaiting the key-free CTX interpreter. -/
noncomputable def laterObserve (depth : Nat)
    (context : LaterContext env baseImpl kem attachedVerify primitives program post targets selected depth) (key : RootOutput) : ProbComp Bool :=
  PqxdhInitialSampledParent.native env.source env.recordWriter env.senderId env.route env.decode depth 0 context.1.1 context.1.2
    (materialChainEquiv.symm ((key, context.2.1), context.2.2))

noncomputable def laterIdeal (depth : Nat) : ProbComp Bool := do
  let context ← laterPrepare env baseImpl kem attachedVerify primitives program post targets selected depth
  let key ← $ᵗ RootOutput
  laterObserve env baseImpl kem attachedVerify primitives program post targets selected depth context key

/-- The actual final-material sampler and its complete native source event equal an ordinary uniform selected key sampled after all retained source context, nonce and next-chain data. -/
theorem later_source (depth : Nat) :
    𝒟[PqxdhAdaptiveFinalMaterial.laterIdeal env baseImpl kem attachedVerify primitives program post targets selected depth] =
      𝒟[laterIdeal env baseImpl kem attachedVerify primitives program post targets selected depth] := by
  unfold PqxdhAdaptiveFinalMaterial.laterIdeal PqxdhInitialSampledParentSecrecy.random laterIdeal laterPrepare laterObserve
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro context
  apply evalDist_eq_of_evalSPMF_eq
  exact PqxdhFinalMaterialKeySplit.complete_vcvioLegacy _

abbrev FirstContext :=
  (Bool ⊕ PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)) × HmacBlock × NonceOutput × RootOutput

/-- First-record preparation retains the actual source input and shared64 response, then samples only the selected nonce and next chain. -/
noncomputable def firstPrepare : ProbComp (FirstContext (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)) := do
  let context ← sourcePrior
  let initial ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  pure (context, initial, nonce, chain)

noncomputable def firstObserve
    (context : FirstContext (M := M) (P := P) (I := I) (K := K) (X := X)
      (Response := Response) (A := A) (S := S) (B := B) (setup := setup)) (key : RootOutput) : ProbComp Bool :=
  PqxdhAdaptiveFirstMaterial.observe env context.1 context.2.1 (materialChainEquiv.symm ((key, context.2.2.1), context.2.2.2))

noncomputable def firstIdeal : ProbComp Bool := do
  let context ← firstPrepare env baseImpl kem attachedVerify primitives program post targets selected
  let key ← $ᵗ RootOutput
  firstObserve env context key

/-- The actual first-record full76 source continuation has the same complete distribution with its selected message key sampled last. -/
theorem first_source :
    𝒟[PqxdhAdaptiveFirstMaterial.ideal env baseImpl kem attachedVerify primitives program post targets selected] =
      𝒟[firstIdeal env baseImpl kem attachedVerify primitives program post targets selected] := by
  unfold PqxdhAdaptiveFirstMaterial.ideal firstIdeal firstPrepare firstObserve
  simp only [bind_assoc, pure_bind]
  apply evalDist_bind_congr
  intro context
  apply evalDist_bind_congr
  intro initial
  apply evalDist_eq_of_evalSPMF_eq
  exact PqxdhFinalMaterialKeySplit.complete_vcvioLegacy _

/-- The complete_vcvioLegacy actual source comparison reaches one ordinary uniform selected message key after its original source preparation; every final-material alias charge is explicit. -/
theorem later_bound (depth : Nat) (position : (targets selected).number.val = depth + 2)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (choose selected <$> PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets).boolDistAdvantage
      (laterIdeal env baseImpl kem attachedVerify primitives program post targets selected depth) ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected +
      (PqxdhAdaptiveFinalMaterial.statistical qPost).toReal := by
  have result := PqxdhAdaptiveFinalMaterial.later_bound env baseImpl kem attachedVerify primitives program post targets c selected
    depth position compatible adapter functional hmac correct fallback ordinaryFallback
  simpa only [ProbComp.boolDistAdvantage,
    later_source env baseImpl kem attachedVerify primitives program post targets selected depth] using result

/-- The first-record source comparison reaches the same ordinary selected-key endpoint without a final cached-prefix charge. -/
theorem first_bound (position : (targets selected).number.val = 1)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (choose selected <$> PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets).boolDistAdvantage
      (firstIdeal env baseImpl kem attachedVerify primitives program post targets selected) ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected := by
  have result := PqxdhAdaptiveFirstMaterial.bound env baseImpl kem attachedVerify primitives program post targets c selected
    position compatible adapter functional hmac correct fallback ordinaryFallback
  simpa only [ProbComp.boolDistAdvantage,
    first_source env baseImpl kem attachedVerify primitives program post targets selected] using result

end BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.later_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.later_source

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.first_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.first_source

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.later_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.later_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.first_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource.first_bound
