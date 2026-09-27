import BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources
import BeaconcryptCore.Computational.PqxdhInitialSourceRandom

/-! The first-record source endpoint exposes its exact full76 material draw to a subsequent selected-message-key compiler, preserving the complete source event and both common and accepted preparation outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial
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

local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

noncomputable def observe
    (context : Bool ⊕ PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
      (Response := Response) (A := A) (S := S) (B := B) (setup := setup))
    (initial : HmacBlock) (output : PqxdhFullSecretInputKdf.FullOutput) : ProbComp Bool :=
  match context with
  | .inl decision => pure decision
  | .inr input =>
    let response := RawCtxSelectedInitialConstructor.response64 initial
    PqxdhInitialSourceRandom.decision env.source zeroRoot response input.selected output input.number input.ancestors input.disclosed <$>
      PqxdhInitialSourceRandom.randomRun env.source env.recordWriter input.selectedMessage zeroRoot response input.other
        env.senderId env.route env.decode input.index input.metadata {input.ready with root := zeroRoot} input.post input.before
        input.selected input.shared input.privateState input.cache output

/-- The source first-record material is sampled after the identical authenticated preparation and shared64 response, retaining every completed branch. -/
noncomputable def ideal : ProbComp Bool := do
  let context ← sourcePrior
  let initial ← $ᵗ HmacBlock
  let output ← $ᵗ PqxdhFullSecretInputKdf.FullOutput
  observe env context initial output

/-- For record one, the source private table is actually empty and the exact original source publication/freshness event sees the complete independent full76 draw. No miss or final-event equality premise is supplied. -/
theorem source (position : (targets selected).number.val = 1) :
    𝒟[PqxdhAdaptiveCoordinateSecrecy.targetIdeal env baseImpl kem attachedVerify primitives program post targets selected] =
      𝒟[ideal env baseImpl kem attachedVerify primitives program post targets selected] := by
  unfold PqxdhAdaptiveCoordinateSecrecy.targetIdeal PqxdhInitialSourceSampled.game ideal
  rw [position]
  apply evalDist_bind_congr_of_support
  intro context supported
  apply evalDist_bind_congr ($ᵗ HmacBlock)
  intro initial
  cases context with
  | inl decision =>
    apply evalDist_eq_of_evalSPMF_eq
    exact (OracleComp.ProgramLogic.Relational.evalSPMF_bind_const_of_no_failure
      ($ᵗ PqxdhFullSecretInputKdf.FullOutput) (pure decision)).symm
  | inr input =>
    have positive : 0 < input.number.val := by
      rw [PqxdhAuthenticatedEvolvingSecrecy.prior_position env baseImpl kem attachedVerify primitives program
        (mapPost post (choose selected)) (targets selected).owner (targets selected).number
        (targets selected).ancestors (targets selected).disclosed input supported, position]
      norm_num
    exact PqxdhInitialSourceRandom.game_source env.source env.recordWriter input.selectedMessage zeroRoot
      (RawCtxSelectedInitialConstructor.response64 initial) input.other env.senderId env.route env.decode input.index input.metadata
      {input.ready with root := zeroRoot} input.post input.before input.selected input.shared input.privateState input.cache
      input.number positive input.ancestors input.disclosed

/-- The original source execution reaches the first record's explicit full76 sampler with the concrete authenticated-root and evolving-chain losses, preserving common decisions exactly. -/
theorem bound (position : (targets selected).number.val = 1)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (choose selected <$> PqxdhAdaptiveNativeResult.actual env baseImpl kem attachedVerify primitives program post targets).boolDistAdvantage
      (ideal env baseImpl kem attachedVerify primitives program post targets selected) ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env baseImpl kem attachedVerify primitives program post targets c hmac fallback ordinaryFallback selected := by
  have result := PqxdhAdaptiveCoordinateSecrecy.target_bound env baseImpl kem attachedVerify primitives program post targets c
    selected (by omega) compatible adapter functional hmac correct fallback ordinaryFallback
  simpa only [ProbComp.boolDistAdvantage,
    source env baseImpl kem attachedVerify primitives program post targets selected position] using result

end BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial.source

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveFirstMaterial.bound
