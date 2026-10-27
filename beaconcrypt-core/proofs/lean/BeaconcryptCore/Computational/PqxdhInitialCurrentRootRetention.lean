import BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets
import BeaconcryptCore.Computational.RawCtxInitialSentinelSampler

/-!
The checked current initializer comparison samples its preparation and root before an independent64-byte response. This endpoint may privately retain that already sampled root for later chain-cut auditing. Erasure is the identical current random64 game, not a new secrecy assumption. The complete continuation may retain the earlier root and both role states when splitting either directional half; the selected half is still drawn after that context. No such retained-root observer is substituted into the earlier initial64 Extract game.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhInitialLegalObserver
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot
variable {ι M P I K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

noncomputable def retained : ProbComp (RootOutput × Bool) := do
  let (context, previousRoot) ← sample env baseImpl kem attachedVerify primitives program post
  let output ← $ᵗ HmacBlock
  let decision ← observe env baseImpl kem attachedVerify primitives program post context
    (RawCtxSelectedInitialConstructor.response64 output)
  pure (previousRoot, decision)

/-- Removing the private retained root gives the identical literal current random64 endpoint, including completed source branches. -/
theorem erased : Prod.snd <$> retained env baseImpl kem attachedVerify primitives program post =
    PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post := by
  simp only [retained, PqxdhInitialCurrentSecrecy.random, map_bind, map_pure, bind_pure]

/-- Either directional half is delayed after the actual preparation, previous root and opposite half, while preserving an arbitrary complete continuation rather than only a marginal key distribution. -/
theorem complete_split
    (second : (Context env kem attachedVerify primitives program post × RootOutput) → Bool)
    (next : Context env kem attachedVerify primitives program post → RootOutput → HmacBlock → ProbComp Result) :
    EvalDistEq
      (do let pair ← sample env baseImpl kem attachedVerify primitives program post
          let output ← $ᵗ HmacBlock
          next pair.1 pair.2 output)
      (do let pair ← sample env baseImpl kem attachedVerify primitives program post
          let other ← $ᵗ RootOutput
          let target ← $ᵗ RootOutput
          next pair.1 pair.2 (RawCtxInitialSentinelSampler.join (second pair) other target)) := by
  refine EvalDistEq.bind_right (sample env baseImpl kem attachedVerify primitives program post) (fun pair => ?_)
  simpa only [RawCtxInitialSentinelSampler.join_parts] using
    RawCtxInitialChildSecrecy.parts_observed (second pair)
      (fun other target => next pair.1 pair.2 (RawCtxInitialSentinelSampler.join (second pair) other target))

/-- The first-child ordinary sampler contains the exact current preparation and its earlier root, plus the opposite half; only the selected half is serialized as the unavailable input. -/
theorem joint_separated
    (second : (Context env kem attachedVerify primitives program post × RootOutput) → Bool) :
    EvalDistEq (RawCtxInitialChildSecrecy.joint
      (sample env baseImpl kem attachedVerify primitives program post) second)
      (RawCtxInitialChildSecrecy.separated
        (sample env baseImpl kem attachedVerify primitives program post)) :=
  RawCtxInitialChildSecrecy.joint_separated _ second

/-- Private root retention adds no query: the exact current source certificate still pays its preparation,64-byte response and complete observer bill. -/
theorem retained_uniform (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post) :
    (retained env baseImpl kem attachedVerify primitives program post).IsTotalQueryBound
      (PqxdhInitialCurrentBudgets.qSample env baseImpl kem program post c +
        (64 + PqxdhInitialCurrentBudgets.qObserver env baseImpl kem program post c)) := by
  have bound := PqxdhInitialCurrentBudgets.random_uniform env baseImpl kem attachedVerify primitives program post c
  rw [← erased env baseImpl kem attachedVerify primitives program post] at bound
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bound

end BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.erased

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.complete_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.complete_split

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.joint_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.joint_separated

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.retained_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentRootRetention.retained_uniform
