import BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateSecrecy
import BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources

/-! The selected-coordinate endpoint charges its actual preparation, shared64 draw and every complete source callback at any chain stage. The concrete consumer uses only the original source caller certificate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialSourceInitialSecrecy
open PqxdhInitialSourceInitialResources
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- All source-supported contexts are charged, including completed and rejected preparation branches and every failed or repeated source callback. -/
theorem sampled_uniform
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (prior : ProbComp (Context extra M P I D K X Response A N S B))
    (qPost qCheck qKnown qPre qApplication qSelector qAux : Nat)
    (caps : ∀ input : Input extra M P I D K X Response A N S B, Sum.inr input ∈ support prior →
      PqxdhInitialSourceFirstResources.Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)
    (qPrior : Nat) (priorBound : prior.IsTotalQueryBound qPrior) (stage : Nat) :
    (PqxdhInitialSourceSampled.game source writer sender route decode prior stage).IsTotalQueryBound
      (qPrior + (64 + uniformCap qPost qPre qApplication qSelector qAux)) := by
  unfold PqxdhInitialSourceSampled.game
  rw [← RawCtxSupportedSample.sum_run prior]
  have annotated : (RawCtxSupportedSample.sum prior).IsTotalQueryBound qPrior := by
    apply (isQueryBound_map_iff _ (Sum.map id Subtype.val) _ _ _).mp
    rw [RawCtxSupportedSample.sum_erase]
    exact priorBound
  apply isTotalQueryBound_bind annotated
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
  intro output
  cases context with
  | inl decision => trivial
  | inr input =>
    exact one_uniform source writer sender route decode qPost qCheck qKnown qPre qApplication qSelector qAux
      input.val (caps input.val input.property) _ _ stage

section Actual
open PqxdhAdaptiveTargetPost PqxdhAdaptiveAcceptedResult PqxdhPhase2GeneratedDriver
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
variable {Choice KemSK : Type} {baseSpec : OracleSpec ι} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAdaptiveTargetPost.Post Choice program.Selection baseSpec S (B + 1))
    (targets : Choice → Target S (B + 1)) [DecidableEq Choice]
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (mapPost post Prod.snd))

/-- The actual selected-coordinate source endpoint pays preparation, one shared64 response, all private full76 requests and every original external source callback. The final choice itself is query free. -/
theorem target_uniform (selected : Choice) :
    let projected := certificate env baseImpl kem program post c (choose selected)
    let qPrior := PqxdhAuthenticatedEvolvingResources.priorBudget env baseImpl kem program (mapPost post (choose selected)) projected
    let qPost := PqxdhInitialPreparedSourceCaps.postCap env baseImpl kem program (mapPost post (choose selected)) projected
    let qCallback := PqxdhInitialPreparedSourceCaps.callbackCap env baseImpl kem program (mapPost post (choose selected)) projected
    let qSelector := PqxdhInitialPreparedSourceCaps.selectorCap env baseImpl kem program (mapPost post (choose selected)) projected
    (PqxdhAdaptiveCoordinateSecrecy.targetIdeal env baseImpl kem attachedVerify primitives program post targets selected).IsTotalQueryBound
      (qPrior + (64 + uniformCap qPost qCallback qCallback qSelector projected.qAux)) := by
  exact sampled_uniform env.source env.recordWriter env.senderId env.route env.decode
    (PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program (mapPost post (choose selected))
      (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed)
    _ ((targets selected).number.val - 1 + 1) _ _ _ _ _
    (PqxdhAuthenticatedEvolvingResources.first_caps env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) (certificate env baseImpl kem program post c (choose selected))
      (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed)
    _ (PqxdhInitialPreparedSourceCaps.prior_uniform env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) (certificate env baseImpl kem program post c (choose selected))
      (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed) _

end Actual

end BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources.sampled_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources.sampled_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources.target_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveCoordinateResources.target_uniform
