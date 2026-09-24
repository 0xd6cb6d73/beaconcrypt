import BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeySource

/-! The selected-key primitive reduction receives one explicitly billed source preparation. The target32-byte key is absent from that preparation and is supplied by its ordinary challenger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeyResources
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

local notation "qPrior" => PqxdhAuthenticatedEvolvingResources.priorBudget env baseImpl kem program (mapPost post (choose selected)) projected
local notation "qCallback" => PqxdhInitialPreparedSourceCaps.callbackCap env baseImpl kem program (mapPost post (choose selected)) projected
local notation "qSelector" => PqxdhInitialPreparedSourceCaps.selectorCap env baseImpl kem program (mapPost post (choose selected)) projected
local notation "qKnown" => PqxdhInitialPreparedSourceCaps.knownCap env baseImpl kem program (mapPost post (choose selected)) projected (Target.disclosed (targets selected))
local notation "qSample" => qPrior + (64 + PqxdhInitialSourcePreparedSecrecy.sampleBudget qPost qCallback qCallback qSelector c.qAux)

/-- First-record key-free preparation pays actual authenticated preparation plus shared64, nonce12 and nextchain32; the external selected key is charged separately to its primitive challenger. -/
theorem first_prepare :
    (PqxdhAdaptiveMessageKeySource.firstPrepare env baseImpl kem attachedVerify primitives program post targets selected).IsTotalQueryBound
      (qPrior + (64 + (12 + 32))) := by
  unfold PqxdhAdaptiveMessageKeySource.firstPrepare
  apply isTotalQueryBound_bind (PqxdhInitialPreparedSourceCaps.prior_uniform env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) projected (targets selected).owner (targets selected).number
    (targets selected).ancestors (targets selected).disclosed)
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
  intro initial
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12)
  intro nonce
  exact isTotalQueryBound_bind (n₂ := 0) (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun _ => by trivial)

/-- Later-record preparation additionally pays the actual stopped-source prefix and its complete76-byte parent draw, followed by nonce12 and nextchain32. No opaque ambient work is assigned zero cost. -/
theorem later_prepare (depth : Nat) :
    (PqxdhAdaptiveMessageKeySource.laterPrepare env baseImpl kem attachedVerify primitives program post targets selected depth).IsTotalQueryBound
      (qSample + (76 + (12 + 32))) := by
  have sampled := PqxdhInitialSampledResources.sample_uniform env.source env.recordWriter env.senderId env.route env.decode depth
    qPost qCallback qCallback qSelector c.qAux qKnown sourcePrior
    (PqxdhInitialPreparedSourceCaps.supported_caps env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) projected (targets selected).owner (targets selected).number
      (targets selected).ancestors (targets selected).disclosed)
    qPrior (PqxdhInitialPreparedSourceCaps.prior_uniform env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) projected (targets selected).owner (targets selected).number
      (targets selected).ancestors (targets selected).disclosed)
  unfold PqxdhAdaptiveMessageKeySource.laterPrepare RawCtxSelectedParentCandidates.sample
  simp only [bind_assoc, pure_bind]
  apply isTotalQueryBound_bind sampled
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
  intro parent
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12)
  intro nonce
  exact isTotalQueryBound_bind (n₂ := 0) (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun _ => by trivial)

end BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeyResources

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeyResources.first_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeyResources.first_prepare

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeyResources.later_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveMessageKeyResources.later_prepare
