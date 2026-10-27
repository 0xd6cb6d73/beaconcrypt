import BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingSecrecy

/-! Each constructed adaptive-target reduction pays the complete HB112 root, initial64 and evolving-chain ledger. Choosing the final target adds no source call, hidden ambient work or uncharged candidate test. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources
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

/-- Every fixed-coordinate primitive reduction, collision tester and final ideal inherits the complete checked ledger from the single original source certificate. Target selection changes no source query. -/
theorem target_ledger (selected : Choice) (hmac : HmacSha512) :
    PqxdhAuthenticatedEvolvingResources.Ledger env baseImpl kem attachedVerify primitives program
      (mapPost post (choose selected)) (certificate env baseImpl kem program post c (choose selected))
      (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed hmac := by
  exact PqxdhAuthenticatedEvolvingResources.complete env baseImpl kem attachedVerify primitives program
    (mapPost post (choose selected)) (certificate env baseImpl kem program post c (choose selected))
    (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed hmac

/-- Logical pre/post source budgets and every primitive callback cap are unchanged by adaptive target filtering. Selection factors multiply advantages, not the queries within a constructed reduction. -/
theorem numeric_caps (selected : Choice) :
    let projected := certificate env baseImpl kem program post c (choose selected)
    projected.preBudget = c.preBudget ∧ projected.postBudget = c.postBudget ∧
    projected.qLocal = c.qLocal ∧ projected.qAux = c.qAux ∧ projected.qWrite = c.qWrite ∧
    projected.prekey = c.prekey ∧ projected.oneTime = c.oneTime ∧ projected.ephemeral = c.ephemeral ∧
    projected.nativeEncapsulation = c.nativeEncapsulation ∧ projected.totalEncapsulation = c.totalEncapsulation ∧
    projected.qKeygen = c.qKeygen ∧ projected.qEncap = c.qEncap ∧ projected.qBase = c.qBase ∧ projected.qDecap = c.qDecap := by
  repeat' constructor

end BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources.target_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources.target_ledger
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources.numeric_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveEvolvingResources.numeric_caps
