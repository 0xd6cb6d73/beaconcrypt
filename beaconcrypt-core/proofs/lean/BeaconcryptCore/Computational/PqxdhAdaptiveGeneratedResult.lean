import BeaconcryptCore.Computational.PqxdhAdaptiveCommonResult
import BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult

/-!
One actual source execution retains the final target choice across generation, verification, every common candidate and the accepted registration path. Target projection is proved against the existing authenticated evolving-chain experiment. No honest-target selection or per-target simulation equality is assumed.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveGeneratedResult
open PqxdhAdaptiveTargetPost PqxdhAdaptiveAcceptedResult PqxdhAdaptiveCommonResult
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

def rejected : Decision Choice := (none, false)

noncomputable def common : PqxdhAdaptiveCommonResult.Continuation setup (driver env.toDriverEnvironment program).State (Decision Choice) where
  completed output _ := match output with
    | none => pure rejected
    | some output => simulateQ PqxdhAuthenticatedRootExperiment.selectorLift (Prod.fst <$>
        (simulateQ (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
          (post output.context.selection.1 (ok none))).run output.context.selection.2)
  accepted output ready := match output with
    | none => pure rejected
    | some output => do
        let result ← PqxdhProtocolRegistration.coins
          ((PqxdhRegistrationProtocolState.build env.source env.recordWriter env.aux env.senderId
            env.index env.metadata ready).run output.context.selection.2)
        simulateQ PqxdhAuthenticatedRootExperiment.selectorLift (Prod.fst <$>
          (simulateQ (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
            (post output.context.selection.1 result.1)).run result.2)

/-- Target filtering leaves every common/ineligible candidate on its complete original source path, including the same final post decision. -/
theorem common_map [DecidableEq Choice] (selected : Choice) :
    PqxdhAdaptiveCommonResult.project (common env program post) (choose selected) =
      PqxdhAuthenticatedRootExperiment.commonObserver env program (mapPost post (choose selected)) := by
  apply congrArg₂ PqxdhPrivateAcceptedRoot.Continuation.mk
  · funext output execution
    cases output <;> simp only [common,
      mapPost, simulateQ_map, StateT.run_map, Functor.map_map, map_pure]
    rfl
  · funext output ready
    cases output <;> simp only [common,
      mapPost, simulateQ_map, StateT.run_map, Functor.map_map, map_pure, map_bind]
    rfl

end BeaconcryptCore.Computational.PqxdhAdaptiveGeneratedResult

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveGeneratedResult.common_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveGeneratedResult.common_map
