import BeaconcryptCore.Computational.PqxdhAdaptiveSourceResult

/-!
One complete accepted source run retains the final adaptive target alongside the adversary's decision. The original first Server response and full source schedule execute before the target is inspected. Each fixed-target observer used by the existing authenticated evolving-chain proof is obtained by mapping that same run, including its original publication and full-history freshness event.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhAdaptiveTargetPost
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhPrivateAcceptedRoot
variable {ι Choice M P I K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAdaptiveTargetPost.Post Choice program.Selection baseSpec S (B + 1))
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) (ready : Ready)

structure Target (S B : Nat) where
  owner : RawCtxProtocolReveals.Owner S B
  number : Std.U64
  ancestors : List RatchetChain
  disclosed : List RatchetChain

noncomputable def client :=
  (PqxdhInitialOriginPost.sequence (X := X ⊕ PqxdhPhase2JointIdentity.Converted) (Response := Response)
    env.source (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false
      (PqxdhInitialRootLabelService.realInitial env.source ready.root))
    (PqxdhInitialSelectedOrigin.mark env.source (PqxdhInitialRootEventAccepted.selectedMessage env program prepared ready)) true
    env.senderId env.route env.decode env.index env.metadata ready (post prepared.1.context.selection.1)).run
    (PqxdhInitialRootEventAccepted.front env program prepared, PqxdhInitialSourcePublication.empty)

/-- The fixed-target post is a literal final-result map of the same original source client and complete source state. -/
theorem client_map (f : Decision Choice → Bool) :
    PqxdhInitialRootEventAccepted.client env program (mapPost post f) prepared ready =
      (fun result => (f result.1, result.2)) <$> client env program post prepared ready := by
  exact PqxdhAdaptiveSourceResult.sequence_map env.source _ _ true env.senderId env.route env.decode
    env.index env.metadata ready (post prepared.1.context.selection.1) f _

noncomputable def decision (targets : Choice → Target S (B + 1))
    (result : Decision Choice × PqxdhInitialRootEventAccepted.Snapshot (M := M) (P := P) (I := I) (K := K) (S := S) (B := B) (setup := setup)) : Decision Choice :=
  match result.1.1 with
  | none => (none, false)
  | some target => (some target, PqxdhInitialRootEventAccepted.decision env ready (targets target).owner (targets target).number
      (targets target).ancestors (targets target).disclosed (result.1.2, result.2))

/-- The final adaptive choice and freshness observation reproduce the existing fixed-target source event exactly, including unsuccessful and unselected choices. -/
theorem decision_map [DecidableEq Choice] (targets : Choice → Target S (B + 1)) (target : Choice)
    (result : Decision Choice × PqxdhInitialRootEventAccepted.Snapshot (M := M) (P := P) (I := I) (K := K) (S := S) (B := B) (setup := setup)) :
    choose target (decision env ready targets result) =
      PqxdhInitialRootEventAccepted.decision env ready (targets target).owner (targets target).number
        (targets target).ancestors (targets target).disclosed (choose target result.1, result.2) := by
  cases selected : result.1.1 with
  | none => simp [choose, decision, selected, PqxdhInitialRootEventAccepted.decision, PqxdhInitialPublishedEvent.Gate]
  | some chosen =>
    by_cases same : chosen = target
    · subst chosen
      simp [choose, decision, selected]
    · simp [choose, decision, selected, same, PqxdhInitialRootEventAccepted.decision, PqxdhInitialPublishedEvent.Gate]

noncomputable def target (targets : Choice → Target S (B + 1)) :
    OracleComp (PqxdhChallengeSecretRouting.LocalPostSpec baseSpec) (Decision Choice) :=
  (fun result => decision env ready targets result.1) <$>
    (simulateQ (PqxdhInitialRootEventCompiler.target env.source env.recordWriter attachedVerify primitives 1 env.localImpl
      env.aux ready.ciphertext) (client env program post prepared ready)).run
      (prepared.1.context.selection.2.primitive, prepared.2)

/-- The exact executable fixed-target root continuation is obtained from one common adaptive-choice source execution, without exposing its retained private state. -/
theorem target_map [DecidableEq Choice] (targets : Choice → Target S (B + 1)) (selected : Choice) :
    PqxdhInitialRootEventAccepted.target env attachedVerify primitives program (mapPost post (choose selected)) prepared ready
      (targets selected).owner (targets selected).number (targets selected).ancestors (targets selected).disclosed =
      choose selected <$> target env attachedVerify primitives program post prepared ready targets := by
  simp only [PqxdhInitialRootEventAccepted.target, client_map, target, simulateQ_map, StateT.run_map, Functor.map_map]
  congr 1
  funext result
  exact (decision_map env ready targets selected result.1).symm

end BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult.client_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult.client_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult.decision_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult.decision_map
/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult.target_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveAcceptedResult.target_map
