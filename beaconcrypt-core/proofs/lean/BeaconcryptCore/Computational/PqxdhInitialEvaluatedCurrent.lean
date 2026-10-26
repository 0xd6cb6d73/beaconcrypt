import BeaconcryptCore.Computational.PqxdhInitialEvaluatedPost
import BeaconcryptCore.Computational.PqxdhInitialPrivateCurrent
import BeaconcryptCore.Computational.PqxdhInitialSelectedBuilder

/-!
The authenticated-root endpoint's actual accepted source execution is represented before its original Server first send and throughout its complete post continuation. The same private selected-chain interpretation is used for the builder, repeated Beacon initialization and every record. The original root cache and private identity state survive unchanged across the boundary; no arbitrary established-state premise replaces the source prefix.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialEvaluatedCurrent
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhCorrelatedExtractFamily PqxdhInitialRootLabelService PqxdhSecretInputKdf
open PqxdhAuthenticatedRootExperiment PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot PqxdhInitialGenericProtocolBuilder
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

section Current
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (selected : Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (second : Bool) (other target : RootOutput)

noncomputable def accepted : StateT RootOracle.QueryCache ProbComp Bool := fun cache => do
  let result ← (build env.source (RawCtxSelectedParentCalls.labelCalls env.source env.recordWriter prior entry
      (RawCtxSelectedParentCalls.childResponse prior entry target)) env.aux
      (RawCtxInitialSentinelSampler.labelInitial second false other) env.senderId env.index env.metadata
      (PqxdhInitialBuilderCut.eraseRoot ready)).run
        (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel prepared.1.context.selection.2)
  (Prod.fst <$> (simulateQ (PqxdhInitialEvaluatedPost.handler attachedVerify primitives 1 env.source env.localImpl
      env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext prior entry selected second other target)
      (post prepared.1.context.selection.1 result.1)).run (result.2, prepared.2)).run cache

set_option backward.isDefEq.respectTransparency false in
/-- The actual accepted endpoint has this exact source-derived slot execution before its first ciphertext and across every permitted post request, with the whole initializer cache retained. -/
theorem source :
    simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected
      (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
      (PqxdhInitialPrivateCurrent.accepted env (retainedKdf prior entry target) baseImpl kem attachedVerify primitives
        program post secret selected prepared ready) =
      accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready prior entry second other target := by
  funext cache
  change StateT.run (simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected
    (RawCtxSelectedInitialConstructor.response64 (RawCtxInitialSentinelSampler.join second other target)))
      (PqxdhInitialPrivateCurrent.accepted env (retainedKdf prior entry target) baseImpl kem attachedVerify primitives
        program post secret selected prepared ready)) cache = _
  rw [PqxdhInitialPrivateCurrent.accepted_response]
  have built := selected_build env.source env.recordWriter prior entry target env.aux
    (RawCtxInitialSentinelSampler.labelInitial second false other) env.senderId env.index env.metadata
    (PqxdhInitialBuilderCut.eraseRoot ready)
    (PqxdhInitialGenericProtocol.fromNative PqxdhInitialSelectedBuilder.knownKernel prepared.1.context.selection.2)
  simp only [PqxdhInitialSelectedBuilder.known_state] at built
  rw [PqxdhInitialSelectedBuilder.kernel_response, built, bind_map_left]
  unfold accepted
  apply bind_congr
  intro result
  have mapped := PqxdhInitialEvaluatedPost.source attachedVerify primitives 1 env.source env.localImpl
    env.recordWriter env.senderId env.route env.decode baseImpl kem secret ready.ciphertext prior entry selected second other target
    (post prepared.1.context.selection.1 result.1) (result.2, prepared.2)
  have observed := congrArg (fun work => (Prod.fst <$> work).run cache) mapped
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, Prod.map_def, id_eq,
    PqxdhInitialGenericPost.native] using observed

end Current
end BeaconcryptCore.Computational.PqxdhInitialEvaluatedCurrent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialEvaluatedCurrent.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialEvaluatedCurrent.source
