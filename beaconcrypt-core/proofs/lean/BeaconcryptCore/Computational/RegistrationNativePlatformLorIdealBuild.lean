-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! The literal symbolic Server build and complete current public build envelope retain their free material-choice interpretation. Any lawful persistent interpreter may supply hidden, known or failed material replies; only the individual demand/effect dictionary relation is used. Dynamic source pin, reservation, seal, publication, allocation, writer and platform poststates remain in the exact body. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSecretWordOrdinary (State evaluate)
open RegistrationNativePlatformSecretWordBuild (body realize)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def nativeEmbedding : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ
    (RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ RegistrationNativePlatformPublicFrontend.buildEmbedding)

def wordEmbedding : QueryImpl (RegistrationNativePlatformSecretWordBuild.Spec n)
    (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativePlatformSecretWordBuild.wordEmbedding

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) m)
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) m)
    (compatible : (native ∘ₛ nativeEmbedding) ∘ₛ realize candidate = symbolic ∘ₛ wordEmbedding)

include compatible in
/-- The genuine free source-body realization holds under any stateful demand/effect interpretation, without restricting a material reply to known material. -/
theorem body_source (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeSecretWordMessage.ServerState)
    (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    simulateQ native (simulateQ nativeEmbedding
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run (before.eval candidate))).run previous)) =
      Prod.map (Prod.map id (RegistrationNativeSecretWordMessage.ServerState.eval candidate)) id <$>
        simulateQ symbolic (simulateQ wordEmbedding
          (((body setup.source view failure allocation erased helper sign writer reserve handle application).run before).run previous)) := by
  have compared := congrArg (simulateQ (native ∘ₛ nativeEmbedding))
    (RegistrationNativePlatformSecretWordBuild.body_source (n := n) setup.source view failure allocation erased helper sign writer reserve candidate handle application before previous)
  simpa only [simulateQ_map,←QueryImpl.simulateQ_compose,compatible] using compared.symm

include compatible in
/-- The complete literal current build envelope preserves its reply, opaque frontend and shared platform state under the same individual material/effect dictionary relation. -/
theorem build (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    simulateQ native (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ symbolic ((RegistrationNativePlatformSecretWordFrontend.build setup sign view failure allocation erased helper writer reserve handle application source).run before) := by
  let nativeTree := (simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run (before.1.server.eval candidate))).run (before.1.environment.receipts,before.2)
  let wordTree := ((body (n := n) setup.source view failure allocation erased helper sign writer reserve handle application).run before.1.server).run (before.1.environment.receipts,before.2)
  have compared := body_source setup sign view failure allocation erased helper writer reserve candidate native symbolic compatible handle application before.1.server (before.1.environment.receipts,before.2)
  have outer := congrArg (fun action => (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    (({ server := result.1.2, beacons := before.1.beacons,
        environment := { before.1.environment with receipts := result.2.1,recordRequests := [] },
        parsedAccepts := before.1.parsedAccepts } : RegistrationNativePublicFrontend.State source),result.2.2))) <$> action) compared
  simpa only [RegistrationNativePlatformPublicFrontend.executeLocal,RegistrationNativePlatformPublicFrontend.build,
    RegistrationNativePlatformSecretWordFrontend.build,evaluate,RegistrationNativeSecretWordMessage.State.eval,
    StateT.run,simulateQ_map,QueryImpl.simulateQ_compose,Functor.map_map,Prod.map_def,id_eq,
    nativeEmbedding,wordEmbedding,nativeTree,wordTree] using outer

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild.body_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild.build
