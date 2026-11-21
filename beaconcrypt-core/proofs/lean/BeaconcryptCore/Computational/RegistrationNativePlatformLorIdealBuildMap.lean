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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSecretWordOrdinary (State evaluate)
open RegistrationNativePlatformSecretWordBuild (body realize)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable {NativePrivate WordPrivate : Type}
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
    (native : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate)
    (compatible : ∀ query before, Prod.map id frame <$>
      ((symbolic ∘ₛ wordEmbedding) query).run before =
      (((native ∘ₛ nativeEmbedding) ∘ₛ realize candidate) query).run (frame before))

include compatible in
/-- The actual free source body is natural under a projected persistent state relation, including arbitrary material choices. -/
theorem body_source (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativeSecretWordMessage.ServerState)
    (previous : RegistrationNativePlatformBoundCompiler.PublicState Platform) (privateBefore : WordPrivate) :
    (simulateQ native (simulateQ nativeEmbedding
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run (before.eval candidate))).run previous))).run (frame privateBefore) =
      Prod.map (Prod.map (Prod.map id (RegistrationNativeSecretWordMessage.ServerState.eval candidate)) id) frame <$>
        (simulateQ symbolic (simulateQ wordEmbedding
          (((body setup.source view failure allocation erased helper sign writer reserve handle application).run before).run previous))).run privateBefore := by
  let tree := (((body (n := n) setup.source view failure allocation erased helper sign writer reserve handle application).run before).run previous)
  have natural := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (symbolic ∘ₛ wordEmbedding) ((native ∘ₛ nativeEmbedding) ∘ₛ realize candidate) frame compatible tree privateBefore
  have compared := congrArg (fun work => (simulateQ (native ∘ₛ nativeEmbedding) work).run (frame privateBefore))
    (RegistrationNativePlatformSecretWordBuild.body_source (n := n) setup.source view failure allocation erased helper sign writer reserve candidate handle application before previous).symm
  simp only [simulateQ_map,StateT.run_map,←QueryImpl.simulateQ_compose] at compared ⊢
  rw [compared]
  have mapped := congrArg (Functor.map (Prod.map (Prod.map (Prod.map id (RegistrationNativeSecretWordMessage.ServerState.eval candidate)) id) id)) natural.symm
  simpa only [tree,Functor.map_map,Prod.map_def,id_eq] using mapped

omit primitive in
private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

include compatible in
/-- The complete public build envelope carries the same projected private poststate and exact reached P. -/
theorem build (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) (privateBefore : WordPrivate) :
    (simulateQ native (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run (evaluate candidate before)))).run (frame privateBefore) =
      Prod.map (Prod.map id (evaluate candidate)) frame <$>
        (simulateQ symbolic ((RegistrationNativePlatformSecretWordFrontend.build setup sign view failure allocation erased helper writer reserve handle application source).run before)).run privateBefore := by
  have compared := body_source setup sign view failure allocation erased helper writer reserve candidate native symbolic frame compatible
    handle application before.1.server (before.1.environment.receipts,before.2) privateBefore
  have outer := congrArg (Functor.map (Prod.map (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    (({ server := result.1.2, beacons := before.1.beacons,
        environment := { before.1.environment with receipts := result.2.1,recordRequests := [] },
        parsedAccepts := before.1.parsedAccepts } : RegistrationNativePublicFrontend.State source),result.2.2))) id)) compared
  simpa only [RegistrationNativePlatformPublicFrontend.executeLocal,RegistrationNativePlatformPublicFrontend.build,
    RegistrationNativePlatformSecretWordFrontend.build,evaluate,RegistrationNativeSecretWordMessage.State.eval,
    StateT.run,simulateQ_map,map_apply,QueryImpl.simulateQ_compose,Functor.map_map,Prod.map_def,id_eq,
    nativeEmbedding,wordEmbedding] using outer

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap.body_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap.build
