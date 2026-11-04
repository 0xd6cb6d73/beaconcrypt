-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms
/-! The complete corrected build callback executes the same dynamic source compiler and persistent platform state after symbolic one-use reference evaluation. Only the material address is evaluated; pin/reserve/seal/hash/serialization/install failures remain the literal source tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativePlatformSecretWordOrdinary (State evaluate)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

theorem build (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativePlatformSecretWordFrontend.build setup sign view failure allocation erased helper writer reserve handle application source).run before) := by
  let nativeTree := (simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run (before.1.server.eval candidate))).run (before.1.environment.receipts, before.2)
  let wordTree := ((RegistrationNativePlatformSecretWordBuild.body (n := n) setup.source view failure allocation erased helper sign writer reserve handle application).run before.1.server).run (before.1.environment.receipts, before.2)
  have low := RegistrationNativePlatformSecretWordBuild.checked_source (n := n) setup.source view failure allocation erased helper sign writer reserve
    setup inside candidate seed scalar handle application before.1.server (before.1.environment.receipts, before.2)
  have lifted := congrArg (simulateQ (RegistrationNativeSecretWordCheckedFrontend.localLift false)) low
  simp only [simulateQ_map, QueryImpl.simulateQ_compose] at lifted
  have symbolic := RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program setup.source inside candidate
    (input setup.joint setup.dh seed scalar) false
    (simulateQ (RegistrationNativePlatformSecretWordBuild.wordEmbedding (KemSK := KemSK)) wordTree)
  have physical := RegistrationNativePlatformSecretWordFrontendPrograms.build_program (KemSK := KemSK) setup.source inside candidate
    (input setup.joint setup.dh seed scalar) nativeTree
  simp only [QueryImpl.simulateQ_compose] at physical
  change simulateQ (RegistrationNativeSecretWordCheckedFrontend.localLift false)
    (simulateQ (RegistrationNativeSecretWordChecked.native setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformSecretWordBuild.nativeEmbedding nativeTree)) = _ at lifted
  rw [← symbolic] at lifted
  have compared := physical.trans lifted
  have outer := congrArg (fun action => (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    (({ server := result.1.2, beacons := before.1.beacons,
        environment := { before.1.environment with receipts := result.2.1, recordRequests := [] },
        parsedAccepts := before.1.parsedAccepts } : RegistrationNativePublicFrontend.State source), result.2.2))) <$> action) compared
  simpa only [RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.build,
    RegistrationNativePlatformSecretWordFrontend.build, evaluate, RegistrationNativeSecretWordMessage.State.eval,
    StateT.run, simulateQ_map, QueryImpl.simulateQ_compose, Functor.map_map, Prod.map_def, id_eq,
    nativeTree, wordTree] using outer

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildSource.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBuildSource.build
