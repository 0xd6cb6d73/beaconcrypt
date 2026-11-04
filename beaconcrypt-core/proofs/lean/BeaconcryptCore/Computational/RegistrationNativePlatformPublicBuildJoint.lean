-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildClosure
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceStartup
/-! The actual adaptive public build and the complete source build are marginals of the same earlier-root execution. The security observation applies only the named accounting view; actual source poststates and private local frames remain separate exact marginals. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformServerCompilerJoint (joint clientView)
open RegistrationNativePublicSourceEffects (close)
variable {n : Nat} {E Platform I KemSK Reader Response : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

abbrev Reply := RustM (Option (U64 × Pqxdh.Bytes))
def observe (result : Reply × State n KemSK Platform source) :=
  ((result.1, result.2.1.1.server), ((result.2.1.1.environment.receipts, result.2.1.2),
    RegistrationNativeWorldView.project result.2.2.world))
def jointObserve (result : RegistrationNativePlatformServerCompilerJoint.Outcome n Platform) :=
  ((RegistrationNativePlatformPublicFrontend.responseBytes result.1.1, result.1.2.1),
    RegistrationNativePlatformBoundCompiler.strip (result.1.2.2, result.2))

omit primitive in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before


def buildState (before : State n KemSK Platform source)
    (result : ((RegistrationNativePlatformServerCompilerJoint.Result × RegistrationServerMaterialFrontend.State) ×
      RegistrationNativePlatformBoundCompiler.PublicState Platform) × PqxdhRecordLiftWorld.State n) : Reply × State n KemSK Platform source :=
  (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1.1,
    (({ before.1.1 with server := result.1.1.2, environment := { before.1.1.environment with receipts := result.1.2.1, recordRequests := [] } }, result.1.2.2),
      { before.2 with world := result.2 }))
def stateView (before : State n KemSK Platform source) : State n KemSK Platform source :=
  (before.1, RegistrationNativePlatformPublicBuildClosure.worldView before.2)

/-- The literal adaptive build closes through the actual optional private memo and the same persistent platform state. -/
theorem closed (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK Platform source) :
    observe <$> (execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source))).run before =
    (fun result => ((RegistrationNativePlatformPublicFrontend.responseBytes result.1.1.1, result.1.1.2), (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativePlatformServerMemoCompiler.optional setup.source before.2.roots)
        ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
          ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.1.server)).run
            (before.1.1.environment.receipts, before.1.2))).run (RegistrationNativeWorldView.project before.2.world) := by
  let work := ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.1.server)).run
      (before.1.1.environment.receipts, before.1.2))
  have actual := RegistrationNativePlatformPublicBuildClosure.source_program setup wire route sign seed scalar work before.2
  have reduced := congrArg (Functor.map (fun result =>
    ((RegistrationNativePlatformPublicFrontend.responseBytes result.1.1.1, result.1.1.2), (result.1.2, result.2.world)))) actual
  simpa only [execute, RegistrationNativePlatformPublicFrontend.executeLocal,
    RegistrationNativePlatformPublicFrontend.build, observe, simulateQ_map,
    ← QueryImpl.simulateQ_compose, RegistrationNativePlatformPublicBuildClosure.embedded,
    close, StateT.run, map_apply, Functor.map_map, RegistrationNativePlatformPublicBuildClosure.worldView,
    Prod.map_def, id_eq, work] using reduced

/-- The full adaptive build state retains every private frame coordinate under the named World accounting view. -/
theorem closed_state (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK Platform source) :
    Prod.map id stateView <$> (execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source))).run before =
    buildState before <$>
      (simulateQ (RegistrationNativePlatformServerMemoCompiler.optional setup.source before.2.roots)
        ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
          ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.1.server)).run
            (before.1.1.environment.receipts, before.1.2))).run (RegistrationNativeWorldView.project before.2.world) := by
  let work := ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target (n := n) setup.source view failure allocation erased helper sign writer reserve)
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.1.server)).run
      (before.1.1.environment.receipts, before.1.2))
  have actual := RegistrationNativePlatformPublicBuildClosure.source_program setup wire route sign seed scalar work before.2
  have reduced := congrArg (Functor.map (fun result =>
    (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1.1,
      (({ before.1.1 with server := result.1.1.2, environment := { before.1.1.environment with receipts := result.1.2.1, recordRequests := [] } }, result.1.2.2), result.2)))) actual
  convert reduced using 1 <;> simp only [execute, RegistrationNativePlatformPublicFrontend.executeLocal,
    RegistrationNativePlatformPublicFrontend.build, stateView, simulateQ_map,
    ← QueryImpl.simulateQ_compose, RegistrationNativePlatformPublicBuildClosure.embedded,
    close, StateT.run, map_apply, Functor.map_map, RegistrationNativePlatformPublicBuildClosure.worldView,
    Prod.map_def, id_eq, work]
  rfl

/-- The actual new adaptive build security observation is the marginal of the same complete source execution, with the root of its earlier live Ready token. -/
theorem source_joint (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK Platform source)
    (live : RegistrationNativePublicSourceState.Live before.1.1 before.2)
    (correct : RegistrationNativePublicSourceState.MemoCorrect setup seed scalar before.2.roots) :
    observe <$> (execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source))).run before =
    jointObserve <$> joint setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper sign writer reserve
      (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
      (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 := by
  rw [closed]
  have actual := RegistrationNativePlatformServerMemoCompiler.source_marginal setup (RegistrationNativeWire.ledgerCodec wire)
    view failure allocation erased helper sign writer reserve before.2.roots
    (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
    (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 live
    (fun message root stored => by simp only [RegistrationNativePublicSourceState.roots, correct message root stored, Option.getD_some])
  have mapped := congrArg (Functor.map (fun result =>
    ((RegistrationNativePlatformPublicFrontend.responseBytes result.1.1, result.1.2), result.2))) actual
  convert mapped.symm using 1 <;> simp only [Functor.map_map, clientView, RegistrationNativePlatformBoundCompiler.strip,
    RegistrationWorldAgreementCompiler.join]
  rfl

def jointState (before : State n KemSK Platform source)
    (result : RegistrationNativePlatformServerCompilerJoint.Outcome n Platform) : Reply × State n KemSK Platform source :=
  buildState before (((result.1.1, result.1.2.1), (result.1.2.2.world.2, result.2)),
    RegistrationNativeWorldView.project result.1.2.2.world.1)

/-- The full public and private adaptive build state is a marginal of the same complete source execution, retaining every earlier private memo and pool coordinate. -/
theorem source_state (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK Platform source)
    (live : RegistrationNativePublicSourceState.Live before.1.1 before.2)
    (correct : RegistrationNativePublicSourceState.MemoCorrect setup seed scalar before.2.roots) :
    Prod.map id stateView <$> (execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source))).run before =
    jointState before <$> joint setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper sign writer reserve
      (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
      (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 := by
  rw [closed_state]
  have actual := RegistrationNativePlatformServerMemoCompiler.source_marginal setup (RegistrationNativeWire.ledgerCodec wire)
    view failure allocation erased helper sign writer reserve before.2.roots
    (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
    (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 live
    (fun message root stored => by simp only [RegistrationNativePublicSourceState.roots, correct message root stored, Option.getD_some])
  have mapped := congrArg (Functor.map (fun result => buildState before ((result.1, result.2.1), result.2.2))) actual
  convert mapped.symm using 1 <;> simp only [Functor.map_map, clientView, RegistrationNativePlatformBoundCompiler.strip,
    RegistrationWorldAgreementCompiler.join]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.closed_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.closed_state

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.source_joint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.source_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint.source_state
