-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectView
/-! The actual first record and response publication share one free restricted client with internal signing receipts and persistent public platform state. This is the supplied-material component; the selected branch is obtained from the separately checked material44/private-seed split. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {E Platform A ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

abbrev WorkSpec := (Unit →ₒ RustM RegistrationServerRecordExecutor.Result) +
  (registration.ServerResponseHash →ₒ RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
abbrev PublicState (Platform : Type) := RegistrationNativePlatformSigningCompiler.State Platform
abbrev State (n : Nat) (Platform : Type) := PublicState Platform × PqxdhRecordLiftWorld.State n

def program : OracleComp WorkSpec (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) := do
  let completed ← WorkSpec.query (.inl ())
  RegistrationNativePlatformServerPublication.continueResult completed
    (fun response => WorkSpec.query (.inr response))

def liftPlatform (work : StateT Platform (OracleComp (Spec n)) A) :
    StateT (PublicState Platform) (OracleComp (Spec n)) A := fun previous =>
  (fun result => (result.1, (previous.1, result.2))) <$> work.run previous.2

noncomputable def target (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    QueryImpl WorkSpec (StateT (PublicState Platform) (OracleComp (Spec n)))
  | .inl _ => liftPlatform (RegistrationNativePlatformRecordCompiler.record source view failure allocation erased helper initial output)
  | .inr response => simulateQ (RegistrationNativePlatformPublicationCompiler.target source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program response)

noncomputable def actual (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    QueryImpl WorkSpec (StateT (Local n) (StateT Platform ProbComp))
  | .inl _ => RegistrationNativePlatformBoundPublication.record
      (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper) initial output
  | .inr response => RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) response

def strip (state : Local n × Platform) : State n Platform :=
  ((state.1.world.2, state.2), RegistrationNativeWorldView.project state.1.world.1)

noncomputable def closed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    QueryImpl WorkSpec (StateT (State n Platform) ProbComp) :=
  (RegistrationNativePlatformWorldEffectView.implementation.mapStateTBase
    (target source view failure allocation erased helper sign writer initial output)).flattenStateT

omit primitive in
private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem closed_run {Q S T V : Type} {spec : OracleSpec Q}
    (outer : QueryImpl (Spec n) (StateT T ProbComp))
    (inner : QueryImpl spec (StateT S (OracleComp (Spec n))))
    (work : OracleComp spec V) (state : S × T) :
    (simulateQ (outer.mapStateTBase inner).flattenStateT work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ outer ((simulateQ inner work).run state.1)).run state.2 := by
  rw [OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run, bind_pure_comp]

private theorem record_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT (.inl ())).run state =
      (closed setup.source view failure allocation erased helper sign writer initial output (.inl ())).run (strip state) := by
  have native := congrArg (fun action => action.run state.2)
    (RegistrationNativePlatformSourceRecordLower.bound RegistrationNativePlatformMldsaProgram.coins setup codec
      view failure allocation erased helper initial output state.1)
  rw [← RegistrationNativePlatformRecordCompiler.interpret setup view failure allocation erased helper initial output,
    RegistrationNativePlatformWorldEffectClosure.local_world] at native
  have mapped := congrArg (fun action => (fun result => (result.1.1,
    ((result.1.2.world.2, result.2), RegistrationNativeWorldView.project result.1.2.world.1))) <$> action) native
  have projected := RegistrationNativePlatformWorldEffectView.source
    (RegistrationNativePlatformRecordCompiler.record (n := n) setup.source view failure allocation erased helper initial output)
    (RegistrationNativeWorldView.project state.1.world.1) state.2
  rw [RegistrationNativeWorldView.project_idempotent] at projected
  have viewed := congrArg (fun action => (fun result => (result.1.1,
    ((state.1.world.2, result.2), result.1.2))) <$> action) projected
  simp only [StateT.run_map, Functor.map_map, Prod.map, id_eq,
    RegistrationNativePlatformWorldEffectClosure.attach, RegistrationServerRecordWorldSource.project,
    RegistrationNativeWorldView.project_idempotent] at mapped
  simp only [Functor.map_map] at viewed
  have combined := mapped.trans viewed
  convert combined using 1 <;>
    simp only [WorkSpec, actual, closed, target, strip, liftPlatform, QueryImpl.flattenStateT,
      QueryImpl.mapStateTBase, StateT.run, StateT.mk, simulateQ_map, map_apply, Functor.map_map, Prod.map, id_eq,
      RegistrationNativePlatformWorldEffectView.close] <;> rfl


private theorem publication_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (response : registration.ServerResponseHash) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT (.inr response)).run state =
      (closed setup.source view failure allocation erased helper sign writer initial output (.inr response)).run (strip state) := by
  have native := RegistrationNativePlatformPublicationCompiler.source setup.source (fun _ => none) sign writer state.1 response state.2
  have mapped := congrArg (fun action => Prod.map id strip <$> action) native
  unfold RegistrationNativePlatformPublicationCompiler.closed at mapped
  rw [closed_run] at mapped
  have projected := RegistrationNativePlatformWorldEffectView.program
    ((simulateQ (RegistrationNativePlatformPublicationCompiler.target setup.source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program response)).run (state.1.world.2, state.2)) state.1.world.1
  have viewed := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) projected
  simp only [Functor.map_map, Prod.map, id_eq, strip, RegistrationNativePlatformPublicationCompiler.view,
    RegistrationNativePlatformSigningCompiler.restored, RegistrationServerRecordWorldSource.project,
    RegistrationNativeWorldView.project_idempotent] at mapped
  simp only [Functor.map_map, Prod.map, id_eq] at viewed
  have combined := mapped.trans viewed
  convert combined using 1 <;>
    simp only [WorkSpec, actual, closed, target, strip, QueryImpl.flattenStateT,
      QueryImpl.mapStateTBase, StateT.run, StateT.mk, Functor.map_map, Prod.map, id_eq] <;> rfl


private theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (request : WorkSpec.Domain) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT request).run state =
      (closed setup.source view failure allocation erased helper sign writer initial output request).run (strip state) := by
  cases request with
  | inl token => cases token; exact record_query setup codec view failure allocation erased helper sign writer initial output state
  | inr response => exact publication_query setup codec view failure allocation erased helper sign writer initial output response state

/-- The actual first record and its adaptive response publication compile into the same receipt/platform client beside one separate private World. -/
theorem work (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp WorkSpec A) (state : Local n × Platform) :
    Prod.map id strip <$> (simulateQ (actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT work).run state =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer initial output) work).run (strip state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ strip
    (query setup codec view failure allocation erased helper sign writer initial output) work state

private theorem actual_interpret (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ (actual (n := n) setup codec view failure allocation erased helper sign writer initial output) program =
      RegistrationNativePlatformBoundPublication.program
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer) initial output := by
  simp only [program, simulateQ_bind, simulateQ_spec_query, actual,
    RegistrationNativePlatformBoundPublication.program, RegistrationNativePlatformBoundPublication.after]
  apply bind_congr
  intro completed
  cases completed with
  | fail error => rfl
  | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok response => simp only [RegistrationNativePlatformServerPublication.continueResult, simulateQ_spec_query, actual]

noncomputable def compile (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    StateT (PublicState Platform) (OracleComp (Spec n))
      (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :=
  simulateQ (target source view failure allocation erased helper sign writer initial output) program

/-- Literal source first-record/hash/sign/encoding execution has this concrete restricted free client, including every failed allocation, primitive and writer continuation. The private World and true native uniform/cache state remain separate from its receipt/platform state. -/
theorem source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformBoundPublication.program
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer) initial output).run before).run previous =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        ((RegistrationNativePlatformWorldEffectView.close
          (compile setup.source view failure allocation erased helper sign writer initial output)).run
            (RegistrationNativeWorldView.project before.world.1)).run (before.world.2, previous) := by
  have same := work setup codec view failure allocation erased helper sign writer initial output program (before, previous)
  rw [OracleComp.simulateQ_flattenStateT_run, actual_interpret, bind_pure_comp] at same
  unfold closed at same
  rw [closed_run] at same
  simpa only [compile, RegistrationNativePlatformWorldEffectView.close, StateT.run,
    Functor.map_map, Prod.map, id_eq, strip] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler.work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler.work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler.source
