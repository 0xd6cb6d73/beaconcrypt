-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler
/-! The literal source response-publication controller composes actual signing with its stateful source encoder. Internal receipts and common platform state remain outside the separate private World; serializers are trusted local work, never external packet requests. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {E Platform A : Type}

abbrev WorkSpec := RegistrationSigningShared.Spec +
  (registration.SignedResponseView →ₒ RustM (core.option.Option (alloc.vec.Vec U8)))
abbrev PublicState (Platform : Type) := RegistrationNativePlatformSigningCompiler.State Platform
abbrev State (n : Nat) (Platform : Type) := PublicState Platform × PqxdhRecordLiftWorld.State n

def signLift : QueryImpl RegistrationSigningShared.Spec (OracleComp WorkSpec) :=
  fun query => WorkSpec.query (.inl query)
def encodeLift (view : registration.SignedResponseView) : OracleComp WorkSpec (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  WorkSpec.query (.inr view)

def program (response : registration.ServerResponseHash) :
    OracleComp WorkSpec (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformServerPublication.program signLift encodeLift response

def encoding (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) : StateT (PublicState Platform) (OracleComp (Spec n)) (RustM (core.option.Option (alloc.vec.Vec U8))) := fun previous =>
  (fun result => (result.1, (previous.1, result.2))) <$>
    simulateQ RegistrationNativePlatformEffectCompiler.publicCoin
      ((RegistrationNativePlatformSourceCompletion.encodeWith writer view).run previous.2)

def target (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl WorkSpec (StateT (PublicState Platform) (OracleComp (Spec n)))
  | .inl query => RegistrationNativePlatformSigningCompiler.signing hkdf frame sign query
  | .inr view => encoding writer view

noncomputable def actual
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl WorkSpec (StateT (Local n) (StateT Platform ProbComp))
  | .inl query => RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign query
  | .inr view => RegistrationNativePlatformSourceBuild.encode writer view

noncomputable def closed (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl WorkSpec (StateT (State n Platform) ProbComp) :=
  (RegistrationNativePlatformWorldEffectClosure.implementation.mapStateTBase (target hkdf frame sign writer)).flattenStateT

def view (before : Local n) (state : State n Platform) : Local n × Platform :=
  (RegistrationNativePlatformSigningCompiler.restored before state.2 state.1.1, state.1.2)

def metadata (before : Local n) (state : State n Platform) : Local n :=
  { before with world := (state.2, state.1.1) }

private theorem signing_query (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (query : RegistrationSigningShared.Spec.Domain) (state : State n Platform) :
    Prod.map id (view before) <$> (closed hkdf frame sign writer (.inl query)).run state =
      ((actual sign writer).flattenStateT (.inl query)).run (view before state) := by
  have source := RegistrationNativePlatformSigningCompiler.at_view hkdf frame sign query (metadata before state) state.1.2
  have mapped := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) source.symm
  convert mapped using 1 <;>
    simp only [WorkSpec, RegistrationServerRootCompiler.Local, PublicState, RegistrationNativePlatformSigningCompiler.State,
    closed, target, actual, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    RegistrationNativePlatformWorldEffectClosure.close, StateT.run, StateT.mk, Functor.map_map, Prod.map, id_eq,
    view, metadata, RegistrationNativePlatformSigningCompiler.restored, RegistrationServerRecordWorldSource.project] <;> rfl

private theorem external_program (work : ProbComp A) :
    simulateQ (RegistrationNativePlatformWorldEffectClosure.implementation (n := n))
      (simulateQ RegistrationNativePlatformEffectCompiler.publicCoin work) =
      (StateT.lift work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A) := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : RegistrationNativePlatformWorldEffectClosure.implementation (n := n) ∘ₛ
      RegistrationNativePlatformEffectCompiler.publicCoin =
        (fun coin => StateT.lift (unifSpec.query coin : ProbComp _)) := by
    funext coin
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformEffectCompiler.publicCoin,
      simulateQ_spec_query, RegistrationNativePlatformWorldEffectClosure.implementation]
  rw [leaves]
  exact simulateQ_liftTarget (QueryImpl.ofLift unifSpec ProbComp) work |>.trans
    (congrArg (fun action => (StateT.lift action : StateT (PqxdhRecordLiftWorld.State n) ProbComp A))
      (simulateQ_ofLift_eq_self work))

private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem encoding_query (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (response : registration.SignedResponseView) (state : State n Platform) :
    Prod.map id (view before) <$> (closed hkdf frame sign writer (.inr response)).run state =
      ((actual sign writer).flattenStateT (.inr response)).run (view before state) := by
  simp only [closed, target, actual, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    encoding, simulateQ_map, external_program, RegistrationNativePlatformSourceBuild.encode,
    StateT.run, StateT.mk, lift_apply, map_apply, Functor.map_map, Prod.map, id_eq, view]

private theorem query (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (request : WorkSpec.Domain) (state : State n Platform) :
    Prod.map id (view before) <$> (closed hkdf frame sign writer request).run state =
      ((actual sign writer).flattenStateT request).run (view before state) := by
  cases request with
  | inl request => exact signing_query hkdf frame sign writer before request state
  | inr response => exact encoding_query hkdf frame sign writer before response state

/-- Every actual signing/encoding source continuation has the same replies, receipt prefix and persistent platform poststate beside the single private World. -/
theorem work (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (work : OracleComp WorkSpec A) (state : State n Platform) :
    Prod.map id (view before) <$> (simulateQ (closed hkdf frame sign writer) work).run state =
      (simulateQ (actual sign writer).flattenStateT work).run (view before state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (view before) (query hkdf frame sign writer before) work state

private theorem actual_interpret
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (response : registration.ServerResponseHash) :
    simulateQ (actual (n := n) sign writer) (program response) =
      RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer) response := by
  unfold program
  rw [RegistrationNativePlatformServerPublication.program_interpret]
  simp only [signLift, encodeLift, simulateQ_spec_query, actual]

/-- The literal complete source response publication, including late stateful writer failures, is the interpreted free receipt/platform client on the derived source view. -/
theorem source_at_view (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (response : registration.ServerResponseHash) (state : State n Platform) :
    Prod.map id (view before) <$> (simulateQ (closed hkdf frame sign writer) (program response)).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformServerPublication.program
          (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
          (RegistrationNativePlatformSourceBuild.encode writer) response).run (view before state).1).run (view before state).2 := by
  rw [work hkdf frame sign writer before (program response) state,
    OracleComp.simulateQ_flattenStateT_run, actual_interpret, bind_pure_comp]


private def projected (state : Local n × Platform) : Local n × Platform :=
  (RegistrationServerRecordWorldSource.project state.1, state.2)

private theorem actual_signing_project
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : RegistrationSigningShared.Spec.Domain) (state : Local n × Platform) :
    Prod.map id projected <$> ((actual sign writer).flattenStateT (.inl request)).run state =
      ((actual sign writer).flattenStateT (.inl request)).run (projected state) := by
  have same := (RegistrationNativePlatformSigningCompiler.source hkdf frame sign request state.1 state.2).trans
    (RegistrationNativePlatformSigningCompiler.at_view hkdf frame sign request state.1 state.2).symm
  have mapped := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> action) same
  convert mapped using 1 <;>
    simp only [WorkSpec, RegistrationServerRootCompiler.Local, actual, QueryImpl.flattenStateT,
      StateT.run, StateT.mk, map_apply, Functor.map_map, Prod.map, id_eq, projected] <;> rfl

private theorem actual_encoding_project
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (response : registration.SignedResponseView) (state : Local n × Platform) :
    Prod.map id projected <$> ((actual sign writer).flattenStateT (.inr response)).run state =
      ((actual sign writer).flattenStateT (.inr response)).run (projected state) := by
  simp only [actual, QueryImpl.flattenStateT, RegistrationNativePlatformSourceBuild.encode,
    StateT.run, StateT.mk, lift_apply, map_apply, Functor.map_map, Prod.map, id_eq, projected]

private theorem actual_project
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : WorkSpec.Domain) (state : Local n × Platform) :
    Prod.map id projected <$> ((actual sign writer).flattenStateT request).run state =
      ((actual sign writer).flattenStateT request).run (projected state) := by
  cases request with
  | inl request => exact actual_signing_project hkdf frame sign writer request state
  | inr response => exact actual_encoding_project sign writer response state

/-- The complete literal source publication from the original native state lowers to a free receipt/platform program beside one private World. Only the named instrumentation view is applied; all operational states, true native uniforms, shared hashes and failed source writer effects remain. -/
private theorem program_source (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (response : registration.ServerResponseHash) (previous : Platform) :
    Prod.map id projected <$> ((simulateQ (actual sign writer).flattenStateT (program response)).run (before, previous)) =
      Prod.map id (view before) <$> (simulateQ (closed hkdf frame sign writer) (program response)).run
        ((before.world.2, previous), before.world.1) := by
  rw [OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ projected
    (actual_project hkdf frame sign writer), work]
  rfl


/-- From the original reached native state, literal source publication lowers with its full operational state and true native randomness to this World-free receipt/platform client. Late encoder failures retain the same reached signing prefix. -/
theorem source (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : Local n) (response : registration.ServerResponseHash) (previous : Platform) :
    (fun result => (result.1.1, (RegistrationServerRecordWorldSource.project result.1.2, result.2))) <$>
      ((RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer) response).run before).run previous =
      Prod.map id (view before) <$> (simulateQ (closed hkdf frame sign writer) (program response)).run
        ((before.world.2, previous), before.world.1) := by
  have same := program_source hkdf frame sign writer before response previous
  rw [OracleComp.simulateQ_flattenStateT_run, actual_interpret, bind_pure_comp] at same
  simpa only [Functor.map_map, Prod.map, id_eq, projected] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler.work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler.work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler.source_at_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler.source_at_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler.source
