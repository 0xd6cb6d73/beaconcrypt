-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBoundCompiler
/-! The supplied-material source Server stage compiles its full dynamic publication and actual installation effects into a root-free public client. Selected material uses the checked material44/private-seed split. The stated instrumentation projection is an intermediate functional endpoint; exact source bills remain separate reached-execution receipts. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformBoundCompiler (PublicState State strip)
variable {n : Nat} {E Platform A ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

abbrev WorkSpec (n : Nat) := (Unit →ₒ RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) + EnvEffects n

def forward : QueryImpl (EnvEffects n) (OracleComp (WorkSpec n)) := fun query => (WorkSpec n).query (.inr query)

def known (control : pqxdh.ServerState) : OracleComp (WorkSpec n) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) := do
  let published ← (WorkSpec n).query (.inl ())
  simulateQ forward (RegistrationNativePairedServerService.knownAfter control published)

def hidden (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n) :
    OracleComp (WorkSpec n) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) := do
  let published ← (WorkSpec n).query (.inl ())
  simulateQ forward (RegistrationHiddenInstall.after control slot published)

noncomputable def target (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    QueryImpl (WorkSpec n) (StateT (PublicState Platform) (OracleComp (Spec n)))
  | .inl _ => RegistrationNativePlatformBoundCompiler.compile source view failure allocation erased helper sign writer initial output
  | .inr effect => RegistrationNativePlatformEffectCompiler.effect effect

noncomputable def actual (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    QueryImpl (WorkSpec n) (StateT (Local n) (StateT Platform ProbComp))
  | .inl _ => RegistrationNativePlatformBoundPublication.program
      (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
      (RegistrationNativePlatformSourceBuild.write helper)
      (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
      (RegistrationNativePlatformSourceBuild.encode writer) initial output
  | .inr effect => RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins effect

noncomputable def closed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    QueryImpl (WorkSpec n) (StateT (State n Platform) ProbComp) :=
  (RegistrationNativePlatformWorldEffectView.implementation.mapStateTBase
    (target source view failure allocation erased helper sign writer initial output)).flattenStateT

omit primitive in
private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem publication_query (setup : Setup base KemSK) (codec : Codec Reader Response)
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
  have same := RegistrationNativePlatformBoundCompiler.source setup codec view failure allocation erased helper sign writer initial output state.1 state.2
  convert same using 1 <;>
    simp only [WorkSpec, actual, closed, target, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      RegistrationNativePlatformWorldEffectView.close, StateT.run, StateT.mk, Functor.map_map, Prod.map, id_eq, strip] <;> rfl

private theorem effect_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (effect : (EnvEffects n).Domain) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT (.inr effect)).run state =
      (closed setup.source view failure allocation erased helper sign writer initial output (.inr effect)).run (strip state) := by
  have native := congrArg (fun action => (action.run state.1).run state.2)
    (RegistrationNativePlatformEffectCompiler.close_effect
      (Auxiliary := RegistrationServerRoleBackend.State) (Platform := Platform) effect).symm
  rw [RegistrationNativePlatformWorldEffectClosure.local_world] at native
  have mapped := congrArg (fun action => (fun result => (result.1.1, strip (result.1.2, result.2))) <$> action) native
  have projected := RegistrationNativePlatformWorldEffectView.source
    (RegistrationNativePlatformEffectCompiler.effect (Platform := Platform) effect) state.1.world.1 state.2
  have viewed := congrArg (fun action => (fun result => (result.1.1, ((state.1.world.2, result.2), result.1.2))) <$> action) projected
  simp only [Functor.map_map, RegistrationNativePlatformWorldEffectClosure.attach, strip] at mapped
  simp only [Functor.map_map] at viewed
  have combined := mapped.trans viewed
  convert combined using 1 <;>
    simp only [WorkSpec, actual, closed, target, strip, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      RegistrationNativePlatformWorldEffectView.close, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run, StateT.mk, lift_apply, map_apply, simulateQ_map, simulateQ_spec_query,
      Functor.map_map, Prod.map, id_eq]; rfl


private theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (request : (WorkSpec n).Domain) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT request).run state =
      (closed setup.source view failure allocation erased helper sign writer initial output request).run (strip state) := by
  cases request with
  | inl token => cases token; exact publication_query setup codec view failure allocation erased helper sign writer initial output state
  | inr effect => exact effect_query setup codec view failure allocation erased helper sign writer initial output effect state

/-- Every reached publication/install continuation shares the derived source-view World, literal reply, signing receipts and common platform poststate. -/
theorem work (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (WorkSpec n) A) (state : Local n × Platform) :
    Prod.map id strip <$> (simulateQ (actual setup codec view failure allocation erased helper sign writer initial output).flattenStateT work).run state =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer initial output) work).run (strip state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ strip
    (query setup codec view failure allocation erased helper sign writer initial output) work state

private theorem forward_interpret (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (EnvEffects n) A) :
    simulateQ (actual setup codec view failure allocation erased helper sign writer initial output) (simulateQ forward work) =
      simulateQ (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation work)
  funext query
  simp only [QueryImpl.apply_compose, forward, simulateQ_spec_query, actual]

private theorem known_interpret (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (control : pqxdh.ServerState) :
    simulateQ (actual (n := n) setup codec view failure allocation erased helper sign writer initial output) (known control) =
      RegistrationNativePlatformPairedServerService.knownStage
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins)
        control initial output := by
  simp only [known, simulateQ_bind, simulateQ_spec_query, actual,
    RegistrationNativePlatformPairedServerService.knownStage]
  apply bind_congr
  intro published
  exact forward_interpret setup codec view failure allocation erased helper sign writer initial output _

private theorem hidden_interpret (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n) :
    simulateQ (actual setup codec view failure allocation erased helper sign writer initial output) (hidden control slot) =
      RegistrationNativePlatformPairedServerService.hiddenStage
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins)
        control slot initial output := by
  simp only [hidden, simulateQ_bind, simulateQ_spec_query, actual,
    RegistrationNativePlatformPairedServerService.hiddenStage]
  apply bind_congr
  intro published
  exact forward_interpret setup codec view failure allocation erased helper sign writer initial output _

/-- The complete concrete supplied-material source stage, including actual failed peer installation, has this executable restricted interpretation. -/
theorem known_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (control : pqxdh.ServerState) (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformPairedServerService.knownStage
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins)
        control initial output).run before).run previous =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer initial output) (known control)).run
        (strip (before, previous)) := by
  have same := work setup codec view failure allocation erased helper sign writer initial output (known control) (before, previous)
  rw [OracleComp.simulateQ_flattenStateT_run, known_interpret, bind_pure_comp] at same
  simpa only [Functor.map_map, Prod.map, id_eq] using same


/-- The macro interpreter is exactly the concrete restricted program on receipt/platform state beside the private World. -/
theorem interpret (setup : Setup base KemSK)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (WorkSpec n) A) (state : State n Platform) :
    (simulateQ (closed setup.source view failure allocation erased helper sign writer initial output) work).run state =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        ((RegistrationNativePlatformWorldEffectView.close
          (simulateQ (target setup.source view failure allocation erased helper sign writer initial output) work)).run state.2).run state.1 := by
  unfold closed
  rw [OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run, bind_pure_comp]
  simp only [RegistrationNativePlatformWorldEffectView.close, StateT.run, Functor.map_map]

/-- The protected stage receives material44 and a private slot; its executable client contains only the fixed placeholder seed, while the actual hidden installation retains the real private kernel. -/
theorem hidden_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformPairedServerService.hiddenStage
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins)
        control slot initial (PqxdhDeploymentHiddenLayout.joinOutput material seed)).run before).run previous =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer initial
        (PqxdhDeploymentHiddenLayout.joinOutput material RegistrationBoundPublication.fixedSeed)) (hidden control slot)).run
          (strip (before, previous)) := by
  have same := work setup codec view failure allocation erased helper sign writer initial
    (PqxdhDeploymentHiddenLayout.joinOutput material RegistrationBoundPublication.fixedSeed) (hidden control slot) (before, previous)
  rw [OracleComp.simulateQ_flattenStateT_run, hidden_interpret, bind_pure_comp] at same
  have sourceSplit := RegistrationNativePlatformPairedServerService.stage_split
    (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins) control slot initial material seed
  have fixedSplit := RegistrationNativePlatformPairedServerService.stage_split
    (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins) control slot initial material RegistrationBoundPublication.fixedSeed
  have sourceEqual := congrArg (fun action =>
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$> (action.run before).run previous)
    (sourceSplit.trans fixedSplit.symm)
  apply sourceEqual.trans
  simpa only [Functor.map_map, Prod.map, id_eq] using same

/-- Literal source completion runs its exact two-KDF accounting prefix and then the checked known-material restricted stage. This endpoint applies the declared instrumentation view; it does not equate the omitted native KDF bill. -/
theorem finish_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : pending.pending = PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray root))
    (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformSourceBuild.finishSource RegistrationNativePlatformMldsaProgram.coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        sign helper writer control pending).run before).run previous =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer
        (RegistrationBoundKeySchedule.publicInitial pending) (PqxdhServerAuthKeySchedule.fromRoot setup.source root))
        (known control)).run (strip (before, previous)) := by
  have reached := congrArg (fun action => (fun result => (result.1.1, strip (result.1.2, result.2))) <$> action.run previous)
    (RegistrationNativePlatformPairedServerService.finish_source RegistrationNativePlatformMldsaProgram.coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
      sign helper writer control pending root role before)
  have native := known_source setup codec view failure allocation erased helper sign writer
    (RegistrationBoundKeySchedule.publicInitial pending) (PqxdhServerAuthKeySchedule.fromRoot setup.source root) control
    (RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before)) previous
  have prefixView : strip
      (RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before), previous) =
      strip (before, previous) := rfl
  rw [prefixView] at native
  exact reached.trans native

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.hidden_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.hidden_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler.finish_source
