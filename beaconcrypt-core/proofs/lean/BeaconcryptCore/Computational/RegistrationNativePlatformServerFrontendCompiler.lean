-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendProgram
/-! The complete corrected Server reference frontend is executable over a typed material-demand oracle and restricted World effects with external platform coins. Its public code contains no root table or private World lens. The real private interpreter below supplies the root actually retained by earlier preparation; other demand policies are separate hybrid interpretations. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState State strip)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {E Platform A ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

abbrev Spec (n : Nat) := (RegistrationNativeRelatedFamily.Message →ₒ Option (Choice n)) + RegistrationNativePlatformEffectCompiler.Spec n

def embed : QueryImpl (RegistrationNativePlatformEffectCompiler.Spec n) (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inr query)

def liftEffects (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A) :
    StateT (PublicState Platform) (OracleComp (Spec n)) A := fun previous => simulateQ embed (work.run previous)

noncomputable def service (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    StateT (PublicState Platform) (OracleComp (Spec n)) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) := do
  let selected ← StateT.lift ((Spec n).query (.inl message) : OracleComp (Spec n) _)
  match selected with
  | none => pure (.ok (.Err control))
  | some choice => liftEffects (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice)

noncomputable def target (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) :
    QueryImpl RegistrationNativePlatformServerFrontendProgram.Spec (StateT (PublicState Platform) (OracleComp (Spec n)))
  | .pin current => liftEffects (RegistrationNativePlatformServerRestrictedService.pin current)
  | .reserve => liftEffects (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile reserve))
  | .present keyId => liftEffects (RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId)))
  | .service control initial message => service source view failure allocation erased helper sign writer control initial message

noncomputable def implementation (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (roots : RegistrationServerReferenceRestore.Roots) :
    QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp)
  | .inl message => pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source (roots message))))
  | .inr query => RegistrationNativePlatformWorldEffectView.implementation query

omit primitive in
private theorem effects_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (roots : RegistrationServerReferenceRestore.Roots) (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A) :
    simulateQ (implementation source roots) (simulateQ embed work) =
      simulateQ RegistrationNativePlatformWorldEffectView.implementation work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler work)
  funext query
  simp only [QueryImpl.apply_compose, embed, simulateQ_spec_query, implementation]

omit primitive in
private theorem bind_apply {S V W : Type} {q : Type → Type} [Monad q]
    (work : StateT S q V) (next : V → StateT S q W) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

omit primitive in
private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem service_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (roots : RegistrationServerReferenceRestore.Roots) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (message : RegistrationNativeRelatedFamily.Message)
    (previous : PublicState Platform) :
    simulateQ (implementation (n := n) source roots)
      (service source view failure allocation erased helper sign writer control initial message previous) =
      simulateQ RegistrationNativePlatformWorldEffectView.implementation
        ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial
          (.known (PqxdhServerAuthKeySchedule.fromRoot source (roots message)))).run previous) := by
  simp only [service, StateT.run, bind_apply, lift_apply, bind_map_left, simulateQ_bind,
    simulateQ_spec_query, implementation]
  simp only [pure_bind, liftEffects, effects_program]
  rfl


noncomputable def actual (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots) :
    QueryImpl RegistrationNativePlatformServerFrontendProgram.Spec (StateT (Local n) (StateT Platform ProbComp))
  | .pin current => RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins current
  | .reserve => StateT.lift reserve
  | .present keyId => RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins (.peerPresent keyId)
  | .service control initial message => RegistrationNativePlatformServerMaterialState.service RegistrationNativePlatformMldsaProgram.coins setup codec
      (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
      (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
      sign helper writer roots control initial message

noncomputable def closed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots) :
    QueryImpl RegistrationNativePlatformServerFrontendProgram.Spec (StateT (State n Platform) ProbComp) :=
  fun request state => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (implementation source roots)
      ((target source view failure allocation erased helper sign writer reserve request).run state.1)).run state.2

private theorem service_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (message : RegistrationNativeRelatedFamily.Message)
    (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer reserve roots).flattenStateT
      (.service control initial message)).run state =
      (closed setup.source view failure allocation erased helper sign writer reserve roots (.service control initial message)).run (strip state) := by
  have native := RegistrationNativePlatformServerRestrictedService.source_service setup codec view failure allocation erased helper sign writer
    roots control initial message state.1 state.2
  have interpreted := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    action.run (RegistrationNativeWorldView.project state.1.world.1))
    (service_run setup.source view failure allocation erased helper sign writer roots control initial message (state.1.world.2, state.2))
  simp only [RegistrationNativePlatformWorldEffectView.close, StateT.run, Functor.map_map] at native
  have combined := native.trans interpreted.symm
  convert combined using 1 <;>
    simp only [actual, closed, target, QueryImpl.flattenStateT, StateT.run, StateT.mk,
      Functor.map_map, Prod.map, id_eq, strip] <;> rfl


private theorem pin_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (current : session.ServerAuthenticationPin) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer reserve roots).flattenStateT (.pin current)).run state =
      (closed setup.source view failure allocation erased helper sign writer reserve roots (.pin current)).run (strip state) := by
  have native := RegistrationNativePlatformServerRestrictedService.pin_source current state.1 state.2
  convert native using 1 <;>
    simp only [actual, closed, target, liftEffects, effects_program, QueryImpl.flattenStateT,
      RegistrationNativePlatformWorldEffectView.close, StateT.run, StateT.mk,
      Functor.map_map, Prod.map, id_eq, strip] <;> rfl

omit primitive in
private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem effect_source (effect : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (state : Local n × Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins effect).run state.1).run state.2 =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        ((RegistrationNativePlatformWorldEffectView.close
          (RegistrationNativePlatformEffectCompiler.effect (Platform := PublicState Platform) effect)).run
          (RegistrationNativeWorldView.project state.1.world.1)).run (state.1.world.2, state.2) := by
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
    simp only [RegistrationNativePlatformWorldEffectView.close, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run, lift_apply, map_apply, simulateQ_map, simulateQ_spec_query, Functor.map_map, Prod.map, id_eq]
  all_goals rfl

private theorem present_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (keyId : U64) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer reserve roots).flattenStateT (.present keyId)).run state =
      (closed setup.source view failure allocation erased helper sign writer reserve roots (.present keyId)).run (strip state) := by
  have native := effect_source (.inr (.peerPresent keyId)) state
  convert native using 1 <;>
    simp only [actual, closed, target, liftEffects, effects_program, QueryImpl.flattenStateT,
      RegistrationNativePlatformWorldEffectView.close, StateT.run, StateT.mk,
      Functor.map_map, Prod.map, id_eq, strip] <;> rfl


omit primitive in
private theorem external_program (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n) :
    simulateQ RegistrationNativePlatformWorldEffectView.implementation
      (simulateQ RegistrationNativePlatformEffectCompiler.publicCoin work) (RegistrationNativeWorldView.project before) =
      (fun value => (value, RegistrationNativeWorldView.project before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, map_pure]; rfl
  | query_bind coin next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformEffectCompiler.publicCoin,
        StateT.run, bind_apply, RegistrationNativePlatformWorldEffectView.implementation,
        RegistrationNativePlatformWorldEffectClosure.implementation, lift_apply,
        Functor.map_map, Prod.map, id_eq, RegistrationNativeWorldView.project_idempotent,
        bind_map_left, map_bind]
      apply bind_congr
      intro value
      exact ih value before

private theorem reserve_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer reserve roots).flattenStateT .reserve).run state =
      (closed setup.source view failure allocation erased helper sign writer reserve roots .reserve).run (strip state) := by
  simp only [actual, closed, target, liftEffects, effects_program,
    RegistrationNativePlatformBoundCompiler.liftPlatform, RegistrationNativePlatformEffectCompiler.compile,
    QueryImpl.flattenStateT, StateT.run, StateT.mk, lift_apply, map_apply, simulateQ_map,
    external_program, Functor.map_map, Prod.map, id_eq, strip]


private theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (request : RegistrationNativePlatformServerFrontendProgram.Spec.Domain) (state : Local n × Platform) :
    Prod.map id strip <$> ((actual setup codec view failure allocation erased helper sign writer reserve roots).flattenStateT request).run state =
      (closed setup.source view failure allocation erased helper sign writer reserve roots request).run (strip state) := by
  cases request with
  | pin current => exact pin_query setup codec view failure allocation erased helper sign writer reserve roots current state
  | reserve => exact reserve_query setup codec view failure allocation erased helper sign writer reserve roots state
  | present keyId => exact present_query setup codec view failure allocation erased helper sign writer reserve roots keyId state
  | service control initial message => exact service_query setup codec view failure allocation erased helper sign writer reserve roots control initial message state

/-- Every adaptive continuation of the complete source-reference build uses the same private World and external platform execution under the named instrumentation view. -/
theorem work (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A) (state : Local n × Platform) :
    Prod.map id strip <$> (simulateQ (actual setup codec view failure allocation erased helper sign writer reserve roots).flattenStateT work).run state =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer reserve roots) work).run (strip state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ strip
    (query setup codec view failure allocation erased helper sign writer reserve roots) work state

private theorem actual_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) :
    simulateQ (actual (n := n) setup codec view failure allocation erased helper sign writer reserve roots)
      ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before) =
      (RegistrationNativePlatformServerMaterialFrontend.build
        (RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins)
        (StateT.lift reserve)
        (fun keyId => RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins (.peerPresent keyId))
        (RegistrationNativePlatformServerMaterialState.service RegistrationNativePlatformMldsaProgram.coins setup codec
          (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
          (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
          sign helper writer roots) handle application).run before := by
  rw [RegistrationNativePlatformServerFrontendProgram.interpret]
  rfl

/-- The complete corrected source-reference build, whose private restoration is the literal source SDK build, is this executable public client on all outcomes. Root bytes occur only in the private demand interpretation. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      (((RegistrationNativePlatformServerMaterialFrontend.build
        (RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins)
        (StateT.lift reserve)
        (fun keyId => RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins (.peerPresent keyId))
        (RegistrationNativePlatformServerMaterialState.service RegistrationNativePlatformMldsaProgram.coins setup codec
          (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
          (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
          sign helper writer roots) handle application).run front).run before).run previous =
      (simulateQ (closed setup.source view failure allocation erased helper sign writer reserve roots)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run (strip (before, previous)) := by
  have same := work setup codec view failure allocation erased helper sign writer reserve roots
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front) (before, previous)
  rw [OracleComp.simulateQ_flattenStateT_run, actual_program, bind_pure_comp] at same
  simpa only [Functor.map_map, Prod.map, id_eq] using same

/-- The source macro fold is exactly the free client interpretation on one public receipt/platform state beside the private World. -/
theorem interpret (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A) (state : State n Platform) :
    (simulateQ (closed source view failure allocation erased helper sign writer reserve roots) work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (implementation source roots)
          ((simulateQ (target source view failure allocation erased helper sign writer reserve) work).run state.1)).run state.2 := by
  have same : closed (n := n) source view failure allocation erased helper sign writer reserve roots =
      ((implementation (n := n) source roots).mapStateTBase (target source view failure allocation erased helper sign writer reserve)).flattenStateT := rfl
  rw [same, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run, bind_pure_comp]

end BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler.work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler.work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler.interpret
