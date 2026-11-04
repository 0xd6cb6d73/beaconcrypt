-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin
/-! The executable corrected Server build uses only public reference control, internal signing receipts and persistent platform state. Material choice is a typed demand, ordinary local work uses the separate external-coin branch, and all World access is through restricted effects. The real and hidden demand interpreters remain separate from this public code. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativePlatformBoundCompiler (PublicState State strip)
open RegistrationNativePairedChoice (Choice PrivateChoice publicChoice)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

noncomputable def branch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) :
    Choice n → StateT (PublicState Platform) (OracleComp (Spec n))
      (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)))
  | .known output => simulateQ
      (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
      (RegistrationNativePlatformPairedServerCompiler.known control)
  | .hidden reference => simulateQ
      (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial
        (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed))
      (RegistrationNativePlatformPairedServerCompiler.hidden control reference.slot)

noncomputable def admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (demand : RegistrationNativeRelatedFamily.Message → StateT (PublicState Platform) (OracleComp (Spec n)) (Option (Choice n)))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    StateT (PublicState Platform) (OracleComp (Spec n)) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) := do
  let selected ← demand message
  match selected with
  | none => pure (.ok (.Err control))
  | some selected => branch source view failure allocation erased helper sign writer control initial selected

omit primitive in
def pin (current : session.ServerAuthenticationPin) :
    StateT (PublicState Platform) (OracleComp (Spec n)) (RustM (core.option.Option session.ServerAuthenticationPin)) := do
  let digest ← RegistrationNativePlatformEffectCompiler.effect
    (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))
  pure (.ok (.Some ⟨current.binding, current.public_key, RegistrationAuthenticationShared.digestArray digest⟩))

noncomputable def build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)
    (demand : RegistrationNativeRelatedFamily.Message → StateT (PublicState Platform) (OracleComp (Spec n)) (Option (Choice n)))
    (handle : Nat) (application : Option (Slice U8)) :
    StateT RegistrationServerMaterialFrontend.State
      (StateT (PublicState Platform) (OracleComp (Spec n)))
      (RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) :=
  RegistrationNativePlatformServerMaterialFrontend.build pin
    (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile reserve))
    (fun keyId => RegistrationNativePlatformEffectCompiler.effect (.inr (.peerPresent keyId)))
    (admitted source view failure allocation erased helper sign writer demand) handle application

/-- A concrete private known/hidden source branch lowers to the same public branch. Only material44 and the private slot remain in its selected branch code. -/
theorem source_branch (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (choice : PrivateChoice n)
    (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformPairedServerService.privateBranch
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        (RegistrationNativePlatformSourceBuild.write helper)
        (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign)
        (RegistrationNativePlatformSourceBuild.encode writer)
        (RegistrationNativePlatformPairedServerService.nativeEffects RegistrationNativePlatformMldsaProgram.coins)
        control initial choice).run before).run previous =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        ((RegistrationNativePlatformWorldEffectView.close
          (branch setup.source view failure allocation erased helper sign writer control initial (publicChoice choice))).run
          (RegistrationNativeWorldView.project before.world.1)).run (before.world.2, previous) := by
  cases choice with
  | known output =>
      have actual := RegistrationNativePlatformPairedServerCompiler.known_source setup codec view failure allocation erased helper sign writer
        initial output control before previous
      rw [RegistrationNativePlatformPairedServerCompiler.interpret] at actual
      simpa only [RegistrationNativePlatformPairedServerService.privateBranch, publicChoice, branch, strip] using actual
  | hidden slot output =>
      have actual := RegistrationNativePlatformPairedServerCompiler.hidden_source setup codec view failure allocation erased helper sign writer
        control slot initial (PqxdhDeploymentHiddenLayout.splitOutput output).1
        (PqxdhDeploymentHiddenLayout.splitOutput output).2 before previous
      rw [PqxdhDeploymentHiddenLayout.join_split, RegistrationNativePlatformPairedServerCompiler.interpret] at actual
      simpa only [RegistrationNativePlatformPairedServerService.privateBranch, publicChoice, branch, strip] using actual


omit primitive in
private theorem native_program {A : Type} (work : ProbComp A) :
    simulateQ (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform)) work = StateT.lift work := by
  have coins : RegistrationNativePlatformMldsaProgram.coins (Platform := Platform) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Platform ProbComp) := rfl
  rw [coins, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  rfl

omit primitive in
private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

omit primitive in
private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem bind_apply {S V W : Type} {q : Type → Type} [Monad q]
    (work : StateT S q V) (next : V → StateT S q W) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

omit primitive in
private theorem pure_apply {S V : Type} {q : Type → Type} [Monad q] (value : V) (before : S) :
    (pure value : StateT S q V) before = pure (value, before) := rfl

omit primitive in
private theorem native_pin_apply (current : session.ServerAuthenticationPin) (before : PqxdhRecordLiftWorld.State n) :
    RegistrationNativeServerPinRecompute.native current.binding current.public_key before = (do
      let hashed ← PqxdhRecordLiftWorld.effects (.inr (.hash (PqxdhRefinement.absBytes current.public_key))) before
      pure (.ok (.Some (⟨current.binding, current.public_key, RegistrationAuthenticationShared.digestArray hashed.1⟩ : session.ServerAuthenticationPin)), hashed.2)) :=
  RegistrationNativeServerPinRecompute.native_run current.binding current.public_key before

omit primitive in
/-- Repeated source pin recomputation is the same literal public-key hash in this client, retaining its extra hash charge and all actual uniform/cache effects. -/
theorem pin_source (current : session.ServerAuthenticationPin) (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins current).run before).run previous =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        ((RegistrationNativePlatformWorldEffectView.close (pin current)).run
          (RegistrationNativeWorldView.project before.world.1)).run (before.world.2, previous) := by
  have actual := RegistrationNativePlatformWorldEffectView.program
    ((Spec n).query (.inl (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))) : OracleComp (Spec n) _) before.world.1
  simp only [simulateQ_spec_query, RegistrationNativePlatformWorldEffectClosure.implementation] at actual
  have mapped := congrArg (fun action => (fun result =>
    ((.ok (.Some (⟨current.binding, current.public_key, RegistrationAuthenticationShared.digestArray result.1⟩ : session.ServerAuthenticationPin)) :
      RustM (core.option.Option session.ServerAuthenticationPin)), ((before.world.2, previous), result.2))) <$> action) actual
  convert mapped using 1 <;>
    simp only [RegistrationNativePlatformServerMaterialState.pin, native_program,
      RegistrationNativePlatformWorldEffectView.close, pin, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run, native_pin_apply, bind_apply, pure_apply, lift_apply, map_apply,
      simulateQ_map, simulateQ_spec_query,
      bind_pure_comp, Functor.map_map, Prod.map, id_eq, strip]
  all_goals rfl


/-- The concrete private-root source service restores only its actual earlier root and exact KDF accounting prefix; the executable branch receives its material reply, not the root table. -/
theorem source_service (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (roots : RegistrationServerReferenceRestore.Roots) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (message : RegistrationNativeRelatedFamily.Message)
    (before : Local n) (previous : Platform) :
    (fun result => (result.1.1, strip (result.1.2, result.2))) <$>
      ((RegistrationNativePlatformServerMaterialState.service RegistrationNativePlatformMldsaProgram.coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        sign helper writer roots control initial message).run before).run previous =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        ((RegistrationNativePlatformWorldEffectView.close
          (branch setup.source view failure allocation erased helper sign writer control initial
            (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source (roots message))))).run
            (RegistrationNativeWorldView.project before.world.1)).run (before.world.2, previous) := by
  have same := source_branch setup codec view failure allocation erased helper sign writer control initial
    (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source (roots message)))
    (RegistrationNativePlatformPrivateKdfState.ratchetState (RegistrationNativePlatformPrivateKdfState.initialState before)) previous
  simp only [RegistrationNativePlatformServerMaterialState.service, StateT.run_bind, StateT.run_modify, pure_bind]
  convert same using 1 <;>
    simp only [RegistrationNativePlatformPairedServerService.privateBranch, publicChoice]
  all_goals rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService.source_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService.source_branch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService.pin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService.source_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerRestrictedService.source_service
