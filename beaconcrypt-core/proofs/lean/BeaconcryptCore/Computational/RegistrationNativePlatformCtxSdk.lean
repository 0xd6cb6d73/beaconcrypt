-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion
/-! The literal source SDK build has a complete physical-CTX implementation. All individual pin, platform, capability and supplied-pending completion laws are discharged by source lemmas; existing independent root auxiliaries remain in the joint-Ed context. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork publicWork)
open RegistrationNativePlatformCtxSdkCoupling (Native Coupled realize replace)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

def world (work : M (Local n) Platform A) : M (State n) Platform A := RegistrationNativePlatformServerSdk.world work

noncomputable def pin : M (State n) Platform (RustM (core.option.Option session.ServerAuthenticationPin)) := fun before =>
  (world (privateWork (RegistrationNativePlatformCtxPin.pin before.pin))) before

/-- The owned transcript continuation uses the same physical hash interpreter as all other SDK hashes. -/
noncomputable def adHash (pending : registration.ServerAdHash) :
    M (State n) Platform RegistrationServerAdHash.Result :=
  RegistrationServerAdHash.runWith (fun request => do
    let digest ← world (privateWork (RegistrationNativePlatformCtxLocal.effects
      (.inr (.hash (RegistrationInputs.hashBytes request)))))
    pure (.Some (RegistrationAuthenticationShared.digestArray digest))) pending

noncomputable def present (keyId : U64) : M (State n) Platform Bool :=
  world (privateWork (RegistrationNativePlatformCtxLocal.effects (.inr (.peerPresent keyId))))

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let reply ← work before; next reply.1 reply.2) := rfl

/-- Moving an actual Local callback into the complete SDK preserves every source field and the physical hash interpretation. -/
theorem world_source (left : M (Local n) Platform A) (right : StateT (Local n) (StateT Platform ProbComp) A)
    (coupled : ∀ before : Full (Local n) Platform,
      Prod.map id RegistrationNativePlatformCtxLocal.realize <$> (interpret left).run before =
        (pack right).run (RegistrationNativePlatformCtxLocal.realize before)) :
    Coupled (world left) (RegistrationNativePlatformServerSdk.world right) := by
  intro before
  have same := congrArg (fun distribution => (fun result =>
    (result.1, ({(realize before).1 with world := result.2.1}, result.2.2))) <$> distribution)
    (coupled ((before.1.1.world, before.1.2), before.2))
  simpa only [world, RegistrationNativePlatformServerSdk.world, interpret, pack, StateT.run,
    simulateQ_map, state_map_apply, Functor.map_map, realize, replace,
    RegistrationNativePlatformCtxLocal.realize, RegistrationNativePlatformCtxLocal.attach,
    RegistrationNativePlatformCtxCacheFrame.replace, Prod.map_def, id_eq] using same

/-- Pure selection retains the complete supplied Server pin and full SDK state without a hash callback. -/
theorem pin_source : Coupled (pin : M (State n) Platform _)
    (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins) := by
  intro before
  have same := world_source (privateWork (RegistrationNativePlatformCtxPin.pin before.1.1.pin))
    (RegistrationNativePlatformServerMaterialState.pin RegistrationNativePlatformMldsaProgram.coins before.1.1.pin)
    (RegistrationNativePlatformCtxPin.pin_source before.1.1.pin) before
  simpa only [pin, world, RegistrationNativePlatformServerSdk.world,
    RegistrationNativePlatformSourceBuild.pin, RegistrationNativePlatformServerMaterialState.pin,
    interpret, RegistrationNativePlatformPackedState.pack, StateT.run, simulateQ_map, state_map_apply,
    Functor.map_map, realize, replace, RegistrationNativePlatformCtxLocal.attach,
    RegistrationNativePlatformCtxCacheFrame.replace, Prod.map_def, id_eq] using same

private theorem native_world_pure {Value : Type} (value : Value) :
    RegistrationNativePlatformServerSdk.world
        (pure value : StateT (Local n) (StateT Platform ProbComp) Value) = pure value := by
  funext before previous
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run_pure, map_pure]
  rfl

private theorem native_world_bind {Value Next : Type}
    (work : StateT (Local n) (StateT Platform ProbComp) Value)
    (next : Value → StateT (Local n) (StateT Platform ProbComp) Next) :
    RegistrationNativePlatformServerSdk.world (work >>= next) =
      (RegistrationNativePlatformServerSdk.world work >>= fun value =>
        RegistrationNativePlatformServerSdk.world (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, state_bind_apply,
    state_map_apply, map_bind, bind_map_left, Prod.map_def, id_eq]

/-- The real AD hash reaches the same core continuation, returned metadata, complete source cache and platform poststate. -/
theorem adHash_source (pending : registration.ServerAdHash) :
    Coupled (adHash (n := n) (Platform := Platform) pending)
      (RegistrationNativePlatformCompletionSdk.nativeAdHash RegistrationNativePlatformMldsaProgram.coins pending) := by
  unfold adHash RegistrationNativePlatformCompletionSdk.nativeAdHash
    RegistrationNativePlatformServerSdk.adHash RegistrationNativePlatformServerCompletion.adHash
    RegistrationNativePlatformServerCompletion.adHashWith RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div =>
    rw [native_world_pure]
    exact RegistrationNativePlatformCtxSdkCoupling.pure_source _
  | ok request =>
    simp only [native_world_bind, native_world_pure, bind_assoc, pure_bind]
    exact RegistrationNativePlatformCtxSdkCoupling.bind_source _ _ _ _
      (world_source _ _ (RegistrationNativePlatformCtxPin.capability_source
        (.hash (RegistrationInputs.hashBytes request))))
      (fun _ => RegistrationNativePlatformCtxSdkCoupling.pure_source _)

/-- Public reservation consumes only the actual external platform state and keeps native/private state intact. -/
theorem reserve_source (reserve : StateT Platform ProbComp Bool) :
    Coupled (publicWork reserve : M (State n) Platform Bool) (StateT.lift reserve) := by
  intro before
  rw [RegistrationNativePlatformCtxRunner.public_run]
  simp only [RegistrationNativePlatformPackedState.pack, StateT.run, state_map_apply,
    StateT.lift, bind_pure_comp, Functor.map_map, realize, Prod.map_def, id_eq]

/-- Actual occupancy is interpreted through the same individual native capability leaf. -/
theorem present_source (keyId : U64) : Coupled (present keyId : M (State n) Platform Bool)
    (RegistrationNativePlatformCompletionSdk.nativePresent RegistrationNativePlatformMldsaProgram.coins keyId) :=
  world_source _ _ (RegistrationNativePlatformCtxPin.capability_source (.peerPresent keyId))

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def build (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    M (State n) Platform (RustM (Option (U64 × alloc.vec.Vec U8))) :=
  RegistrationNativePlatformCompletionSdk.build adHash pin (publicWork reserve) present
    (RegistrationNativePlatformCtxCompletion.completion setup codec view failure allocation erased sign helper writer) handle application

/-- The complete literal SDK build has no remaining whole-callback law: every leaf is the checked source interpretation on the same physical and platform state. -/
theorem build_source (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    Coupled (build (n := n) setup codec view failure allocation erased sign helper writer reserve handle application)
      (RegistrationNativePlatformSourceBuild.buildSource RegistrationNativePlatformMldsaProgram.coins setup codec
        (RegistrationNativePlatformSourceSeal.sealing RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation)
        (RegistrationNativePlatformSourceSeal.hash RegistrationNativePlatformMldsaProgram.coins setup codec erased)
        reserve sign helper writer handle application) := by
  apply RegistrationNativePlatformCtxSdkCoupling.build_source
    (deriveAdLeft := adHash)
    (deriveAdRight := RegistrationNativePlatformCompletionSdk.nativeAdHash RegistrationNativePlatformMldsaProgram.coins)
    (ad := adHash_source)
  · exact pin_source
  · exact reserve_source reserve
  · exact present_source
  · intro control pending
    exact world_source _ _ (RegistrationNativePlatformCtxCompletion.completion_source setup codec view failure allocation erased sign helper writer control pending)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.world_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.pin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.adHash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.adHash_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.reserve_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.reserve_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.present_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.present_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk.build_source
