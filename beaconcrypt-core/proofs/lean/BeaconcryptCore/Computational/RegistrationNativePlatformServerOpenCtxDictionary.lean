-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The OPEN CTX dictionary also targets an arbitrary shared monad. Its backend embedding exposes hashes while supplied indexed/root-reference leaves may remain open protocol queries in a larger language. No indexed operation is replaced by a closed uniform sampler. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceWorld (Private)
variable {n : Nat} {ι KemSK Extra Platform Value : Type} {base : OracleSpec ι}
section
variable {m : Type → Type} [Monad m] [LawfulMonad m]

structure Callbacks (n : Nat) (KemSK Extra : Type) (m : Type → Type) where
  prepare : QueryImpl RegistrationServerReferenceRoot.PrepareSpec (StateT (Private n KemSK Extra) m)
  demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m)
  publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m)
  indexed : QueryImpl (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) (StateT (Private n KemSK Extra) m)

noncomputable def effects (backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec m)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) : StateT (Private n KemSK Extra) m ((PqxdhRecordLiftInterface.EnvEffects n).Range query) :=
  RegistrationNativePlatformServerOpenEffects.withWorld
    (RegistrationNativePlatformInterpret.state backend (RegistrationNativePlatformCtxEffects.program query))

noncomputable def handler (backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec m) (callbacks : Callbacks n KemSK Extra m) :
    QueryImpl (RegistrationNativeKemReferenceCompiler.Spec n KemSK) (StateT (Private n KemSK Extra) m)
  | .inl query => callbacks.prepare query
  | .inr (.inl (.inl query)) => callbacks.demand query
  | .inr (.inl (.inr (.inl query))) => callbacks.publication query
  | .inr (.inl (.inr (.inr query))) => effects backend query
  | .inr (.inr query) => callbacks.indexed query

noncomputable def extended (backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec m)
    (callbacks : Callbacks n KemSK Extra m) (reserve : m Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (StateT (Private n KemSK Extra) m)
  | .inl query => handler backend callbacks query
  | .inr _ => StateT.lift reserve

noncomputable def accept (backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec m)
    (callbacks : Callbacks n KemSK Extra m) (reserve : m Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) :=
  RegistrationNativePlatformServerOpenControl.close (RegistrationNativePlatformServerOpenControl.accept
    (handler backend callbacks) (StateT.lift reserve) setup checks verify packet)

theorem source (backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec m)
    (callbacks : Callbacks n KemSK Extra m) (reserve : m Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) :
    accept backend callbacks reserve setup checks verify packet =
      RegistrationNativePlatformServerOpenControl.close (RegistrationNativePlatformServerOpenSyntax.evaluate
        (extended backend callbacks reserve) (RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet)) := by
  exact (congrArg (RegistrationNativePlatformServerOpenControl.close (n := n) (KemSK := KemSK) (Extra := Extra))
    (RegistrationNativePlatformServerOpenSyntax.accept_source (extended backend callbacks reserve) setup checks verify packet)).symm

end

def backend : QueryImpl RegistrationNativePlatformCtxBackend.Spec (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) :=
  (QueryImpl.id' RegistrationNativePlatformCtxBackend.Spec).liftTarget (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec))

def concrete (callbacks : RegistrationNativePlatformServerOpenCtxKernel.Callbacks n KemSK Extra Platform) :
    Callbacks n KemSK Extra (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) :=
  ⟨callbacks.prepare, callbacks.demand, callbacks.publication, callbacks.indexed⟩

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem state_liftM_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (liftM work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem effects_specialize (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    effects (KemSK := KemSK) (Extra := Extra) (backend (Platform := Platform)) query =
      RegistrationNativePlatformServerOpenCtxEffects.effect query := by
  funext before currentP
  simp only [effects, backend, RegistrationNativePlatformServerOpenCtxEffects.effect,
    RegistrationNativePlatformServerOpenEffects.withWorld, RegistrationNativePlatformCtxRunner.privateWork,
    RegistrationNativePlatformInterpret.state, StateT.run, simulateQ_liftTarget, simulateQ_id',
    state_map_apply, state_lift_apply, state_liftM_apply, bind_pure_comp, Functor.map_map]
  rfl

theorem handler_specialize (callbacks : RegistrationNativePlatformServerOpenCtxKernel.Callbacks n KemSK Extra Platform) :
    handler backend (concrete callbacks) = RegistrationNativePlatformServerOpenCtxKernel.handler callbacks := by
  funext query
  cases query with
  | inl query => rfl
  | inr query => cases query with
    | inr query => rfl
    | inl query => cases query with
      | inl query => rfl
      | inr query => cases query with
        | inl query => rfl
        | inr query => exact effects_specialize query

def publicReserve (reserve : StateT Platform ProbComp Bool) : StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec) Bool :=
  fun before => simulateQ RegistrationNativePlatformCtxBackend.coin (reserve.run before)

theorem reserve_specialize (reserve : StateT Platform ProbComp Bool) :
    (StateT.lift (publicReserve reserve) : StateT (Private n KemSK Extra) (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Bool) =
      RegistrationNativePlatformCtxRunner.publicWork reserve := by
  funext before currentP
  change ((StateT.lift (publicReserve reserve) : StateT (Private n KemSK Extra) (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Bool).run before).run currentP = _
  simp only [RegistrationNativePlatformCtxRunner.publicWork, StateT.run, state_lift_apply,
    state_map_apply, publicReserve, bind_pure_comp, Prod.map_def]
  rfl

theorem accept_specialize (callbacks : RegistrationNativePlatformServerOpenCtxKernel.Callbacks n KemSK Extra Platform)
    (reserve : StateT Platform ProbComp Bool) (setup : Setup base KemSK) (checks : Checks)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) :
    accept backend (concrete callbacks) (publicReserve reserve) setup checks verify packet =
      RegistrationNativePlatformServerOpenCtxAccept.accept callbacks reserve setup checks verify packet := by
  unfold accept RegistrationNativePlatformServerOpenCtxAccept.accept
  rw [handler_specialize, reserve_specialize]

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.effects_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.effects_specialize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.handler_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.handler_specialize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.reserve_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.reserve_specialize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.accept_specialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxDictionary.accept_specialize
