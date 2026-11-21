-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxLocal
/-! Native response signing exposes its literal hash input while retaining every signing draw and chronological receipt, including failed signing and later publication failure. Receipt privacy is a later explicit source projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning
open RegistrationWorldAgreement (State)
open RegistrationNativePlatformCtxBackend (Spec coin)
open RegistrationNativePlatformCtxRunner (Full interpret privateWork)
open RegistrationNativePlatformCtxLocal (realize attach)
open RegistrationNativePlatformCtxCacheFrame (replace)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (replyBytes)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {n : Nat} {Auxiliary Platform A : Type}

noncomputable def outgoing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State n Auxiliary) (OracleComp Spec))
  | .hash request => RegistrationNativePlatformCtxLocal.effects (.inr (.hash (hashBytes request)))
  | .sign request payload digest => fun before =>
      (fun result => (result.1, {before with world := (result.2,
        before.world.2 ++ [⟨⟨request.public_key, payload, replyBytes result.1⟩, digest⟩])})) <$>
      simulateQ coin ((PqxdhRecordLiftWorld.sampled (sign request)).run before.world.1)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

theorem query_source (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (outgoing sign query))).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (RegistrationNativePlatformServerCompletion.nativeOutgoing sign query).run (realize before).1 := by
  cases query with
  | hash request =>
    simpa only [outgoing, RegistrationNativePlatformServerCompletion.nativeOutgoing,
      RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, attach] using
      RegistrationNativePlatformCtxLocal.effects_source (.inr (.hash (hashBytes request))) before
  | sign request payload digest =>
    rw [RegistrationNativePlatformCtxRunner.private_run]
    have source := RegistrationNativePlatformCtxCacheFrame.sampled before.2.1 (sign request) before.1.1.world.1
    have mapped := congrArg (fun action => (fun (result : RegistrationSigningShared.SignReply × PqxdhRecordLiftWorld.State n) => (result.1,
      ({(realize before).1 with world := (result.2,
        before.1.1.world.2 ++ [(⟨⟨request.public_key, payload, replyBytes result.1⟩, digest⟩ : RegistrationSigningShared.Receipt)])}, before.1.2))) <$> action) source
    simpa only [outgoing, StateT.run, simulateQ_map, RegistrationNativePlatformCtxBackend.coins,
      state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map,
      RegistrationNativePlatformServerCompletion.nativeOutgoing, RegistrationWorldSigning.outgoing,
      realize, attach, replace, Prod.map_def, id_eq] using mapped

theorem complete (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec A) (before : Full (State n Auxiliary) Platform) :
    Prod.map id realize <$> (interpret (privateWork (simulateQ (outgoing sign) work))).run before =
      (fun result => (result.1, (result.2, before.1.2))) <$>
        (simulateQ (RegistrationNativePlatformServerCompletion.nativeOutgoing sign) work).run (realize before).1 := by
  rw [RegistrationNativePlatformCtxLocal.private_program, RegistrationNativePlatformCtxRunner.simulate]
  have leaf (query : RegistrationSigningShared.Spec.Domain) (current : Full (State n Auxiliary) Platform) :
      Prod.map id realize <$> (interpret (privateWork (outgoing sign query))).run current =
        (RegistrationNativePlatformCtxLocal.native (RegistrationNativePlatformServerCompletion.nativeOutgoing sign) query).run (realize current) := by
    have transport := RegistrationNativePlatformCtxLocal.native_program
      (RegistrationNativePlatformServerCompletion.nativeOutgoing sign)
      (RegistrationSigningShared.Spec.query query : OracleComp RegistrationSigningShared.Spec _) (realize current)
    simp only [simulateQ_spec_query] at transport
    exact (query_source sign query current).trans transport.symm
  have whole := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => interpret (privateWork (outgoing sign query)))
    (RegistrationNativePlatformCtxLocal.native (RegistrationNativePlatformServerCompletion.nativeOutgoing sign))
    realize leaf work before
  rw [RegistrationNativePlatformCtxLocal.native_program] at whole
  exact whole
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSigning.complete
