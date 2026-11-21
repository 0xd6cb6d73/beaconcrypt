-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformWorldEffectClosure
import BeaconcryptCore.Computational.RegistrationServerSigningWorldSource
/-! Actual source signing forwards its draws through restricted native coin effects and retains chronological attempts in internal protocol metadata. External platform randomness stays on the distinct public branch. The compiler state contains only receipts and persistent platform state; the private World remains separate. Receipts are not allocator requests or API observations. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler
open RegistrationNativePlatformEffectCompiler (Spec)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerRecordWorldSource (project)
variable {n : Nat} {Auxiliary Platform A : Type}

abbrev State (Platform : Type) := List RegistrationSigningShared.Receipt × Platform

def forward : QueryImpl (EnvEffects n) (OracleComp (Spec n)) := fun query => (Spec n).query (.inl query)

def signing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State Platform) (OracleComp (Spec n))) := fun query previous =>
  (fun result => (result.1, (result.2, previous.2))) <$>
    simulateQ forward ((RegistrationBoundSourceCompiler.compiler source writer sign (.inr query)).run previous.1)

def restored (before : RegistrationWorldAgreement.State n Auxiliary) (world : PqxdhRecordLiftWorld.State n)
    (receipts : List RegistrationSigningShared.Receipt) : RegistrationWorldAgreement.State n Auxiliary :=
  { project before with world := (RegistrationNativeWorldView.project world, receipts) }

private theorem effect_program (work : OracleComp (EnvEffects n) A) :
    simulateQ RegistrationNativePlatformWorldEffectClosure.implementation (simulateQ forward work) =
      simulateQ PqxdhRecordLiftWorld.effects work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler work)
  funext query
  simp only [QueryImpl.apply_compose, forward, simulateQ_spec_query,
    RegistrationNativePlatformWorldEffectClosure.implementation]

private theorem native_program (work : ProbComp A) :
    simulateQ (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform)) work = StateT.lift work := by
  have coins : RegistrationNativePlatformMldsaProgram.coins (Platform := Platform) =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Platform ProbComp) := rfl
  rw [coins, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  rfl

private theorem lift_apply {S V : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (work : q V) (before : S) :
    (StateT.lift work : StateT S q V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem map_apply {S V W : Type} {q : Type → Type} [Monad q] [LawfulMonad q]
    (f : V → W) (work : StateT S q V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Every actual source ML-sign/hash reply, receipt and shared-cache draw agrees with the World-free receipt compiler after its explicitly stated native/coin instrumentation view. Native signing randomness is never reclassified as external platform randomness. -/
theorem source (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) (previous : Platform) :
    ((Prod.map id project <$>
      (RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign query).run before).run previous) =
      (fun result => ((result.1.1, restored before result.1.2 result.2.1), result.2.2)) <$>
        ((RegistrationNativePlatformWorldEffectClosure.close (signing hkdf writer sign query)).run before.world.1).run
          (before.world.2, previous) := by
  have native := (RegistrationServerSigningWorldSource.source_query sign query before).trans
    (RegistrationServerSigningWorldSource.compiler_query hkdf writer sign query before).symm
  have mapped := congrArg (fun action => (fun result => (result, previous)) <$> action) native
  simpa only [RegistrationNativePlatformServerCompletion.outgoing,
    RegistrationNativePlatformServerCompletion.liftNative, RegistrationNativePlatformServerCompletion.nativeOutgoing,
    RegistrationServerSigningWorldSource.source, RegistrationServerSigningWorldSource.compiler,
    RegistrationNativePlatformWorldEffectClosure.close, signing, restored, StateT.run_map, StateT.run,
    native_program, StateT.run_lift, lift_apply, map_apply, bind_pure_comp, simulateQ_map, effect_program,
    Functor.map_map, Prod.map, id_eq, project] using mapped

/-- The pointwise interpretation starts the actual callback at its derived source view, so it composes with arbitrary later controller queries on the separate private World. -/
theorem at_view (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) (previous : Platform) :
    ((RegistrationNativePlatformServerCompletion.outgoing RegistrationNativePlatformMldsaProgram.coins sign query).run (project before)).run previous =
      (fun result => ((result.1.1, restored before result.1.2 result.2.1), result.2.2)) <$>
        ((RegistrationNativePlatformWorldEffectClosure.close (signing hkdf writer sign query)).run before.world.1).run
          (before.world.2, previous) := by
  have mapped := congrArg (fun action => (fun result => (result, previous)) <$> action)
    (RegistrationServerSigningWorldSource.compiler_query hkdf writer sign query before).symm
  simpa only [RegistrationNativePlatformServerCompletion.outgoing,
    RegistrationNativePlatformServerCompletion.liftNative, RegistrationNativePlatformServerCompletion.nativeOutgoing,
    RegistrationServerSigningWorldSource.source, RegistrationServerSigningWorldSource.compiler,
    RegistrationNativePlatformWorldEffectClosure.close, signing, restored, StateT.run_map, StateT.run,
    native_program, StateT.run_lift, lift_apply, map_apply, bind_pure_comp, simulateQ_map, effect_program,
    Functor.map_map, Prod.map, id_eq, project] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler.at_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSigningCompiler.at_view
