-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerWorldInstallSource
import BeaconcryptCore.Computational.RegistrationServerRecordTargetProjection

/-! The actual native bound publication compiler runs pure components on the caller's current World and signing receipts. This lens preserves the local auxiliary state and request logs; it does not identify an arbitrary mutable environment with a nested copy of itself. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler
variable {n : Nat} {Auxiliary Value : Type}

noncomputable def effect : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n)
    (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) := fun query before =>
  (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
    (PqxdhRecordLiftWorld.effects query).run before.world.1

private theorem effect_run (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    (effect query).run before =
      (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
        (PqxdhRecordLiftWorld.effects query).run before.world.1 := rfl

/-- Arbitrary adaptive pure effect components retain the exact current World and every other local coordinate. -/
theorem effect_program (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    (simulateQ effect work).run before =
      (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, effect_run,
        bind_map_left, ih, map_bind]

noncomputable def publication (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) :=
  fun query before => (fun result => (result.1.1, { before with world := (result.2, result.1.2) })) <$>
    (simulateQ PqxdhRecordLiftWorld.effects
      ((RegistrationBoundSourceCompiler.compiler hkdf writer sign query).run before.world.2)).run before.world.1

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- The actual raw primitive component uses exactly its current World and leaves the signing log unchanged. -/
theorem raw_query (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationRawSealBridge.Spec.Domain) :
    (publication (n := n) (Auxiliary := Auxiliary) hkdf writer sign ∘ₛ RegistrationBoundPublication.rawLift) query =
      (effect ∘ₛ RegistrationBoundSourceCompiler.rawCompiler hkdf writer) query := by
  funext before
  simp only [QueryImpl.apply_compose, RegistrationBoundPublication.rawLift, simulateQ_spec_query,
    publication, RegistrationBoundSourceCompiler.compiler, StateT.run, simulateQ_map,
    state_map_apply, Functor.map_map, Prod.map_def, id_eq]
  have native := effect_program (Auxiliary := Auxiliary)
    (RegistrationBoundSourceCompiler.rawCompiler (n := n) hkdf writer query) before
  simp only [StateT.run] at native
  rw [native]
  rfl

/-- Full native raw components retain the exact World at every adaptive branch. -/
theorem raw_program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    simulateQ (publication (n := n) (Auxiliary := Auxiliary) hkdf writer sign)
      (simulateQ RegistrationBoundPublication.rawLift work) =
      simulateQ effect (simulateQ (RegistrationBoundSourceCompiler.rawCompiler hkdf writer) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreter => simulateQ interpreter work)
  funext query
  exact raw_query hkdf writer sign query

/-- Signing uses the existing exact chronological receipt compiler on the same current World. -/
theorem signing_program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) :
    simulateQ (publication (n := n) (Auxiliary := Auxiliary) hkdf writer sign)
      (simulateQ RegistrationBoundPublication.signingLift work) =
      simulateQ (RegistrationServerSigningWorldSource.compiler hkdf writer sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreter => simulateQ interpreter work)
  funext query
  simp only [QueryImpl.apply_compose, RegistrationBoundPublication.signingLift, simulateQ_spec_query]
  rfl

end BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.effect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.effect_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.raw_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.raw_query
/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.raw_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.signing_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler.signing_program
