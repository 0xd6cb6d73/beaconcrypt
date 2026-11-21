-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublicationStateView
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationNativeBeaconEnvBundle
/-! Literal common-monad bundle control does not inspect the private record-request-kind ledger. Actual trusted signing, source allocation/serialization and every optional writer outcome remain on their original shared state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePlatformGenericBundle (M)
open RegistrationNativeBeaconEnvView (erase project)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary E A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def close (work : M source Auxiliary m A) :
    StateT (RegistrationNativeBeaconFrontend.State source × EnvState Auxiliary) m A := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2
omit [LawfulMonad m] in
private theorem close_run (work : M source Auxiliary m A)
    (before : RegistrationNativeBeaconFrontend.State source × EnvState Auxiliary) :
    (close work).run before = (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2 := rfl
private theorem close_pure (value : A) : close (pure value : M source Auxiliary m A) = pure value := by
  funext before
  simp only [close, StateT.run_pure, map_pure]
  rfl
private theorem close_bind (work : M source Auxiliary m A) (next : A → M source Auxiliary m B) :
    close (work >>= next) = (close work >>= fun value => close (next value)) := by
  funext before
  simp only [close, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]
private theorem close_hom : Cslib.IsMonadHom (M source Auxiliary m)
    (StateT (RegistrationNativeBeaconFrontend.State source × EnvState Auxiliary) m) close :=
  .mk' close_pure close_bind

def Stable (work : M source Auxiliary m A) : Prop := RegistrationStateView.Stable project (close work)
private theorem idem (before : RegistrationNativeBeaconFrontend.State source × EnvState Auxiliary) : project (project before) = project before := rfl
private theorem pure_stable (value : A) : Stable (pure value : M source Auxiliary m A) := by
  unfold Stable
  rw [close_pure]
  exact RegistrationStateView.pure_stable project idem value
private theorem bind_stable (work : M source Auxiliary m A) (next : A → M source Auxiliary m B)
    (first : Stable work) (rest : ∀ value, Stable (next value)) : Stable (work >>= next) := by
  unfold Stable at *
  rw [close_bind]
  exact RegistrationStateView.bind_stable project _ _ first rest
private theorem get_stable : Stable (get : M source Auxiliary m (RegistrationNativeBeaconFrontend.State source)) := by
  intro before
  simp only [close_run, StateT.run_get, StateT.run_pure, map_pure, Prod.map_def, id_eq, project, erase]
private theorem legacy_stable (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) m)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (stable : RegistrationNativeBeaconEnvView.Stable work) : Stable (RegistrationNativePlatformGenericBundle.liftLegacy implementation work) := by
  intro before
  have actual := congrArg (fun action => (fun result => (result.1.1, (result.1.2, result.2))) <$> simulateQ implementation action)
    (RegistrationNativeBeaconEnvView.run_input work stable before.1 before.2)
  simpa only [close, RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, simulateQ_map,
    Functor.map_map, Prod.map_def, id_eq, project] using actual
private theorem external_stable (work : m A) : Stable (StateT.lift (StateT.lift work) : M source Auxiliary m A) := by
  intro before
  simp only [close_run, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, project, erase]

/-- The source common-monad publication body preserves its complete retained owner/Env output through the actual effectful writer. -/
theorem publication (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) m)
    (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (encode : registration.InitView → M source Auxiliary m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : ∀ view, Stable (encode view)) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Stable (RegistrationNativePlatformBeaconPublication.begin
      (fun query => RegistrationNativePlatformGenericBundle.liftLegacy implementation (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
      encode ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin) := by
  unfold Stable
  rw [RegistrationNativePlatformBeaconMap.begin close_hom]
  apply RegistrationNativePlatformBeaconPublicationStateView.begin project idem
  · intro query
    exact legacy_stable implementation _ (RegistrationNativeBeaconEnvBundle.outgoing_stable setup index owner query)
  · exact writer

/-- The original source bundle with its literal Ready writer ignores only the unrelated record-kind input ledger. -/
theorem bundle (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) m)
    (setup : Setup base KemSK)
    (encode : registration.InitView → M source Auxiliary m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : ∀ view, Stable (encode view)) (index : Nat) :
    Stable (RegistrationNativePlatformGenericBundle.bundle implementation setup source encode index) := by
  unfold RegistrationNativePlatformGenericBundle.bundle
  apply bind_stable _ _ get_stable
  intro owners
  cases found : owners[index]? with
  | none => exact pure_stable _
  | some owner =>
      cases phase : owner.phase with
      | fresh =>
        simp only [phase]
        apply bind_stable _ _ (legacy_stable implementation _ (RegistrationNativeBeaconEnvCallbacks.sample_stable _))
        intro oneTime
        apply bind_stable _ _ (publication implementation setup index owner encode writer oneTime)
        intro published
        cases published with
        | fail error | div => exact pure_stable _
        | ok result => cases result with
          | Err previous => exact pure_stable _
          | Ok finished =>
              apply bind_stable _ _ (legacy_stable implementation _ (RegistrationNativeBeaconEnvCallbacks.phase_stable index _))
              intro _
              apply bind_stable _ _ (legacy_stable implementation _ (RegistrationNativeBeaconEnvCallbacks.effect_stable _))
              intro _
              exact pure_stable _
      | freshWithCoins scalar =>
        simp only [phase]
        apply bind_stable _ _ (pure_stable scalar)
        intro oneTime
        apply bind_stable _ _ (publication implementation setup index owner encode writer oneTime)
        intro published
        cases published with
        | fail error | div => exact pure_stable _
        | ok result => cases result with
          | Err previous => exact pure_stable _
          | Ok finished =>
              apply bind_stable _ _ (legacy_stable implementation _ (RegistrationNativeBeaconEnvCallbacks.phase_stable index _))
              intro _
              apply bind_stable _ _ (legacy_stable implementation _ (RegistrationNativeBeaconEnvCallbacks.effect_stable _))
              intro _
              exact pure_stable _
      | initSent pending scalar | established completed | aborted aborted =>
        simp only [phase]
        exact pure_stable _

/-- The exact generated source/writer program has the same retained output for arbitrary initial owner and Env state after record-kind erasure. -/
theorem program (E : Type) (setup : Setup base KemSK) (index : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (before : EnvState Auxiliary) :
    Prod.map id erase <$> ((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run before =
      Prod.map id erase <$> ((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run (erase before) := by
  have stable := bundle (RegistrationNativePlatformGenericBundle.trustedLift (E := E) (n := n)) setup
    (RegistrationNativePlatformGenericBundle.encoder (source := source) (Auxiliary := Auxiliary) E) (fun _ => external_stable (source := source) (Auxiliary := Auxiliary) _) index
  have actual := congrArg (fun action => (fun result => ((result.1, result.2.1), result.2.2)) <$> action) (stable (owners, before))
  simpa only [close, RegistrationNativePlatformGenericBundle.program, StateT.run, Functor.map_map,
    Prod.map_def, id_eq, project] using actual
end BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleEnvMetricView.program
