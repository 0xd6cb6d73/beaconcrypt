-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret

/-! The original side of the effectful generated-Ed bundle correspondence is the literal generic source bundle controller. The same serializer request interpreter and platform state occur in both programs; there is no fixed wire encoder or successful-allocation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformIdentityProgram (Original OriginalSpec original externalOriginal originalLift externalOriginalLift)
variable {n : Nat} {ι KemSK Auxiliary Platform E Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Base (n : Nat) (KemSK Platform : Type) := StateT Platform (OracleComp (OriginalSpec n KemSK))

def trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (Base n KemSK Platform) :=
  fun query => StateT.lift ((originalLift (n := n) (KemSK := KemSK)) query)

def writerProgram (work : StateT Platform ProbComp Value) : Base n KemSK Platform Value :=
  fun before => simulateQ (externalOriginalLift (n := n) (KemSK := KemSK)) (work.run before)

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem trusted_program (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (platform : Platform) :
    (simulateQ trusted work).run platform =
      (fun value => (value, platform)) <$> simulateQ originalLift work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, trusted, StateT.run_lift,
      bind_pure_comp, bind_map_left, ih, map_bind]

/-- The source's original native leaf lifting is the generic bundle's actual trusted lifting. -/
theorem original_native (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) :
    original (Platform := Platform) work = RegistrationNativePlatformGenericBundle.liftLegacy trusted work := by
  funext owners env platform
  exact (trusted_program ((work.run owners).run env) platform).symm

private theorem external_pure (value : Value) :
    externalOriginal (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
      (pure value : StateT Platform ProbComp Value) = pure value := by
  funext owners env platform
  simp only [externalOriginal, pure_apply, StateT.run_pure, simulateQ_pure, map_pure]

private theorem external_bind (work : StateT Platform ProbComp Value) (next : Value → StateT Platform ProbComp Next) :
    externalOriginal (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (work >>= next) =
      (externalOriginal work >>= fun value => externalOriginal (next value)) := by
  funext owners env platform
  simp only [externalOriginal, bind_apply, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

private theorem external_simulate {κ : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec (StateT Platform ProbComp)) (work : OracleComp spec Value) :
    externalOriginal (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (simulateQ implementation work) =
      simulateQ (fun query => externalOriginal (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, external_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, external_bind, ih]

private theorem external_lift (work : StateT Platform ProbComp Value) :
    externalOriginal (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work =
      StateT.lift (StateT.lift (writerProgram work)) := by
  funext owners env platform
  simp only [externalOriginal, lift_apply, map_apply, writerProgram, Functor.map_map, Prod.map, id_eq]

/-- The actual six-field writer requests have the same complete P execution inside the generic owner/Env stack. -/
theorem writer_source (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedInitView) :
    simulateQ (fun query => externalOriginal (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (writer query))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run =
      RegistrationNativePlatformGenericBundle.encoderWith (fun query => writerProgram (writer query)) view := by
  rw [← external_simulate, external_lift]
  unfold RegistrationNativePlatformGenericBundle.encoderWith
  congr 2
  funext platform
  exact congrFun (RegistrationNativePlatformInterpret.state_simulate externalOriginalLift writer
    (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
      (RegistrationNativePlatformWriter.initPacket view)).run) platform

private theorem selected_source (setup : Setup base KemSK) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformIdentityBundle.originalBundled (n := n) (Auxiliary := Auxiliary) setup index owner scalar writer = (do
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy trusted
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoderWith (fun query => writerProgram (writer query)))
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        RegistrationNativePlatformGenericBundle.liftLegacy trusted
          (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending scalar))
        let _ ← RegistrationNativePlatformGenericBundle.liftLegacy trusted
          (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
        pure (.ok (some finished.encoded))) := by
  unfold RegistrationNativePlatformIdentityBundle.originalBundled
  rw [RegistrationNativePlatformWriter.begin_interpret]
  simp only [RegistrationNativePlatformIdentityPublication.originalCallback, original_native]
  rw [show (fun view => simulateQ (fun request => externalOriginal (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (writer request))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run) =
      RegistrationNativePlatformGenericBundle.encoderWith (fun query => writerProgram (writer query)) from funext (writer_source writer)]
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div => rfl
  | ok reply => cases reply with
    | Err error => rfl
    | Ok published => simp only [RegistrationNativePlatformIdentityBundle.originalNext, original_native]

/-- The effectful original bundle is exactly the source generic controller, with its actual optional writer and lifecycle suffix. -/
theorem bundle_source (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformIdentityBundleRun.originalBundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer =
      RegistrationNativePlatformGenericBundle.bundle trusted setup source
        (RegistrationNativePlatformGenericBundle.encoderWith (fun query => writerProgram (writer query))) index := by
  unfold RegistrationNativePlatformIdentityBundleRun.originalBundle RegistrationNativePlatformGenericBundle.bundle
  apply bind_congr
  intro owners
  cases selected : owners[index]? with
  | none => rfl
  | some owner =>
    unfold RegistrationNativePlatformIdentityBundleRun.originalStart
    cases phase : owner.phase with
    | fresh =>
      simp only [phase, original_native]
      apply bind_congr
      intro scalar
      rw [selected_source (n := n) (Auxiliary := Auxiliary) setup index owner scalar writer]
      apply bind_congr
      intro reply
      cases reply with
      | fail error | div => rfl
      | ok result => cases result <;> rfl
    | freshWithCoins scalar =>
      simp only [phase, pure_bind]
      rw [selected_source (n := n) (Auxiliary := Auxiliary) setup index owner scalar writer]
      apply bind_congr
      intro reply
      cases reply with
      | fail error | div => rfl
      | ok result => cases result <;> rfl
    | initSent pending scalar | established completed | aborted previous => simp only [phase]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle.original_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle.original_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle.writer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle.writer_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginalBundle.bundle_source
