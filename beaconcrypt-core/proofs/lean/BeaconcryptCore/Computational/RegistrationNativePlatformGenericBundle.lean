-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExternalWriter
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMap

/-! The native Beacon owner/environment program is lifted into an arbitrary common primitive/platform monad. Its actual legacy crypto requests, metadata and owner histories remain threaded through both StateT layers; the writer can then execute at Core Ready in that same stack. The joint free language uses the actual extracted writer request body, rather than a fixed encoder function. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK Auxiliary Value Next Encoded : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m]

abbrev M (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (m : Type → Type) (Value : Type) :=
  StateT (RegistrationNativeBeaconFrontend.State source) (StateT (EnvState Auxiliary) m) Value

def liftLegacy (implementation : QueryImpl (Trusted n KemSK) m)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : M source Auxiliary m Value :=
  fun owners environment => simulateQ implementation ((work.run owners).run environment)

theorem liftLegacy_id (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) :
    liftLegacy (QueryImpl.id' (Trusted n KemSK)) work = work := by
  funext owners environment
  exact simulateQ_id' ((work.run owners).run environment)

theorem liftLegacy_pure (implementation : QueryImpl (Trusted n KemSK) m) (value : Value) :
    liftLegacy implementation (pure value : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) =
      pure value := by
  funext owners environment
  rfl

def evaluate {κ : Type} {spec : OracleSpec.{0, 0} κ} (implementation : QueryImpl spec m)
    (work : M source Auxiliary (OracleComp spec) Value) : M source Auxiliary m Value :=
  fun owners environment => simulateQ implementation ((work.run owners).run environment)

private theorem evaluate_pure {κ : Type} {spec : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl spec m) (value : Value) :
    evaluate implementation (pure value : M source Auxiliary (OracleComp spec) Value) = pure value := by
  funext owners environment
  rfl

variable [LawfulMonad m]

private theorem evaluate_bind {κ : Type} {spec : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl spec m) (work : M source Auxiliary (OracleComp spec) Value)
    (next : Value → M source Auxiliary (OracleComp spec) Next) :
    evaluate implementation (work >>= next) =
      (evaluate implementation work >>= fun value => evaluate implementation (next value)) := by
  funext owners environment
  simp only [evaluate, StateT.run_bind, simulateQ_bind]
  rfl

private theorem evaluate_hom {κ : Type} {spec : OracleSpec.{0, 0} κ} (implementation : QueryImpl spec m) :
    Cslib.IsMonadHom (M source Auxiliary (OracleComp spec)) (M source Auxiliary m) (evaluate implementation) :=
  .mk' (evaluate_pure implementation) (evaluate_bind implementation)

theorem liftLegacy_bind (implementation : QueryImpl (Trusted n KemSK) m)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Next) :
    liftLegacy implementation (work >>= next) =
      (liftLegacy implementation work >>= fun value => liftLegacy implementation (next value)) := by
  funext owners environment
  simp only [liftLegacy, StateT.run_bind, simulateQ_bind]
  rfl

theorem liftLegacy_simulate {ι : Type} {spec : OracleSpec ι}
    (implementation : QueryImpl (Trusted n KemSK) m)
    (handler : QueryImpl spec (RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary))
    (work : OracleComp spec Value) :
    liftLegacy implementation (simulateQ handler work) =
      simulateQ (fun query => liftLegacy implementation (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, liftLegacy_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, liftLegacy_bind, ih]
omit [LawfulMonad m] in
noncomputable def bundle {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Trusted n KemSK) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (encode : registration.SignedInitView → M source Auxiliary m (RustM (core.option.Option Encoded)))
    (index : Nat) : M source Auxiliary m (RustM (Option Encoded)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner =>
    let selected : Option (Option PqxdhJointGapDh.ScalarBytes) := match owner.phase with
      | .fresh => some none
      | .freshWithCoins scalar => some (some scalar)
      | _ => none
    match selected with
    | none => pure (.ok none)
    | some supplied => do
      let oneTime ← match supplied with
        | some scalar => pure scalar
        | none => liftLegacy implementation (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (fun query => liftLegacy implementation (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        encode ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        liftLegacy implementation (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime))
        let _ ← liftLegacy implementation
          (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
        pure (.ok (some finished.encoded))

abbrev Spec (E : Type) (n : Nat) (KemSK : Type) := Trusted n KemSK +
  BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E

def trustedLift {E : Type} : QueryImpl (Trusted n KemSK) (OracleComp (Spec E n KemSK)) :=
  fun query => (Spec E n KemSK).query (.inl query)

def writerLift {E : Type} : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)
    (OracleComp (Spec E n KemSK)) := fun query => (Spec E n KemSK).query (.inr query)

omit [LawfulMonad m] in
def encoderWith {E : Type}
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.SignedInitView) :
    M source Auxiliary m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  StateT.lift (StateT.lift (simulateQ writer
    (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
      (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
      (RegistrationNativePlatformWriter.initPacket view)).run))

def encoder (E : Type) (view : registration.SignedInitView) :
    M source Auxiliary (OracleComp (Spec E n KemSK)) (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  encoderWith writerLift view

noncomputable def program {ι : Type} {base : OracleSpec ι} (E : Type) (setup : Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (index : Nat) :
    M source Auxiliary (OracleComp (Spec E n KemSK)) (RustM (Option (alloc.vec.Vec U8))) :=
  bundle trustedLift setup source (encoder E) index

private theorem evaluate_legacy {E : Type} (implementation : QueryImpl (Spec E n KemSK) m)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) :
    evaluate implementation (liftLegacy trustedLift work) =
      liftLegacy (fun query => implementation (.inl query)) work := by
  funext owners environment
  change simulateQ implementation (simulateQ trustedLift ((work.run owners).run environment)) = _
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler ((work.run owners).run environment))
  funext query
  exact simulateQ_spec_query implementation (.inl query)

private theorem base_writer {E : Type} (implementation : QueryImpl (Spec E n KemSK) m)
    (work : OracleComp (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) Value) :
    simulateQ implementation (simulateQ writerLift work) =
      simulateQ (fun query => implementation (.inr query)) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler work)
  funext query
  exact simulateQ_spec_query implementation (.inr query)

private theorem evaluate_encoder {E : Type} (implementation : QueryImpl (Spec E n KemSK) m)
    (view : registration.SignedInitView) :
    evaluate (source := source) (Auxiliary := Auxiliary) implementation (encoder E view) =
      encoderWith (fun query => implementation (.inr query)) view := by
  funext owners environment
  change simulateQ implementation (((encoder E view).run owners).run environment) =
    ((encoderWith (fun query => implementation (.inr query)) view).run owners).run environment
  simp only [encoder, encoderWith, StateT.run_lift, bind_pure_comp,
    StateT.run_map, Functor.map_map, simulateQ_map]
  rw [base_writer]

omit [LawfulMonad m] in
private theorem evaluate_get {κ : Type} {spec : OracleSpec.{0, 0} κ} (implementation : QueryImpl spec m) :
    evaluate implementation
      (get : M source Auxiliary (OracleComp spec) (RegistrationNativeBeaconFrontend.State source)) = get := by
  funext owners environment
  rfl

theorem bundle_id {ι : Type} {base : OracleSpec ι} (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (encode : registration.SignedInitView → RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary
      (RustM (core.option.Option Encoded))) (index : Nat) :
    bundle (QueryImpl.id' (Trusted n KemSK)) setup source encode index =
      RegistrationNativePlatformBundle.bundle setup source encode index := by
  unfold bundle RegistrationNativePlatformBundle.bundle
  simp_rw [liftLegacy_id]
  apply bind_congr
  intro owners
  cases owned : owners[index]? with
  | none => rfl
  | some owner =>
    cases phase : owner.phase <;> simp only [phase]
    all_goals
      apply bind_congr
      intro oneTime
      apply bind_congr
      intro published
      cases published with
      | fail error => rfl
      | div => rfl
      | ok result => cases result <;> rfl

/-- The entire native bundle, all its source crypto work and its literal extracted writer execute on one continuous common interpreter state. -/
theorem program_evaluate {E ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E n KemSK) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (index : Nat) :
    evaluate (Auxiliary := Auxiliary) implementation (program E setup source index) =
      bundle (fun query => implementation (.inl query)) setup source
        (encoderWith (fun query => implementation (.inr query))) index := by
  unfold program bundle
  rw [evaluate_bind, evaluate_get]
  apply bind_congr
  intro owners
  cases owned : owners[index]? with
  | none => exact evaluate_pure implementation _
  | some owner =>
    dsimp only
    cases owner.phase <;> simp only [evaluate_pure]
    all_goals
      rw [evaluate_bind]
      simp only [evaluate_legacy, evaluate_pure]
      apply bind_congr
      intro oneTime
      rw [evaluate_bind, RegistrationNativePlatformBeaconMap.begin (evaluate_hom implementation)]
      simp_rw [evaluate_legacy, evaluate_encoder]
      apply bind_congr
      intro published
      cases published with
      | fail error => exact evaluate_pure implementation _
      | div => exact evaluate_pure implementation _
      | ok result =>
        cases result with
        | Err previous => exact evaluate_pure implementation _
        | Ok finished => simp only [evaluate_bind, evaluate_legacy, evaluate_pure]

theorem program_bind {E ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl (Spec E n KemSK) m)
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (index : Nat)
    (next : RustM (Option (alloc.vec.Vec U8)) → M source Auxiliary (OracleComp (Spec E n KemSK)) Value) :
    evaluate implementation (do let output ← program E setup source index; next output) = (do
      let output ← bundle (fun query => implementation (.inl query)) setup source
        (encoderWith (fun query => implementation (.inr query))) index
      evaluate implementation (next output)) := by
  rw [evaluate_bind, program_evaluate]
end BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_id

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.liftLegacy_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.bundle_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.bundle_id

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.program_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.program_evaluate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.program_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle.program_bind
