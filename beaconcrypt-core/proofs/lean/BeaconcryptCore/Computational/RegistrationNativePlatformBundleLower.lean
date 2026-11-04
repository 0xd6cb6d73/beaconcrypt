-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-! The actual stateful Beacon bundle is reassociated into one private native Local state while retaining its separate platform monad. Its actual source writer stays at Core Ready. This exposes the outgoing ML leaf to the existing capability language without replacing failed writers by a static wire function. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local)
variable {n : Nat} {KemSK Value Next Encoded ι : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source} {m : Type → Type} [Monad m]

abbrev Front (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (m : Type → Type) :=
  RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
    (RegistrationNativePlatformExperiment.M n KemSK source m)

def lower (work : Front n KemSK source m Value) : StateT (Local n KemSK source) m Value := fun before =>
  (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$>
    (((work.run before.1).run before.2.1).run before.2.2)

variable [LawfulMonad m]
private theorem lower_pure (value : Value) :
    lower (pure value : Front n KemSK source m Value) = pure value := by
  funext before
  simp only [lower, StateT.run_pure, map_pure]
  rfl

private theorem lower_bind (work : Front n KemSK source m Value)
    (next : Value → Front n KemSK source m Next) :
    lower (work >>= next) = (lower work >>= fun value => lower (next value)) := by
  funext before
  simp only [lower, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

private theorem lower_hom : Cslib.IsMonadHom
    (Front n KemSK source m) (StateT (Local n KemSK source) m) lower := .mk' lower_pure lower_bind

noncomputable def native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    StateT (Local n KemSK source) m Value := fun before =>
  simulateQ coins ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before)

private theorem legacy (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    lower (RegistrationNativePlatformGenericBundle.liftLegacy
      (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source) work) =
      native coins setup checks representation created work := by
  funext before
  have law := congrFun (RegistrationNativePlatformInterpret.state_simulate coins
    (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((work.run before.1).run before.2.1)) before.2.2
  change simulateQ coins ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((work.run before.1).run before.2.1)).run before.2.2) =
    (simulateQ (fun query => RegistrationNativePlatformInterpret.state coins
      (RegistrationNativeExperiment.trusted setup checks representation created source query))
      ((work.run before.1).run before.2.1)).run before.2.2 at law
  change (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$>
    (simulateQ (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source)
      ((work.run before.1).run before.2.1)).run before.2.2 = _
  have handlers : (fun query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain => RegistrationNativePlatformInterpret.state coins
      (RegistrationNativeExperiment.trusted (n := n) setup checks representation created source query)) =
      RegistrationNativePlatformExperiment.trusted (n := n) coins setup checks representation created source := rfl
  rw [handlers] at law
  rw [← law]
  simp only [native, RegistrationNativeMldsaShared.lower, StateT.run, simulateQ_map]

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem owners (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    lower (get : Front n KemSK source m (RegistrationNativeBeaconFrontend.State source)) =
      native coins setup checks representation created get := by
  funext before
  simp only [lower, native, RegistrationNativeMldsaShared.lower, StateT.run, state_get_apply,
    state_pure_apply, simulateQ_pure, map_pure]

noncomputable def bundle (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (encode : registration.SignedInitView → Front n KemSK source m (RustM (Option Encoded)))
    (index : Nat) : StateT (Local n KemSK source) m (RustM (Option Encoded)) := do
  let owners ← native coins setup checks representation created get
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
        | none =>
            native coins setup checks representation created
              (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (fun query => native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (fun view => lower (encode view)) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime))
        let _ ← native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
        pure (.ok (some finished.encoded))

/-- Actual source bundle control, including failed stateful encoding, lowers to its literal owner/environment/native state. -/
theorem bundle_source (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (encode : registration.SignedInitView → Front n KemSK source m (RustM (Option Encoded)))
    (index : Nat) :
    lower (RegistrationNativePlatformGenericBundle.bundle
      (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source)
      setup source encode index) = bundle coins setup checks representation created encode index := by
  unfold RegistrationNativePlatformGenericBundle.bundle bundle
  rw [lower_bind, owners]
  apply bind_congr
  intro owners
  cases found : owners[index]? with
  | none => exact lower_pure _
  | some owner =>
      cases phase : owner.phase <;> simp only [phase]
      all_goals try exact lower_pure _
      all_goals
        rw [lower_bind]
        simp only [legacy, lower_pure]
        apply bind_congr
        intro oneTime
        rw [lower_bind, RegistrationNativePlatformBeaconMap.begin lower_hom]
        simp_rw [legacy]
        apply bind_congr
        intro published
        cases published with
        | fail error | div => exact lower_pure _
        | ok answer => cases answer with
          | Err prior => exact lower_pure _
          | Ok finished => simp only [lower_bind, legacy, lower_pure]

noncomputable def sourceBundle (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    {E : Type} (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) (index : Nat) :
    RegistrationNativePlatformExperiment.M n KemSK source m (RustM (Option Pqxdh.Bytes)) := fun before =>
  (fun result : RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source => ((do let optional ← result.1; .ok (optional.map TranscriptAuthParts.absSlice)),
    RegistrationNativeMldsaShared.close result.2)) <$>
      (bundle coins setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))

/-- The complete actual source bundle, including its actual stateful writer, equals the reassociated local program. -/
theorem sourceBundle_actual (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    {E : Type} (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) (index : Nat) :
    sourceBundle (n := n) (source := source) coins setup checks representation created writer index =
      RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index := by
  let encoder : registration.SignedInitView → Front n KemSK source m (RustM (Option (alloc.vec.Vec U8))) :=
    RegistrationNativePlatformGenericBundle.encoderWith
    (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)
  have localLaw := bundle_source coins setup checks representation created encoder index
  have programLaw : RegistrationNativePlatformGenericBundle.evaluate
      (RegistrationNativePlatformExperiment.bundleHandler (n := n) coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.program E setup source index) =
      RegistrationNativePlatformGenericBundle.bundle
        (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source) setup source encoder index :=
    RegistrationNativePlatformGenericBundle.program_evaluate _ setup source index
  funext before
  have execution := congrFun (congrFun (congrFun programLaw before.beacons)
    (RegistrationWorldAgreementCompiler.erase before.server.world)) before
  simp only [RegistrationNativePlatformGenericBundle.evaluate, StateT.run] at execution
  change (fun result : RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source => ((do let optional ← result.1; .ok (optional.map TranscriptAuthParts.absSlice)),
    RegistrationNativeMldsaShared.close result.2)) <$>
      (bundle coins setup checks representation created encoder index).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) = _
  rw [← localLaw]
  simp only [lower, StateT.run, Functor.map_map, RegistrationNativePlatformExperiment.bundle]
  rw [execution, bind_pure_comp]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower.bundle_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower.sourceBundle_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower.sourceBundle_actual
