-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleLower
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-! The actual stateful source Init bundle reifies its ML leaf inside the same mutable owner/environment/native state and external allocator state. Encoding remains the actual source callback at Core Ready, including failure and divergence. Evaluation preserves full native state, every signing receipt and the real external poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local)
open RegistrationNativePlatformMldsaProgram (M evaluate lift inject coins)
variable {n : Nat} {KemSK Platform Encoded ι : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

noncomputable def outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    StateT (Local n KemSK source) (M source Platform) (RegistrationBeaconInitExecutor.Spec.Range query) :=
  inject (RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query)

private theorem evaluate_outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    evaluate (outgoing (n := n) (Platform := Platform) setup checks representation created index owner query) =
      RegistrationNativePlatformBundleLower.native coins setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query) := by
  rw [outgoing, RegistrationNativePlatformMldsaProgram.evaluate_inject,
    RegistrationNativeMldsaBundle.eval_outgoing]
  funext before
  exact (RegistrationNativePlatformMldsaProgram.lift_coins
    ((RegistrationNativeMldsaShared.lower setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)).run before)).symm

noncomputable def bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (encode : registration.InitView → RegistrationNativePlatformBundleLower.Front n KemSK source
      (StateT Platform ProbComp) (RustM (Option Encoded))) (index : Nat) :
    StateT (Local n KemSK source) (M source Platform) (RustM (Option Encoded)) := do
  let owners ← lift (RegistrationNativePlatformBundleLower.native coins setup checks representation created get)
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
        | none => lift (RegistrationNativePlatformBundleLower.native coins setup checks representation created
            (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (outgoing setup checks representation created index owner)
        (fun view => lift (RegistrationNativePlatformBundleLower.lower (encode view)))
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        lift (RegistrationNativePlatformBundleLower.native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)))
        let _ ← lift (RegistrationNativePlatformBundleLower.native coins setup checks representation created
          (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))))
        pure (.ok (some finished.encoded))

/-- All source bundle phases and every stateful writer outcome evaluate to the actual source local program. -/
theorem evaluate_bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (encode : registration.InitView → RegistrationNativePlatformBundleLower.Front n KemSK source
      (StateT Platform ProbComp) (RustM (Option Encoded))) (index : Nat) :
    evaluate (bundle setup checks representation created encode index) =
      RegistrationNativePlatformBundleLower.bundle coins setup checks representation created encode index := by
  unfold bundle RegistrationNativePlatformBundleLower.bundle
  rw [RegistrationNativePlatformMldsaProgram.evaluate_bind, RegistrationNativePlatformMldsaProgram.evaluate_lift]
  apply bind_congr
  intro owners
  cases found : owners[index]? with
  | none => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
  | some owner =>
      cases phase : owner.phase <;> simp only [phase]
      all_goals try exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
      all_goals
        rw [RegistrationNativePlatformMldsaProgram.evaluate_bind]
        simp only [RegistrationNativePlatformMldsaProgram.evaluate_pure,
          RegistrationNativePlatformMldsaProgram.evaluate_lift]
        apply bind_congr
        intro oneTime
        rw [RegistrationNativePlatformMldsaProgram.evaluate_bind,
          RegistrationNativePlatformBeaconMap.begin RegistrationNativePlatformMldsaProgram.evaluate_hom]
        simp only [evaluate_outgoing, RegistrationNativePlatformMldsaProgram.evaluate_lift]
        apply bind_congr
        intro published
        cases published with
        | fail error | div => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
        | ok answer => cases answer with
          | Err prior => exact RegistrationNativePlatformMldsaProgram.evaluate_pure _
          | Ok finished => simp only [RegistrationNativePlatformMldsaProgram.evaluate_bind,
              RegistrationNativePlatformMldsaProgram.evaluate_lift, RegistrationNativePlatformMldsaProgram.evaluate_pure]

noncomputable def sourceBundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    {E : Type} (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    StateT (RegistrationNativeExperiment.State n KemSK source) (M source Platform) (RustM (Option Pqxdh.Bytes)) := fun before =>
  (fun result : RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source =>
    ((do let optional ← result.1; .ok (optional.map TranscriptAuthParts.absSlice)),
      RegistrationNativeMldsaShared.close result.2)) <$>
    (bundle setup checks representation created
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index).run
      (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))

/-- Exact capability evaluation of the complete actual source bundle preserves private native state and real allocator poststate. -/
theorem evaluate_sourceBundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    {E : Type} (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    evaluate (sourceBundle (n := n) (source := source) setup checks representation created writer index) =
      RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index := by
  rw [← RegistrationNativePlatformBundleLower.sourceBundle_actual]
  funext before previous
  have localLaw := congrFun (congrFun (evaluate_bundle setup checks representation created
    (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
      (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index)
      (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))) previous
  simp only [evaluate, RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate,
    StateT.run] at localLaw
  simp only [sourceBundle, RegistrationNativePlatformBundleLower.sourceBundle, evaluate,
    RegistrationNativeMldsaProgram.evalState, RegistrationNativeMldsaProgram.evaluate, StateT.run]
  simp only [state_map_apply, simulateQ_map]
  rw [localLaw]

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle.evaluate_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle.evaluate_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle.evaluate_sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle.evaluate_sourceBundle
