-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountBundle

/-! Actual source Init publication and stateful encoding preserve both free count laws on the complete packed state. Primitive queries, optional replies, owner phases, caches and external allocation outcomes stay literal; only explicit private native accounting coordinates are projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeMldsaCountLower (localProject)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaCountRules (Correct)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)

private theorem native (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (stable : RegistrationNativeBeaconEnvView.Stable work) :
    Correct (source := source) (Platform := Platform) (localProject (n := n)) (RegistrationNativePlatformMldsaProgram.lift (source := source)
      (RegistrationNativePlatformBundleLower.native RegistrationNativePlatformMldsaProgram.coins setup checks representation created work)) :=
  RegistrationNativePlatformMldsaCountRules.native localProject (RegistrationNativeMldsaShared.lower setup checks representation created work)
    (RegistrationNativeMldsaCountLower.lower_stable setup checks representation created work stable)

/-- Every reached source Init leaf has both original and normalized free count equations, retaining arbitrary optional replies and true request operands. -/
theorem outgoing (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Correct (Platform := Platform) (localProject (n := n))
      (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index owner query) :=
  RegistrationNativePlatformMldsaCountRules.inject localProject _
    (RegistrationNativeMldsaCountBundle.outgoing setup checks representation created index owner query)

private theorem begin (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (publicKey : Std.Array U8 1952#usize) :
    Correct (localProject (n := n)) (RegistrationNativePlatformBeaconPublication.begin
      (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index owner)
      (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
        (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view)))
      control inputs coins pin publicKey) := by
  rw [← RegistrationNativePlatformMldsaBundleMap.begin_source]
  apply RegistrationNativePlatformMldsaCountRules.simulate localProject RegistrationNativeMldsaCountLower.idempotent
  intro query
  cases query with
  | inl query => exact outgoing setup checks representation created index owner query
  | inr query => exact RegistrationNativePlatformMldsaCountRules.external localProject RegistrationNativeMldsaCountLower.idempotent _

/-- The whole actual source bundle satisfies count normalization without replacing its stateful writer by a fixed wire function. -/
theorem bundle
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Correct (source := source) (localProject (n := n))
      (RegistrationNativePlatformMldsaBundle.bundle setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index) := by
  unfold RegistrationNativePlatformMldsaBundle.bundle
  apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
    (native setup checks representation created _ RegistrationNativeBeaconEnvView.get_stable)
  intro owners
  cases found : owners[index]? with
  | none => exact RegistrationNativePlatformMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
  | some owner =>
    have continuation (oneTime : PqxdhJointGapDh.ScalarBytes) :
        Correct (localProject (n := n)) (do
          let published ← RegistrationNativePlatformBeaconPublication.begin
            (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index owner)
            (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
              (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
                (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view)))
            ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
          match published with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.Err _) => pure (.ok none)
          | .ok (.Ok finished) => do
            RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
              RegistrationNativePlatformMldsaProgram.coins setup checks representation created
              (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)))
            let _ ← RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
              RegistrationNativePlatformMldsaProgram.coins setup checks representation created
              (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))))
            pure (.ok (some finished.encoded)) : StateT (Local n KemSK source) (M source Platform) (RustM (Option (alloc.vec.Vec U8)))) := by
      apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _ (begin setup checks representation created index owner writer _ _ _ _ _)
      intro published
      cases published with
      | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
      | ok answer => cases answer with
        | Err previous => exact RegistrationNativePlatformMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
        | Ok finished =>
          apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
            (native setup checks representation created _ (RegistrationNativeBeaconEnvCallbacks.phase_stable index _))
          intro _changed
          apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
            (native setup checks representation created _ (RegistrationNativeBeaconEnvCallbacks.effect_stable _))
          intro _advanced
          exact RegistrationNativePlatformMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
    cases phase : owner.phase <;> simp only [phase]
    all_goals first
      | exact RegistrationNativePlatformMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _
      | apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
          (native setup checks representation created _ (RegistrationNativeBeaconEnvCallbacks.sample_stable _))
        intro oneTime
        convert continuation oneTime using 1
      | apply RegistrationNativePlatformMldsaCountRules.bind localProject _ _
          (RegistrationNativePlatformMldsaCountRules.pure localProject RegistrationNativeMldsaCountLower.idempotent _)
        intro oneTime
        convert continuation oneTime using 1
    all_goals
      congr 1
      funext published
      cases published with
      | fail error => rfl
      | div => rfl
      | ok answer => cases answer <;> rfl


private def openState (before : RegistrationNativeExperiment.State n KemSK source) : Local n KemSK source :=
  (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))
private theorem open_project (before : RegistrationNativeExperiment.State n KemSK source) :
    localProject (openState before) = openState (RegistrationNativeMldsaMainView.project before) := rfl
private theorem close_project (before : Local n KemSK source) :
    RegistrationNativeMldsaShared.close (localProject before) =
      RegistrationNativeMldsaMainView.project (RegistrationNativeMldsaShared.close before) := rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private def closeResult
    (result : RustM (Option (alloc.vec.Vec U8)) × (Local n KemSK source × Platform)) :
    RustM (Option Pqxdh.Bytes) × (RegistrationNativeExperiment.State n KemSK source × Platform) :=
  ((do let optional ← result.1; .ok (optional.map TranscriptAuthParts.absSlice)),
    (RegistrationNativeMldsaShared.close result.2.1, result.2.2))

/-- The complete actual source bundle's Native/Env lens preserves both count equations and the literal public platform poststate. -/
theorem sourceBundle
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index) := by
  constructor
  · intro before
    have same := congrArg (fun computation => closeResult <$> computation)
      ((bundle (source := source) setup checks representation created writer index).1 (openState before.1, before.2))
    simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project,
      closeResult, close_project, open_project] at same
    simp only [RegistrationNativePlatformPackedState.pack, StateT.run, Functor.map_map, openState] at same
    simp only [RegistrationNativePlatformMldsaBundle.sourceBundle, RegistrationNativePlatformPackedState.pack,
      StateT.run, map_apply, Functor.map_map, Prod.map, id_eq,
      RegistrationNativePlatformMldsaCountRules.project]
    exact same
  · intro before
    have same := congrArg (fun computation => closeResult <$> computation)
      ((bundle (source := source) setup checks representation created writer index).2 (openState before.1, before.2))
    simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project,
      closeResult, close_project, open_project] at same
    simp only [RegistrationNativePlatformPackedState.pack, StateT.run, Functor.map_map, openState,
      RegistrationNativeMldsaCountMap.transform, simulateQ_map] at same
    simp only [RegistrationNativePlatformMldsaBundle.sourceBundle, RegistrationNativePlatformPackedState.pack,
      StateT.run, map_apply, RegistrationNativeMldsaCountMap.transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project]
    exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle.sourceBundle
