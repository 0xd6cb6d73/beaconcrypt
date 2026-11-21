-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram

/-! Current Beacon Init has no ML capability leaf: the complete source controller is lifted as ordinary native work. All other native bodies remain their original complete source programs; the original mutable owner and environment states are threaded through every continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaBundle
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaProgram (Spec liftState evalState evaluate call)
open RegistrationNativeMldsaShared (Local lower close)
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (state : S) : (modify change : StateT S m Unit) state = pure ((), change state) := rfl

private theorem lower_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    lower (n := n) (source := source) setup checks representation created (pure value) = pure value := by
  funext before
  simp only [lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next) :
    lower setup checks representation created (work >>= next) =
      (lower setup checks representation created work >>= fun value => lower setup checks representation created (next value)) := by
  funext before
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

private theorem lower_sample (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (draw : ProbComp Value) (before : Local n KemSK source) :
    (lower setup checks representation created (RegistrationNativeBeaconFrontend.sample draw)).run before =
      (fun result => (result.1, (before.1, (before.2.1,
        RegistrationBeaconReferenceNativeEffects.embed before.2.2 result.2)))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin draw)).run
          before.2.2.server.world.world.1 := by
  rw [RegistrationNativeScalarSource.sample_effects]
  have restriction : RegistrationNativeExperiment.trusted (n := n) setup checks representation created source ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created := by
    funext selected
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, RegistrationBeaconReferenceNativeEffects.native]
  simp only [lower, StateT.run, state_lift_apply, state_map_apply, simulateQ_map, Functor.map_map,
    Prod.map, id_eq]
  rw [← QueryImpl.simulateQ_compose, restriction]
  have closed := RegistrationBeaconReferenceNativeEffects.program setup checks representation created
    (simulateQ RegistrationWorldCoinCompiler.envCoin draw) before.2.2
  simp only [StateT.run] at closed
  rw [closed]
  simp only [Functor.map_map, Prod.map, id_eq]

noncomputable def native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    StateT (Local n KemSK source) (OracleComp (Spec source)) Value :=
  liftState (lower setup checks representation created work)

private theorem eval_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    evalState (native setup checks representation created work) = lower setup checks representation created work :=
  RegistrationNativeMldsaProgram.eval_liftState _

noncomputable def outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (Local n KemSK source) (OracleComp (Spec source)))
  | query => native setup checks representation created
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)

/-- Actual evaluation of the named Init signing leaf retains all native poststate and chronological history. -/
theorem eval_outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    evalState (outgoing (n := n) setup checks representation created index owner query) =
      lower setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query) := by
  exact eval_native setup checks representation created _

private theorem lower_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    lower (n := n) setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner) work) =
      simulateQ (fun query => lower setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- The entire adaptive Init controller evaluates to the original native body on its same mutable local state. -/
theorem eval_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    evalState (simulateQ (outgoing (n := n) setup checks representation created index owner) work) =
      lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner) work) := by
  rw [RegistrationNativeMldsaProgram.eval_simulate, lower_program]
  congr 1
  funext query
  exact eval_outgoing setup checks representation created index owner query

noncomputable def afterPublished (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    StateT (Local n KemSK source) (OracleComp (Spec source)) (RustM (Option Pqxdh.Bytes)) :=
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      native setup checks representation created
        (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime))
      let _ ← native setup checks representation created
        (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
      pure (.ok (some finished.encoded))

private theorem eval_afterPublished (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result Pqxdh.Bytes)) :
    evalState (afterPublished (n := n) setup checks representation created index owner oneTime published) =
      lower setup checks representation created
        (match published with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok (.Err _) => pure (.ok none)
        | .ok (.Ok finished) => do
          RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)
          let _ ← RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent))
          pure (.ok (some finished.encoded))) := by
  cases published with
  | fail error | div => simp only [afterPublished, RegistrationNativeMldsaProgram.eval_pure, lower_pure]
  | ok outcome => cases outcome <;>
      simp only [afterPublished, RegistrationNativeMldsaProgram.eval_bind, RegistrationNativeMldsaProgram.eval_pure,
        eval_native, lower_bind, lower_pure]

noncomputable def bundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) :
    StateT (Local n KemSK source) (OracleComp (Spec source)) (RustM (Option Pqxdh.Bytes)) := do
  let owners ← native setup checks representation created get
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
            native setup checks representation created
              (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)
      let published ← simulateQ (outgoing setup checks representation created index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩
          (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
      afterPublished setup checks representation created index owner oneTime published

/-- Full bundle evaluation retains the original phase selection, fresh randomness, optional publication and every reached native effect. -/
theorem eval_bundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) :
    evalState (bundle (n := n) (source := source) setup checks wire representation created index) =
      lower setup checks representation created (RegistrationNativeBeaconFrontend.bundle setup source wire index) := by
  unfold bundle RegistrationNativeBeaconFrontend.bundle
  simp only [RegistrationNativeMldsaProgram.eval_bind, eval_native, lower_bind]
  congr 1
  funext owners
  cases found : owners[index]? with
  | none => simp only [RegistrationNativeMldsaProgram.eval_pure, lower_pure]
  | some owner =>
      cases phase : owner.phase <;>
        simp only [phase, RegistrationNativeMldsaProgram.eval_bind, RegistrationNativeMldsaProgram.eval_pure,
          eval_native, eval_program, eval_afterPublished, lower_bind, lower_pure]
      all_goals rfl

noncomputable def sourceBundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) :
    StateT (RegistrationNativeExperiment.State n KemSK source) (OracleComp (Spec source)) (RustM (Option Pqxdh.Bytes)) :=
  fun before => Prod.map id close <$> (bundle setup checks wire representation created index).run
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))

/-- The original native source wrapper is the actual interpretation of the named ML bundle capability program. -/
theorem eval_sourceBundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) :
    evalState (sourceBundle (n := n) (source := source) setup checks wire representation created index) =
      RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.bundle setup source wire index) := by
  funext before
  have localLaw := congrFun (eval_bundle setup checks wire representation created index)
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before))
  simp only [evalState, StateT.run, evaluate] at localLaw
  simp only [sourceBundle, evalState, StateT.run, evaluate, simulateQ_map]
  rw [localLaw]
  simp only [lower, RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, close]


end BeaconcryptCore.Computational.RegistrationNativeMldsaBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBundle.eval_sourceBundle
