-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarWaiting
/-! Actual selected creation retains its original counted dummy draw and commutes with an early independent scalar in the complete shared-platform continuation. Prefix refusal keeps the target waiting; successful birth permanently passes its actual roster index. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform E Value X ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (do let value ← work; pure (value, before)) := rfl

private theorem beacon_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (value : X) (before : State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (pure value : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State X)).run before = pure (value, before) := by
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  rfl

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ordinary" => RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer


local notation "eager" => RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer


/-- Actual source creation keeps P fixed and retains the complete native constructor result and counted state. -/
theorem ordinary_create_run (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (previous : Platform) :
    (((ordinary (.inr (.create edPin mlPin keyId))).run before).run previous) =
      (fun result => (result, previous)) <$>
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before := by
  change (simulateQ RegistrationNativePlatformMldsaProgram.coins
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)).run previous = _
  rw [RegistrationNativePlatformMldsaProgram.lift_coins]
  simp only [StateT.run_lift, bind_pure_comp]

/-- Selected replacement changes only the constructor scalar, retaining the same complete P/native coordinates. -/
theorem eager_create_run (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (previous : Platform) :
    (((eager selected scalar (.inr (.create edPin mlPin keyId))).run before).run previous) =
      (fun result => (result, previous)) <$>
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before := by
  change (simulateQ RegistrationNativePlatformMldsaProgram.coins
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId)).run before)).run previous = _
  rw [RegistrationNativePlatformMldsaProgram.lift_coins]
  simp only [StateT.run_lift, bind_pure_comp]

/-- Literal optional-prefix source outcomes justify the adaptive scalar interchange with the complete external P retained. -/
theorem after_step (selected : Nat) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RustM (Option (RegistrationNativeBeaconFrontend.Prepared source)))
    (before : State n KemSK source) (previous : Platform) (chosen : before.beacons.length = selected)
    (next : RustM (Option Nat) → OracleComp TypedSpec Value)
    (waiting : ∀ reply (current : State n KemSK source) (platform : Platform), current.beacons.length ≤ selected →
      (((simulateQ ordinary (next reply)).run current).run platform) =ᵈ
        (do let scalar ← PqxdhJointGapDh.sampleScalar
            ((simulateQ (eager selected scalar) (next reply)).run current).run platform)) :
    (do let result ← (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeScalarBirth.after setup source edPin keyId
            (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar) prepared)).run before
        ((simulateQ ordinary (next result.1)).run result.2).run previous) =ᵈ
      (do let scalar ← PqxdhJointGapDh.sampleScalar
          let result ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeScalarBirth.after setup source edPin keyId (RegistrationNativeScalarEagerLocal.dummy scalar) prepared)).run before
          ((simulateQ (eager selected scalar) (next result.1)).run result.2).run previous) := by
  cases prepared with
  | fail error =>
    simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
    exact waiting (.fail error) before previous (by omega)
  | div =>
    simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
    exact waiting .div before previous (by omega)
  | ok preparedOption => cases preparedOption with
    | none =>
      simp only [RegistrationNativeScalarBirth.after, beacon_pure, pure_bind]
      exact waiting (.ok none) before previous (by omega)
    | some prepared =>
      simp only [RegistrationNativeScalarBirth.after, RegistrationNativeScalarEagerLocal.dummy, bind_assoc, pure_bind,
        RegistrationNativeScalarEagerLocal.sample_bind]
      have moved := RegistrationNativeScalarSource.scalar_eager setup checks representation created before
        (fun scalar current => do
          let result ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin prepared.credentials prepared.identity scalar)).run current
          ((simulateQ ordinary (next result.1)).run result.2).run previous)
      refine moved.trans ?_
      apply _root_.EvalDistEq.bind_right
      intro scalar
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro drawn drawnSupport
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro born bornSupport
      rw [RegistrationNativePlatformOrdinaryScalarWaiting.done_program setup checks wire route representation created credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected scalar (next born.1) born.2 previous
        (RegistrationNativeScalarWaiting.birth_done setup checks representation created selected edPin keyId prepared scalar before chosen
          drawn drawnSupport born bornSupport)]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep.ordinary_create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep.ordinary_create_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep.eager_create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep.eager_create_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep.after_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarStep.after_step
