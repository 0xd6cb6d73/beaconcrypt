-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Main Full interpret)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
def value : RegistrationNativePlatformIdentityBundle.Reply → RustM (Option (alloc.vec.Vec U8))
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok none
  | .ok (.Ok published) => .ok (some published.encoded)
def advance (index : Nat) (before : PqxdhRecordLiftWorld.State n) : Bool × PqxdhRecordLiftWorld.State n :=
  let charged := PqxdhRecordLiftWorld.chargeEffect (.inr (.advanceOwner index .initSent)) before
  match charged.owners[index]? with
  | some (.inactive phase) =>
    if PqxdhRecordLiftWorld.LegalAdvance phase .initSent then
      (true, {charged with owners := charged.owners.set index (.inactive .initSent)})
    else (false, charged)
  | _ => (false, charged)
private theorem advance_run (index : Nat) (before : PqxdhRecordLiftWorld.State n) :
    (PqxdhRecordLiftWorld.effects (.inr (.advanceOwner index .initSent))).run before = pure (advance index before) := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run, advance]
  split <;> simp_all only []
  all_goals split <;> simp_all only []
private theorem advance_apply (index : Nat) (before : PqxdhRecordLiftWorld.State n) :
    PqxdhRecordLiftWorld.effects (.inr (.advanceOwner index .initSent)) before = pure (advance index before) :=
  advance_run index before
def after (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RegistrationNativePlatformIdentityBundle.Reply) (before : Main (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  match reply with
  | .ok (.Ok published) =>
    let owners := match before.1.beacons[index]? with
      | none => before.1.beacons
      | some current => before.1.beacons.set index {current with phase := .initSent published.pending oneTime}
    ({before.1 with beacons := owners, context := {before.1.context with server := {before.1.context.server with
      world := {before.1.context.server.world with world :=
        ((advance owner.worldOwner before.1.context.server.world.world.1).2, before.1.context.server.world.world.2)}}}}, before.2)
  | _ => before
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (v : A) (before : S) :
    (pure v : StateT S m A) before = pure (v, before) := rfl
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun v => (v, before)) <$> work := bind_pure_comp _ _
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
variable (reply : RegistrationNativePlatformIdentityBundle.Reply)
local notation "action" => RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
  (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) (Platform := Platform) index owner oneTime reply)
/-- The literal terminal controller has no primitive query: it preserves failure results, or updates the actual owner phase and charged World owner slot before returning the published bytes. -/
theorem next_run (before : Main (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (action).run before = pure (value reply, after index owner oneTime reply before) := by
  cases reply with
  | fail error | div =>
    simp only [RegistrationNativePlatformIdentityBundle.next, RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source]
    rfl
  | ok result => cases result with
    | Err previous =>
      simp only [RegistrationNativePlatformIdentityBundle.next, RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source]
      rfl
    | Ok published =>
      rw [RegistrationNativePlatformIdentityCtxOutgoingFold.run]
      simp only [RegistrationNativePlatformIdentityBundle.next, RegistrationNativePlatformIdentityProgram.native,
        RegistrationNativeIdentityFrontend.updatePhase, RegistrationNativeIdentityFrontend.effect, StateT.run,
        bind_apply, pure_apply, lift_apply, modify_apply, map_apply,
        simulateQ_bind, simulateQ_pure, simulateQ_map, simulateQ_spec_query, pure_bind, bind_map_left, Functor.map_map]
      simp only [RegistrationNativePlatformIdentityProgram.nativeLift,
        RegistrationNativePlatformIdentityCtxCompiler.free, RegistrationNativePlatformIdentityCtxCompiler.implementation,
        RegistrationNativePlatformIdentityCtxAmbient.program, RegistrationNativePlatformIdentityCtxAmbient.world,
        RegistrationNativePlatformCtxEffects.program, simulateQ_spec_query, StateT.run,
        advance_apply, simulateQ_pure, map_pure, pure_bind]
      rfl

/-- Real and censored source interpretations retain the entire actual Main transition and return exactly the controller result, with complete Mode/private-source/P retention. -/
theorem source (selected : Nat) (placeholder : Ed25519Signature) (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    (interpret setup.joint selected placeholder censored action).run before =
      pure (value reply, ((after index owner oneTime reply before.1.1, before.1.2), before.2)) := by
  change (do
    let result ← (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder
        else RegistrationNativeIdentityCensorSource.implementation setup.joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
        ((action).run before.1.1)).run before.1.2)).run before.2
    pure (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) = _
  rw [next_run setup checks representation created index owner oneTime reply before.1.1]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
/-- Every supported terminal outcome preserves the original complete Mode, private generated/hash source state and P; successful publication does not require a legal World row. -/
theorem frame (selected : Nat) (placeholder : Ed25519Signature) (censored : Bool)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (result : RustM (Option (alloc.vec.Vec U8)) × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret setup.joint selected placeholder censored action).run before)) :
    result.1 = value reply ∧ result.2.1.2 = before.1.2 ∧ result.2.2 = before.2 ∧ result.2.1.1.2 = before.1.1.2 := by
  rw [source setup checks representation created index owner oneTime reply selected placeholder censored before] at supported
  simp only [support_pure, Set.mem_singleton_iff] at supported
  subst result
  refine ⟨rfl, rfl, rfl, ?_⟩
  cases reply with
  | fail error | div => rfl
  | ok result => cases result <;> rfl
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal.next_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal.next_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleTerminal.frame
