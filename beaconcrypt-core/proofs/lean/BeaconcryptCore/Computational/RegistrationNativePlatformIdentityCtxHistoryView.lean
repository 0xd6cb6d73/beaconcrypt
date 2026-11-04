-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
/-! The actual Main source does not depend on prior raw Ed signature slots. The input view replaces those prior slots; the final observation masks all stored slots, including newly appended entries. Signed messages and order remain, while full Context/P, current replies, physical queries and all reached counters are retained. The source frontend's checked history law is closed through the literal indexed physical compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxMain (M)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def view (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  ({before.1 with beacons := RegistrationNativeIdentityHistoryView.owners placeholder before.1.beacons}, before.2)
def Stable (placeholder : Ed25519Signature) (work : M n KemSK Platform source A) : Prop :=
  RegistrationNativePlatformViewStable.Stable (view placeholder) work

private def close (result : (A × RegistrationNativePlatformIdentityHistoryView.Packed
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) (Platform := Platform)) × RegistrationNativeIdentityWorld.Context n KemSK) :
    A × (RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  (result.1.1, ({
    context := {result.2 with server := {result.2.server with
      world := RegistrationWorldAgreementCompiler.join result.1.2.1.2 result.2.server.world.world.1}}
    beacons := result.1.2.1.1 }, result.1.2.2))
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- Closing actual owner/Env/Main/P state preserves the checked source history law and every physical request. -/
theorem beacon (placeholder : Ed25519Signature) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (law : RegistrationNativePlatformIdentityHistoryView.Stable placeholder work) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work) := by
  intro before
  have transported := congrArg (fun script => close <$>
    (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) script).run before.1.context)
    (law ((before.1.beacons, RegistrationWorldAgreementCompiler.erase before.1.context.server.world), before.2))
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon, RegistrationNativePlatformIdentityCtxCompiler.beacon,
    RegistrationNativePlatformIdentityHistoryView.pack, RegistrationNativePlatformIdentityHistoryView.view,
    StateT.run, simulateQ_map, state_map_apply, Functor.map_map, view, close, Prod.map_def, id_eq] at transported ⊢
  exact transported

/-- Replacing prior signature slots twice retains the same signed-message chronology. -/
theorem view_idempotent (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    view placeholder (view placeholder before) = view placeholder before := by
  simp only [view, RegistrationNativeIdentityHistoryLifecycle.owners_idempotent]

/-- Actual generated-owner creation ignores only the earlier raw signature slots. -/
theorem create_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxLifecycle.create (n := n) (source := source) (Platform := Platform)
      setup edPin mlPin keyId checks representation created) :=
  beacon placeholder setup checks representation created _
    (RegistrationNativePlatformIdentityHistoryView.native placeholder _
      (RegistrationNativeIdentityHistoryLifecycle.create_stable placeholder setup edPin mlPin keyId))

/-- The entire corrected assigned-ID finish keeps full state after earlier signature-slot replacement. -/
theorem finish_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxLifecycle.finish (n := n) (source := source) (Platform := Platform)
      setup checks representation created wire index packet) :=
  beacon placeholder setup checks representation created _
    (RegistrationNativePlatformIdentityHistoryView.native placeholder _
      (RegistrationNativeIdentityHistoryLifecycle.finish_stable placeholder setup wire index packet))

/-- Full dynamic writer bundle behavior ignores earlier signature slots while keeping all current signature bytes and P effects. -/
theorem bundle_stable {E : Type} (placeholder : Ed25519Signature) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxLifecycle.bundle (n := n) (source := source) setup checks representation created writer index) := by
  apply RegistrationNativePlatformViewStable.map_stable (view placeholder) (view_idempotent placeholder)
  exact beacon placeholder setup checks representation created _
    (RegistrationNativePlatformIdentityHistoryBundle.bundle placeholder setup index writer)

/-- Actual ordinary Context work retains its complete P and backend while the unused private owner-history view changes. -/
theorem ordinary (placeholder : Ed25519Signature) (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxOrdinary.ordinary (source := source) work) := by
  intro before
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.ordinary, RegistrationNativePlatformIdentityCtxCompiler.ordinary,
    StateT.run, Functor.map_map, view, Prod.map_def, id_eq, RegistrationNativeIdentityHistoryLifecycle.owners_idempotent]
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.view_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.create_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.create_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.finish_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.finish_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.bundle_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.bundle_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView.ordinary
