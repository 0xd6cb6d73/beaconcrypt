-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompilerReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOrdinary
/-! Compact frontend ML receipts join to the exact prior Local raw-receipt view in Main. The actual source compiler preserves all private KEM, physical hash, owner and external state while that unused prior log is cleared. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxMain (M)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def view (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  ({before.1 with context := RegistrationNativePlatformCtxBuildReceiptView.context before.1.context}, before.2)
def Stable (work : M n KemSK Platform source A) : Prop := RegistrationNativePlatformViewStable.Stable view work
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


private def observe (result : (A × RegistrationNativePlatformIdentityHistoryView.Packed
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) (Platform := Platform)) × RegistrationNativeIdentityWorld.Context n KemSK) :=
  Prod.map id view (close result)

/-- The actual frontend compact receipt law closes through physical compilation and the full Main state. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (law : RegistrationNativeIdentityEnvReceiptView.PlatformStable work) :
    Stable (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work) := by
  intro before
  have transported := congrArg (fun script => observe <$>
    (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) script).run before.1.context)
    (law ((before.1.beacons, RegistrationWorldAgreementCompiler.erase before.1.context.server.world), before.2))
  have framed := congrArg (fun distribution => observe <$> distribution)
    (RegistrationNativePlatformIdentityCtxCompilerReceiptFrame.program (source := source) setup checks representation created
      ((RegistrationNativePlatformIdentityHistoryView.pack work).run
        ((before.1.beacons, {RegistrationWorldAgreementCompiler.erase before.1.context.server.world with receipts := []}), before.2)) before.1.context)
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, RegistrationNativeIdentityEnvReceiptView.platformView,
    RegistrationNativeIdentityEnvReceiptView.view,
    StateT.run, simulateQ_map, state_map_apply, Functor.map_map, observe, close, view,
    RegistrationNativePlatformCtxBuildReceiptView.context, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq] at transported framed
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon, RegistrationNativePlatformIdentityCtxCompiler.beacon,
    StateT.run, Functor.map_map, view,
    RegistrationNativePlatformCtxBuildReceiptView.context, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]
  exact transported.trans framed

/-- Clearing only the prior raw ML receipt coordinate is idempotent. -/
theorem view_idempotent (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) : view (view before) = view before := rfl

/-- Actual generated owner creation is independent of earlier compact/raw ML receipts. -/
theorem create_stable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Stable (RegistrationNativePlatformIdentityCtxLifecycle.create (n := n) (source := source) (Platform := Platform)
      setup edPin mlPin keyId checks representation created) :=
  beacon setup checks representation created _
    (RegistrationNativeIdentityEnvReceiptView.platform_native _
      (RegistrationNativeIdentityEnvReceiptLifecycle.create setup edPin mlPin keyId))

/-- Actual corrected finish retains every source/P outcome under the prior raw ML receipt view. -/
theorem finish_stable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Stable (RegistrationNativePlatformIdentityCtxLifecycle.finish (n := n) (source := source) (Platform := Platform)
      setup checks representation created wire index packet) :=
  beacon setup checks representation created _
    (RegistrationNativeIdentityEnvReceiptView.platform_native _
      (RegistrationNativeIdentityEnvReceiptLifecycle.finish setup wire index packet))

/-- Whole dynamic writer bundle execution retains exact current signature bytes and P, ignoring only prior raw ML receipts. -/
theorem bundle_stable {E : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Stable (RegistrationNativePlatformIdentityCtxLifecycle.bundle (n := n) (source := source) setup checks representation created writer index) := by
  apply RegistrationNativePlatformViewStable.map_stable view view_idempotent
  exact beacon setup checks representation created _
    (RegistrationNativeIdentityEnvReceiptLifecycle.bundle setup index writer)

/-- Lifting a derived actual Context receipt-view law preserves the entire owner roster and physical query tree. -/
theorem ordinary (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (law : RegistrationNativePlatformCtxBuildReceiptView.Stable work) :
    Stable (RegistrationNativePlatformIdentityCtxOrdinary.ordinary (source := source) work) := by
  intro before
  have transported := congrArg (fun script => (fun result => (result.1, ({before.1 with context := result.2.1}, result.2.2))) <$>
    simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend script) (law (before.1.context, before.2))
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.ordinary, RegistrationNativePlatformIdentityCtxCompiler.ordinary,
    StateT.run, simulateQ_map, Functor.map_map, view, RegistrationNativePlatformCtxBuildReceiptView.view,
    Prod.map_def, id_eq] at transported ⊢
  exact transported
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.view_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.create_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.create_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.finish_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.finish_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.bundle_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.bundle_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView.ordinary
