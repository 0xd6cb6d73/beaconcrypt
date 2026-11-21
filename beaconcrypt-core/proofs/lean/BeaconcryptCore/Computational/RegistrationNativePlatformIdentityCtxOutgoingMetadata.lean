-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReceiptMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView
/-! Current ML signing annotations affect only the compact receipt appended by that source callback. Clearing that analysis coordinate after the literal shared-CTX Main join equates two annotations for the same actual signing request, preserving the current reply, physical calls, counters, private KEM state and P. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingMetadata
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private def close (result : (Value × RegistrationNativePlatformIdentityHistoryView.Packed
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) (Platform := Platform)) × RegistrationNativeIdentityWorld.Context n KemSK) :
    Value × (RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  (result.1.1, ({
    context := {result.2 with server := {result.2.server with
      world := RegistrationWorldAgreementCompiler.join result.1.2.1.2 result.2.server.world.world.1}}
    beacons := result.1.2.1.1 }, result.1.2.2))

private def observe (result : (Value × RegistrationNativePlatformIdentityHistoryView.Packed
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) (Platform := Platform)) × RegistrationNativeIdentityWorld.Context n KemSK) :=
  Prod.map id RegistrationNativePlatformIdentityCtxReceiptView.view (close result)

/-- Equal ML requests yield the same actual Main outcome after the explicit receipt view, regardless of their private raw payload/digest annotations. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (request : registration.MldsaSigningRequest)
    (left right : MldsaTranscriptAuth.Payload) (digestLeft digestRight : CtxRomAuth.CtxDigest)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    Prod.map id RegistrationNativePlatformIdentityCtxReceiptView.view <$>
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native
          (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
            setup source index owner (.inl (.sign request left digestLeft))))).run before =
    Prod.map id RegistrationNativePlatformIdentityCtxReceiptView.view <$>
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native
          (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
            setup source index owner (.inl (.sign request right digestRight))))).run before := by
  have compact := RegistrationNativeIdentityReceiptMetadata.compact (n := n) setup index owner request left right digestLeft digestRight
    (before.1.beacons, RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
  have platform := congrArg (fun action => (fun result => (result.1, (result.2, before.2))) <$>
    simulateQ (RegistrationNativePlatformIdentityProgram.nativeLift (n := n) (KemSK := KemSK)) action) compact
  have transported := congrArg (fun script => observe <$>
    (simulateQ (RegistrationNativePlatformIdentityCtxCompiler.free
      (RegistrationNativePlatformIdentityCtxAmbient.program (source := source) setup checks representation created)) script).run before.1.context) platform
  simp only [RegistrationNativeIdentityHistoryView.pack,
    RegistrationNativeIdentityEnvReceiptView.view, StateT.run,
    simulateQ_map, map_apply, Functor.map_map,
    observe, close, RegistrationNativePlatformIdentityCtxReceiptView.view,
    RegistrationNativePlatformCtxBuildReceiptView.context, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq] at transported
  simp only [RegistrationNativePlatformIdentityCtxMain.beacon, RegistrationNativePlatformIdentityCtxCompiler.beacon,
    RegistrationNativePlatformIdentityProgram.native, StateT.run, simulateQ_map, map_apply,
    Functor.map_map, RegistrationNativePlatformIdentityCtxReceiptView.view,
    RegistrationNativePlatformCtxBuildReceiptView.context, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]
  exact transported
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingMetadata.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingMetadata.outgoing
