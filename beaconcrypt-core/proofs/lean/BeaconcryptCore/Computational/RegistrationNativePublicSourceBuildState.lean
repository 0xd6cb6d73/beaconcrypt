-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild

/-! Full Server build restoration retains the exact public owner roster and opaque private pool around the native SDK controller. Live roots are supplied by the initialized adaptive invariant; the only output erasure is the explicitly named native/coin/record-log analysis view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State run layout)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativePublicSourceState (restore project nativeView Live MemoCorrect)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem pool_kept (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK source) (result : RegistrationServerMaterialFrontend.Result × State n KemSK source)
    (live : Live before.1 before.2)
    (consistent : ∀ message root, before.2.roots message = some root → roots message = root)
    (supported : result ∈ support ((run setup wire route sign seed scalar false
      (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before)) :
    result.2.2.pool = before.2.pool := by
  have reached : (result.1, layout result.2) ∈ support
      ((RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
        (services setup wire route sign seed scalar)
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run (layout before)) := by
    rw [← RegistrationNativePublicSourceServer.server_layout setup wire route sign seed scalar false, support_map]
    exact ⟨result, supported, rfl⟩
  exact (RegistrationNativePublicSourceBuild.build_frame setup wire checks route sign seed scalar roots handle application
    (layout before) (result.1, layout result.2) live consistent reached).2

/-- Complete native build has the exact source SDK outcome and full private state under the explicit output analysis view. -/
theorem build_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK source)
    (live : Live before.1 before.2)
    (consistent : ∀ message root, before.2.roots message = some root → roots message = root) :
    Prod.map id (fun after => project roots scalar after.1 after.2) <$>
      (run setup wire route sign seed scalar false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.server
          (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
            handle application)).run (restore roots scalar before.1 before.2) := by
  have localSource := RegistrationNativePublicSourceBuild.build_source setup wire checks route sign seed scalar roots handle application
    (layout before) live consistent
  have frontend := congrArg (fun distribution => Prod.map id (fun current =>
    RegistrationServerMaterialSourceState.project roots (RegistrationServerOpenMaterialSource.project current)) <$> distribution)
    (RegistrationNativePublicSourceServer.server_layout setup wire route sign seed scalar false
      (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application) before)
  rw [localSource] at frontend
  have lifted := congrArg (fun distribution => (fun result => (result.1,
    { restore roots scalar before.1 before.2 with server := result.2 })) <$> distribution) frontend
  simp only [Functor.map_map] at lifted
  calc
    _ = (fun result => (result.1,
      { restore roots scalar before.1 before.2 with server :=
        RegistrationServerMaterialSourceState.project roots (RegistrationServerOpenMaterialSource.project (layout result.2)) })) <$>
        (run setup wire route sign seed scalar false
          (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before := by
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply bind_congr_of_forall_mem_support
      intro result supported
      obtain ⟨owners, parsed⟩ := RegistrationNativePublicSourceAcceptState.server_fields setup wire route sign seed scalar false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application) before result supported
      have pool := pool_kept setup wire checks route sign seed scalar roots handle application before result live consistent supported
      simp only [Function.comp_def, Prod.map_def, id_eq, project, nativeView, restore,
        RegistrationServerMaterialSourceState.nativeView, RegistrationServerMaterialSourceState.restore,
        RegistrationServerMaterialSourceState.project, RegistrationServerOpenMaterialSource.project,
        RegistrationServerOpenMaterialInterface.project, RegistrationServerReferenceRestore.restore,
        layout, RegistrationNativePublicSourceEffects.toPrivate, owners, parsed, pool]
    _ = _ := by
      simpa only [RegistrationNativeExperiment.server, StateT.run, Functor.map_map,
        Prod.map_def, id_eq, Function.comp_def, project, nativeView, restore,
        RegistrationServerMaterialSourceState.restore, RegistrationServerOpenMaterialSource.project,
        RegistrationServerOpenMaterialInterface.project, layout, RegistrationNativePublicSourceEffects.toPrivate] using lifted

/-- The initialized source memo and live-capability invariant instantiate full native build restoration without an extra source-root hypothesis. -/
theorem build_literal (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handle : Nat) (application : Option (Slice U8)) (before : State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots) :
    Prod.map id (fun after => project (RegistrationNativePublicSourceState.roots setup seed scalar) scalar after.1 after.2) <$>
      (run setup wire route sign seed scalar false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before =
      Prod.map id nativeView <$>
        (RegistrationNativeExperiment.server
          (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse
            handle application)).run
          (restore (RegistrationNativePublicSourceState.roots setup seed scalar) scalar before.1 before.2) := by
  apply build_native setup wire checks route sign seed scalar _ handle application before live
  intro message root stored
  change (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message).getD RegistrationBoundKeySchedule.zero = root
  rw [correct message root stored, Option.getD_some]

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState.build_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState.build_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState.build_literal
