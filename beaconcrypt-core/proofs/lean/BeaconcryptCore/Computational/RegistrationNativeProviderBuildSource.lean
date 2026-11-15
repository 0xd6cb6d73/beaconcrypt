-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame
import BeaconcryptCore.Computational.RegistrationNativeProviderSource
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildState

/-! Actual source closure of the provider-parametric Server build retains the whole arbitrary provider frame. The zero-provider-query certificate is discharged for its literal controller, then the existing current-Env source108/publication/SDK equality applies. Only the explicitly named native/coin/record-log analysis view is projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute)
open RegistrationNativePublicSourceState (Live MemoCorrect restore project nativeView roots)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Closing the actual build keeps the entire provider state without invoking it, while retaining all source callbacks and counters. -/
theorem execute_frame (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (handle : Nat) (application : Option (Slice U8))
    (before : FrontState n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.serverOpen false
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application))).run before =
      (fun result => (result.1, (result.2.1, (result.2.2, before.2.2)))) <$>
        (RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar
          (RegistrationNativePublicFrontend.serverOpen false
            (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application))).run (before.1, before.2.1) := by
  have framed := RegistrationNativeProviderBuildFrame.build_frame setup checks wire route sign provider handle application before.1 before.2
  have closed := congrArg (fun work => simulateQ
    (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar) work) framed
  have packed := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work) closed
  dsimp only [StateT.run] at packed
  dsimp only [execute, RegistrationNativeProviderSource.close, RegistrationNativePublicSourceExecution.execute,
    RegistrationNativePublicSourceEffects.close, StateT.run]
  simpa only [simulateQ_map, Functor.map_map] using packed

/-- An arbitrary same total provider, including a candidate provider, yields the actual native SDK build through its concrete source108 and complete optional publication paths. -/
theorem build_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (handle : Nat) (application : Option (Slice U8))
    (before : FrontState n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots) :
    Prod.map id (fun after => (project (roots setup seed scalar) scalar after.1 after.2.1, after.2.2)) <$>
      (execute setup wire route sign seed scalar provider
        (RegistrationNativePublicFrontend.serverOpen false
          (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application))).run before =
      (fun result => (result.1, (nativeView result.2, before.2.2))) <$>
        (RegistrationNativeExperiment.server (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire)
          checks sign wire.encodeResponse handle application)).run
            (restore (roots setup seed scalar) scalar before.1 before.2.1) := by
  rw [execute_frame]
  have same := congrArg (fun distribution => (fun result => (result.1, (result.2, before.2.2))) <$> distribution)
    (RegistrationNativePublicSourceBuildState.build_literal setup wire checks route sign seed scalar handle application
      (before.1, before.2.1) live correct)
  have ordinary : RegistrationNativePublicSourceServer.run (n := n) (source := source) setup wire route sign seed scalar false
      (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application) =
      RegistrationNativePublicSourceExecution.execute (n := n) (source := source) setup wire route sign seed scalar
        (RegistrationNativePublicFrontend.serverOpen false
          (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)) := rfl
  rw [ordinary] at same
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same

/-- The complete typed build has the same actual SDK dispatcher entry and preserves the provider coordinate without a whole-game equality assumption. -/
theorem handler_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (provider : Provider KemSK ProviderState)
    (handle : Nat) (application : Option (Slice U8)) (before : FrontState n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup created.seed scalar before.2.1.roots) :
    Prod.map id (fun after => (project (roots setup created.seed scalar) scalar after.1 after.2.1, after.2.2)) <$>
      (execute setup wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar provider
        (RegistrationNativePublicFrontend.handler setup checks wire source (RegistrationNativeMldsa.owned source credential)
          selectedOwner selectedAccept publicPrekey (.inr (.build handle application)))).run before =
      (fun result => (result.1, (nativeView result.2, before.2.2))) <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.build handle application))).run
          (restore (roots setup created.seed scalar) scalar before.1 before.2.1) := by
  exact build_source setup checks wire route (RegistrationNativeMldsa.owned source credential) created.seed scalar provider handle application before live correct

end BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource.execute_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource.execute_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource.build_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBuildSource.handler_source
