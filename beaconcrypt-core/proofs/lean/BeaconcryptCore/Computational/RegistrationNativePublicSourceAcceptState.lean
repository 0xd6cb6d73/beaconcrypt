-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution
import BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptPool

/-! Full native accept-state restoration includes the exact owner roster, opaque KEM pool and parsed counter, rather than only the Server controller. The coin-view Server projection is explicit; selected scalar restoration remains private. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePublicSourceServer (State run layout)
open RegistrationNativePublicSourceCallbacks (services remember)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationAuthenticationCompiler.program

noncomputable def project (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : State n KemSK source) : RegistrationNativeExperiment.State n KemSK source :=
  ⟨RegistrationServerOpenReferenceSourceEntry.project setup seed scalar (layout before),
    RegistrationNativePublicSourceState.owners scalar before.1.beacons, before.2.pool, before.1.parsedAccepts⟩

/-- The complete accept projection agrees with the named native/coin/log source view after only those analysis fields are erased. -/
theorem view_project (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : State n KemSK source) :
    RegistrationNativePublicSourceState.nativeView (project setup seed scalar before) =
      RegistrationNativePublicSourceState.project (RegistrationNativePublicSourceState.roots setup seed scalar)
        scalar before.1 before.2 := by
  simp only [RegistrationNativePublicSourceState.nativeView,
    RegistrationNativePublicSourceState.project, RegistrationNativePublicSourceState.restore,
    project, layout,
    RegistrationNativePublicSourceEffects.toPrivate,
    RegistrationServerOpenReferenceSourceEntry.project,
    RegistrationServerOpenReferenceSourceAccept.project,
    RegistrationServerReferenceSourceRetain.project,
    RegistrationServerReferenceRestore.restore,
    RegistrationNativeKemReferenceBackend.project,
    RegistrationWorldAgreementProgramCompiler.project,
    RegistrationWorldAgreementCompiler.join, RegistrationWorldAgreementCompiler.mask,
    RegistrationServerMaterialSourceState.nativeView, RegistrationServerMaterialSourceState.restore,
    RegistrationServerRecordWorldSource.project,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin]
  have sameRoots : RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar =
      RegistrationNativePublicSourceState.roots setup seed scalar := rfl
  rw [sameRoots]
  simp only [Function.update_idem]


theorem server_fields {Value : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((run setup wire route sign seed scalar selected work).run before)) :
    result.2.1.beacons = before.1.beacons ∧ result.2.1.parsedAccepts = before.1.parsedAccepts := by
  have observed := RegistrationNativePublicSourceExecution.observed_support setup wire route sign seed scalar
    (RegistrationNativePublicFrontend.serverOpen selected work) before result supported
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, support_map] at observed
  obtain ⟨inner, _possible, equal⟩ := observed
  exact ⟨(congrArg (fun output => output.2.beacons) equal).symm,
    (congrArg (fun output => output.2.parsedAccepts) equal).symm⟩

private theorem pool_kept (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (selected : Bool) (packet : registration.InitPacket)
    (before : State n KemSK source) (result : RustM (Option Nat) × State n KemSK source)
    (supported : result ∈ support ((run setup wire route sign seed scalar selected
      (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    result.2.2.pool = before.2.pool := by
  have reached : (result.1, layout result.2) ∈ support
      ((RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
        (services setup wire route sign seed scalar)
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run (layout before)) := by
    rw [← RegistrationNativePublicSourceServer.server_layout setup wire route sign seed scalar selected, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativePublicSourceAcceptPool.accept_pool setup checks verify seed scalar remember
    (services setup wire route sign seed scalar) packet (layout before) (result.1, layout result.2) reached

/-- Every actual native Server accept outcome retains the full original owner roster and private pool, alongside its precise Server source state. -/
theorem accept_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (wire : RegistrationNativeWire.Wire) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (packet : registration.InitPacket) (before : State n KemSK source) :
    Prod.map id (project setup created.seed scalar) <$>
      (run setup wire route sign created.seed scalar selected
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before =
      (RegistrationNativeExperiment.server
        (RegistrationServerSdkSource.accept setup codec checks route verify representation created packet)).run
          (project setup created.seed scalar before) := by
  have native := RegistrationNativePublicSourceServer.accept_source setup codec wire checks route sign verify
    representation correct created scalar selected packet before
  have lifted := congrArg (fun distribution => (fun result => (result.1,
    { project setup created.seed scalar before with server := result.2 })) <$> distribution) native
  rw [Functor.map_map] at lifted
  calc
    _ = (fun result => (result.1,
      { project setup created.seed scalar before with server :=
        RegistrationServerOpenReferenceSourceEntry.project setup created.seed scalar (layout result.2) })) <$>
        (run setup wire route sign created.seed scalar selected
          (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before := by
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply bind_congr_of_forall_mem_support
      intro result supported
      obtain ⟨owners, parsed⟩ := server_fields setup wire route sign created.seed scalar selected
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet) before result supported
      have pool := pool_kept setup wire checks route sign verify created.seed scalar selected packet before result supported
      simp only [Function.comp_def, Prod.map_def, id_eq, project, owners, parsed, pool]
    _ = _ := by
      simpa only [RegistrationNativeExperiment.server, StateT.run, Prod.map_def, id_eq, Function.comp_def, project] using lifted

end BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState.accept_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState.view_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState.view_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState.server_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceAcceptState.server_fields
