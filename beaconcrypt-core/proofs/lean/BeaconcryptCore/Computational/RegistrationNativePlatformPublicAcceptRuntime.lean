-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptState
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceInvariant
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
/-! Corrected OPEN acceptance has the literal runtime source comparison on the complete private state and P. Input and output instrumentation views are transported by actual source bodies; true uniform counts, cache and protocol fields remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (roots restore project nativeView)
open RegistrationNativePlatformPublicSourceLocal (external)
variable {n : Nat} {I KemSK Platform Reader Response A E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The concrete OPEN restore and full source restore have the same explicitly named instrumentation view. -/
theorem view_project (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : State n KemSK Platform source) :
    nativeView (RegistrationNativePlatformPublicAcceptState.project setup seed scalar before) =
      project (roots setup seed scalar) scalar before.1.1 before.2 := by
  simp only [nativeView, project, restore, RegistrationNativePlatformPublicAcceptState.project,
    RegistrationNativePlatformPublicSourceServer.layout, RegistrationNativePublicSourceEffects.toPrivate,
    RegistrationNativePlatformServerOpenControl.project, RegistrationServerReferenceRestore.restore,
    RegistrationNativeKemReferenceBackend.project, RegistrationWorldAgreementProgramCompiler.project,
    RegistrationWorldAgreementCompiler.join, RegistrationWorldAgreementCompiler.mask,
    RegistrationServerMaterialSourceState.nativeView, RegistrationServerMaterialSourceState.restore,
    RegistrationServerRecordWorldSource.project, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem server_stable {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : StateT (RegistrationServerFrontendCompiler.State n) m A)
    (stable : RegistrationStateView.Stable RegistrationServerMaterialSourceState.nativeView work) :
    RegistrationStateView.Stable (nativeView (KemSK := KemSK) (mlSource := source))
      (RegistrationNativePlatformExperiment.server work) := by
  intro before
  have mapped := congrArg (fun action => (fun result =>
    (result.1, {nativeView before with server := result.2})) <$> action) (stable before.server)
  simpa only [RegistrationNativePlatformExperiment.server, StateT.run, Functor.map_map,
    nativeView, Prod.map_def, id_eq, Function.comp_def] using mapped

/-- The whole actual source accept uses the complete original native private state, with only named instrumentation projected and the same P retained. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response)
    (wire : RegistrationNativeWire.Wire) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State n KemSK Platform source) :
    (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup wire route sign created.seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
          (RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
            (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformSourceAccept.accept external setup codec checks reserve route verify representation created packet)).run
            (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).run before.1.2 := by
  have actual := RegistrationNativePlatformPublicAcceptState.accept setup codec wire checks route sign verify representation correct
    created scalar selected reserve packet before
  have mapped := congrArg (fun action => Prod.map (Prod.map id nativeView) id <$> action) actual
  simp only [Functor.map_map, Prod.map_def, id_eq, view_project] at mapped
  let work := RegistrationNativePlatformExperiment.server (n := n) (source := source) (KemSK := KemSK)
    (RegistrationNativePlatformSourceAccept.accept external setup codec checks reserve route verify representation created packet)
  have stable : RegistrationStateView.Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := source)) work :=
    server_stable _ (RegistrationNativePlatformSourceAcceptMetricView.accept external setup codec checks reserve route verify representation created packet)
  have same : nativeView (RegistrationNativePlatformPublicAcceptState.project setup created.seed scalar before) =
      nativeView (restore (roots setup created.seed scalar) scalar before.1.1 before.2) := view_project setup created.seed scalar before
  have compared : Prod.map id nativeView <$> work.run (RegistrationNativePlatformPublicAcceptState.project setup created.seed scalar before) =
      Prod.map id nativeView <$> work.run (restore (roots setup created.seed scalar) scalar before.1.1 before.2) :=
    (stable (RegistrationNativePlatformPublicAcceptState.project setup created.seed scalar before)).trans
    (by rw [same]; exact (stable (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).symm)
  have atPlatform := congrArg (fun action => action.run before.1.2) compared
  have final := mapped.trans (by
    simpa only [work, StateT.run, map_apply, Prod.map_def, id_eq] using atPlatform)
  exact final

-- The corrected accept now selects the Server pin purely (no fingerprint hash query); keep the source accept program opaque to the elaborator so the `rfl` below matches it by name instead of evaluating the pin construction. Proof terms are unchanged and kernel-checked.
attribute [local irreducible] RegistrationNativePlatformSourceAccept.accept in
/-- The actual parsed-accept callback advances the source attempt counter before the same full-state runtime acceptance. -/
theorem typed [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (selectedOwner selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (packet : registration.InitPacket) (before : State n KemSK Platform source) :
    (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)))).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryScalarEager.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar (.inr (.accept packet))).run
          (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).run before.1.2 := by
  change (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
    ((RegistrationNativePlatformPublicSourceInvariant.callback setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route (RegistrationNativeMldsa.owned source credential)
      created.seed scalar selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet))).run before) = _
  rw [RegistrationNativePlatformPublicSourceInvariant.accept_source setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route (RegistrationNativeMldsa.owned source credential)
    created.seed scalar selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer packet before]
  convert accept setup (RegistrationNativeWire.ledgerCodec
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) checks route (RegistrationNativeMldsa.owned source credential)
    source.verify representation correct created scalar (decide (before.1.1.parsedAccepts = selectedAccept)) reserveRegistration packet
    (RegistrationNativePlatformPublicSourceInvariant.advance before) using 1 <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime.view_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime.view_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime.typed
