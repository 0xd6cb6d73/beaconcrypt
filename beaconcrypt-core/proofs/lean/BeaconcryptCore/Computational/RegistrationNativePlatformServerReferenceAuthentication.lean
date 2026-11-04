-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Repeated actual pin hashing and mandatory native authentication retain the public-reference frontend and full shared poststate before replay, stateful reservation and one-use retention. Only the dedicated Envcoin forwarding ledger is projected; true sampler costs remain literal. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformServerReferenceAccept
open RegistrationWorldCoinCompiler (eraseCoin)
variable {n : Nat} {ι KemSK Value Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem close_effect (work : StateT (PqxdhRecordLiftWorld.State n) m Value) (before : State n) :
    (close (StateT.lift (StateT.lift work) : PublicM (StateT (PqxdhRecordLiftWorld.State n) m) Value)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$> work.run before.2.2 := by
  simp only [close, RegistrationNativePlatformServerReferencePrefix.closeEnvironment, StateT.run,
    StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure,
    bind_pure_comp, Functor.map_map]

private theorem hash_source (coins : QueryImpl unifSpec m) (request : registration.HashRequest) :
    RegistrationNativePlatformServerReferenceAccept.hash (RegistrationNativePlatformServerReferencePrefix.effects (n := n) coins) request =
      RegistrationNativePlatformInterpret.state coins (RegistrationNativeServerPinRecompute.nativeHash request) := by
  unfold RegistrationNativePlatformServerReferenceAccept.hash RegistrationNativeServerPinRecompute.nativeHash
  rw [RegistrationNativePlatformInterpret.state_bind]
  simp only [RegistrationNativePlatformInterpret.state_pure]
  rfl

private theorem native_hash_mask (request : registration.HashRequest) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$> (RegistrationNativeServerPinRecompute.nativeHash request).run before =
      (RegistrationNativeServerPinRecompute.nativeHash request).run (eraseCoin before) := by
  have compared := congrArg (fun work => (fun result =>
      (RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1)), result.2)) <$> work)
    (RegistrationAuthenticationCoinProjection.hash_mask (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before)
  simpa only [RegistrationNativeServerPinRecompute.nativeHash, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
    Functor.map_map, Prod.map_def, id_eq] using compared

private theorem pin_source (coins : QueryImpl unifSpec m) (before : session.ServerAuthenticationPin) :
    pin (RegistrationNativePlatformServerReferencePrefix.effects (n := n) coins) before =
      RegistrationNativePlatformInterpret.state coins (RegistrationNativeServerPinRecompute.native before.binding before.public_key) := by
  unfold pin RegistrationNativeServerPinRecompute.native
  rw [RegistrationNativePlatformInterpret.state_simulate]
  apply congrArg (fun implementation => simulateQ implementation (RegistrationNativeServerPinRecompute.program before.binding before.public_key))
  funext query
  exact hash_source coins query

private theorem pin_mask_source (coins : QueryImpl unifSpec m) (pin : session.ServerAuthenticationPin)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$> (RegistrationNativePlatformServerReferenceAccept.pin
      (RegistrationNativePlatformServerReferencePrefix.effects coins) pin).run before =
      simulateQ coins ((RegistrationNativeServerPinRecompute.native pin.binding pin.public_key).run (eraseCoin before)) := by
  rw [pin_source]
  unfold RegistrationNativePlatformInterpret.state
  change Prod.map id eraseCoin <$> simulateQ coins ((RegistrationNativeServerPinRecompute.native pin.binding pin.public_key).run before) = _
  rw [← simulateQ_map]
  rw [show Prod.map id eraseCoin <$> (RegistrationNativeServerPinRecompute.native pin.binding pin.public_key).run before =
      (RegistrationNativeServerPinRecompute.native pin.binding pin.public_key).run (eraseCoin before) from
        OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ eraseCoin native_hash_mask _ before]


theorem pin_native (coins : QueryImpl unifSpec m) (roots : RegistrationServerReferenceRestore.Roots) (before : State n) :
    Prod.map id (project roots) <$>
      (close (StateT.lift (StateT.lift (RegistrationNativePlatformServerReferenceAccept.pin
        (RegistrationNativePlatformServerReferencePrefix.effects coins) before.1.pin)))).run before =
      (RegistrationNativePlatformSourceBuild.pin coins).run (project roots before) := by
  rw [close_effect]
  have compared := congrArg (fun work => (fun result => (result.1,
      RegistrationServerReferenceRestore.restore roots before.1 (RegistrationWorldAgreementCompiler.join before.2.1 result.2))) <$> work)
    (pin_mask_source coins before.1.pin before.2.2)
  simpa only [Functor.map_map, Prod.map_def, id_eq, project, RegistrationServerReferenceRestore.restore,
    RegistrationWorldAgreementProgramCompiler.project, RegistrationWorldAgreementCompiler.mask, RegistrationWorldAgreementCompiler.join,
    RegistrationNativePlatformSourceBuild.pin, StateT.run] using compared

private theorem authentication_source (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ (RegistrationNativePlatformServerReferencePrefix.effects coins)
      (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)).run before =
      simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before) := by
  unfold RegistrationNativePlatformServerReferencePrefix.effects
  rw [← RegistrationNativePlatformInterpret.state_simulate]
  change simulateQ coins ((simulateQ PqxdhRecordLiftWorld.effects
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)).run before) = _
  rw [RegistrationServerReferenceCompilerNative.authentication_native setup codec route verify pin packet before]

private theorem authentication_mask_source (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id eraseCoin <$>
      (simulateQ (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)).run before =
      simulateQ coins ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run (eraseCoin before)) := by
  rw [authentication_source coins setup codec route verify pin packet before, ← simulateQ_map,
    RegistrationAuthenticationCoinProjection.begin_mask setup codec route verify pin packet before]

theorem authentication_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (roots : RegistrationServerReferenceRestore.Roots) (before : State n) :
    Prod.map id (project roots) <$>
      (close (StateT.lift (StateT.lift (simulateQ (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet))))).run before =
      (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet).run (project roots before) := by
  rw [close_effect]
  have compared := congrArg (fun work => (fun result => (result.1,
      RegistrationServerReferenceRestore.restore roots before.1 (RegistrationWorldAgreementCompiler.join before.2.1 result.2))) <$> work)
    (authentication_mask_source coins setup codec route verify pin packet before.2.2)
  simpa only [Functor.map_map, Prod.map_def, id_eq, project, RegistrationServerReferenceRestore.restore,
    RegistrationWorldAgreementProgramCompiler.project, RegistrationWorldAgreementCompiler.mask, RegistrationWorldAgreementCompiler.join,
    RegistrationNativePlatformSourceAccept.authenticate, StateT.run] using compared


theorem after_pin_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reserve : m Bool) (packet : registration.InitPacket) (result : RegistrationNativeServerPinRecompute.PinReply) (before : State n) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (RegistrationNativePlatformServerReferenceAccept.afterPin
        (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationNativePlatformServerReferenceAgreement.prepareSource setup created.seed scalar)
        (StateT.lift reserve) setup checks verify packet result)).run before =
      (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
        route verify representation created packet result).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
      route verify representation created packet result).run (project roots before)
  unfold RegistrationNativePlatformServerReferenceAccept.afterPin RegistrationNativePlatformSourceAccept.afterPin
  cases result with
  | fail error | div => simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | ok optional => cases optional with
    | none => simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
    | some pin =>
      simp only [StateT.run_bind]
      rw [close_bind, StateT.run_bind, map_bind,
        ← authentication_native coins setup codec route verify pin packet roots before, bind_map_left]
      apply bind_congr
      rintro ⟨checked, current⟩
      cases checked with
      | fail error | div => simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
      | ok pair =>
        rcases pair with ⟨events, authentication⟩
        cases authentication
        all_goals first
          | exact after_native coins setup checks representation correct created scalar reserve packet _ current
          | simp only [close_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]

theorem accept_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reserve : m Bool) (packet : registration.InitPacket) (before : State n) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (RegistrationNativePlatformServerReferenceAccept.accept
        (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationNativePlatformServerReferenceAgreement.prepareSource setup created.seed scalar)
        (StateT.lift reserve) setup checks verify packet)).run before =
      (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run (project roots before)
  unfold RegistrationNativePlatformServerReferenceAccept.accept RegistrationNativePlatformSourceAccept.accept
  rw [close_bind, StateT.run_bind, close_get, pure_bind, RegistrationNativePlatformSourceAccept.acceptWith_run]
  rw [close_bind, StateT.run_bind, map_bind, ← pin_native coins roots before, bind_map_left]
  apply bind_congr
  rintro ⟨pinned, current⟩
  exact after_pin_native coins setup codec checks route verify representation correct created scalar reserve packet pinned current

end BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.close_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.close_effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.pin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.pin_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.authentication_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.authentication_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.after_pin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.after_pin_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAuthentication.accept_native
