-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView

/-! The literal free Context accept controller never reads earlier raw ML receipt payloads. The receipt view retains current verification operands, replay state, reservations, agreement results, token insertion, all native counters and the same platform/backend state. No whole-source or whole-controller independence law is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformCtxRunner (M)
open RegistrationNativePlatformCtxSdkReceiptView (Stable pure_stable bind_stable serverView view)
variable {n : Nat} {I KemSK Auxiliary Platform A : Type} {base : OracleSpec I}

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem agreement_query (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id RegistrationNativePlatformIdentityReceiptView.view <$>
      (RegistrationWorldAgreement.agreement source primitive query).run before =
      (RegistrationWorldAgreement.agreement source primitive query).run (RegistrationNativePlatformIdentityReceiptView.view before) := by
  simp only [RegistrationWorldAgreement.agreement, StateT.run, Functor.map_map,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

private theorem agreement_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec A) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id RegistrationNativePlatformIdentityReceiptView.view <$>
      (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run before =
      (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run (RegistrationNativePlatformIdentityReceiptView.view before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (agreement_query source primitive) work before

private theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id serverView <$> (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before =
      (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run (serverView before) := by
  have framed := agreement_program setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed)
    (RegistrationReplaySchedule.begin before.control authenticated before.consumed) before.world
  have mapped := congrArg (fun action => (fun result => (result.1, {serverView before with world := result.2})) <$> action) framed
  simpa only [RegistrationServerNativeSource.agree, StateT.run, Functor.map_map, serverView, Prod.map_def, id_eq] using mapped

private theorem retain (created : PqxdhLiveServerConstruction.Created Unit) (accepted : agreement.ServerAgreement)
    (before : RegistrationServerFrontendCompiler.State n) :
    Prod.map id serverView <$> (RegistrationServerNativeSource.retain created accepted).run before =
      (RegistrationServerNativeSource.retain created accepted).run (serverView before) := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run, serverView]
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div => simp only [map_pure]; rfl
  | ok selected => rcases selected with ⟨token, history⟩; cases token <;> simp only [map_pure] <;> rfl

private theorem ordinary (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A)
    (law : ∀ before, Prod.map id serverView <$> work.run before = work.run (serverView before)) :
    Stable (RegistrationNativePlatformCtxAcceptFrame.ordinary (Platform := Platform) work) := by
  rintro ⟨before, previous⟩
  have projected := congrArg (fun action => Prod.map id serverView <$> action) (law before)
  simp only [Functor.map_map] at projected
  change (Prod.map id serverView <$> work.run before) =
    (Prod.map id serverView <$> work.run (serverView before)) at projected
  have interpreted := congrArg (simulateQ RegistrationNativePlatformCtxBackend.coin) projected
  have mapped := congrArg (fun action => (fun result => (result.1, (result.2, previous))) <$> action) interpreted
  simpa only [RegistrationNativePlatformCtxAcceptFrame.ordinary, RegistrationNativePlatformCtxRunner.privateWork,
    RegistrationNativePlatformInterpret.state, RegistrationNativePlatformPackedState.pack, StateT.run,
    state_lift_apply, bind_pure_comp, simulateQ_map, Functor.map_map, view, serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq] using mapped

private theorem hash (bytes : Pqxdh.Bytes) :
    Stable (RegistrationNativePlatformCtxAcceptAuthentication.hash (n := n) (Platform := Platform) bytes) :=
  RegistrationNativePlatformCtxSdkReceiptView.world_stable _
    (RegistrationNativePlatformCtxReceiptView.private_stable _ (RegistrationNativePlatformIdentityReceiptView.effects _))

private theorem authentication_query (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) :
    Stable (RegistrationNativePlatformCtxAcceptAuthentication.callbacks (n := n) (Platform := Platform) crypto verify query) := by
  cases query with
  | hash request => exact bind_stable _ _ (hash _) (fun _ => pure_stable _)
  | mldsa request | ed25519 request => exact pure_stable _

private theorem authentication (setup : Setup base KemSK) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Stable (RegistrationNativePlatformCtxAcceptAuthentication.authenticate (n := n) (Platform := Platform) setup verify pin packet) := by
  unfold RegistrationNativePlatformCtxAcceptAuthentication.authenticate
  induction RegistrationAuthenticationExecutor.begin pin packet using OracleComp.inductionOn with
  | pure value => exact pure_stable _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable _ _ (authentication_query setup.source.crypto verify query) ih

private theorem consumed (authenticated : registration.AuthenticatedInit) :
    Stable ((fun before => pure (before.consumed.contains (RegistrationReplaySchedule.identifier authenticated), before)) :
      M (RegistrationServerFrontendCompiler.State n) Platform Bool) := by
  rintro ⟨before, previous⟩
  simp only [RegistrationNativePlatformPackedState.pack, StateT.run, state_pure_apply, map_pure,
    view, serverView, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

private theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Stable (RegistrationNativePlatformCtxAcceptSdk.afterAuthentication (n := n) setup checks reserve representation created packet authenticated) := by
  unfold RegistrationNativePlatformCtxAcceptSdk.afterAuthentication
  apply bind_stable _ _ (consumed authenticated)
  intro used
  cases used with
  | true => exact pure_stable _
  | false =>
    apply bind_stable _ _ (RegistrationNativePlatformCtxSdkSourceReceiptView.reserve_stable reserve)
    intro admitted
    cases admitted with
    | false => exact pure_stable _
    | true =>
      apply bind_stable _ _ (ordinary _ (agree setup checks representation created packet authenticated))
      intro completed
      cases completed with
      | fail error | div => exact pure_stable _
      | ok effect => cases effect <;> first
        | exact pure_stable _
        | exact ordinary _ (retain created _)

private theorem afterPin (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (result : RegistrationNativeServerPinRecompute.PinReply) :
    Stable (RegistrationNativePlatformCtxAcceptSdk.afterPin (n := n) setup checks reserve verify representation created packet result) := by
  unfold RegistrationNativePlatformCtxAcceptSdk.afterPin
  cases result with
  | fail error | div => exact pure_stable _
  | ok selected => cases selected with
    | none => exact pure_stable _
    | some pin =>
      apply bind_stable _ _ (authentication setup verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact pure_stable _
      | ok pair =>
        rcases pair with ⟨events, verdict⟩
        cases verdict <;> first
          | exact pure_stable _
          | exact afterAuthentication setup checks reserve representation created packet _

/-- The actual SDK accept controller ignores only earlier raw ML receipt payloads; no branch or mutable state is dropped. -/
theorem sdk (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    Stable (RegistrationNativePlatformCtxAcceptSdk.accept (n := n) setup checks reserve verify representation created packet) := by
  unfold RegistrationNativePlatformCtxAcceptSdk.accept
  exact bind_stable _ _ RegistrationNativePlatformCtxSdkSourceReceiptView.pin_stable
    (afterPin setup checks reserve verify representation created packet)

/-- The full Context parse-attempt increment preserves that same receipt view, with the exact KEM pool, P and backend state retained. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket) :
    RegistrationNativePlatformCtxBuildReceiptView.Stable
      (RegistrationNativePlatformCtxAccept.accept (n := n) setup checks reserve verify representation created packet) := by
  intro before
  have same := RegistrationNativePlatformCtxBuildReceiptView.server_stable _
    (sdk setup checks reserve verify representation created packet) (RegistrationNativePlatformCtxAccept.increment before)
  simpa only [RegistrationNativePlatformCtxAccept.accept, StateT.run, RegistrationNativePlatformCtxAccept.increment,
    RegistrationNativePlatformCtxBuildReceiptView.view, RegistrationNativePlatformCtxBuildReceiptView.context] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView.sdk
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView.accept
