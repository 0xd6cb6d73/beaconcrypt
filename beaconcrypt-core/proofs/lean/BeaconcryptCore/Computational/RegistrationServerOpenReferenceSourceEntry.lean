-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept
import BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection

/-! The actual open native Server accept entry retains mandatory ML/Ed authentication before owned replay, reservation and agreement. The source equality is composed from the actual shared verifier and the derived complete post-authentication controller, with only the separately accounted Env coin ledger projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry
open PqxdhServerAuthExperiment (Setup Checks Codec)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationServerOpenReferenceSourceStage (callbacks)
open RegistrationServerOpenReferenceSourceAccept (State close close_bind close_get close_pure)
attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

variable {n : Nat} {ι KemSK Extra Value Reader Response : Type} {base : OracleSpec ι}

noncomputable def project (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : State n KemSK Extra) : RegistrationServerFrontendCompiler.State n :=
  RegistrationServerReferenceSourceRetain.project
    (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar)
    (RegistrationServerOpenReferenceSourceAccept.project before)

private theorem effect_program (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : RegistrationNativeKemReferenceWorld.Private n KemSK Extra) :
    (simulateQ (implementation setup (callbacks setup seed scalar remember services))
      (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [← QueryImpl.simulateQ_compose]
  have same : implementation setup (callbacks setup seed scalar remember services) ∘ₛ
      RegistrationBeaconReferenceCompiler.effect = RegistrationNativeKemReferenceWorld.effect := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceCompiler.effect,
      simulateQ_spec_query, implementation, RegistrationNativeKemReferenceWorld.handler]
  rw [same]
  exact RegistrationNativeKemReferenceWorld.world_program PqxdhRecordLiftWorld.effects work before

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun result => (result, state)) <$> work := by
  change (work >>= fun result => pure (result, state)) = _
  rw [bind_pure_comp]

/-- Actual lifted authentication effects keep every local frontend, environment and private-pool coordinate while executing the original World. -/
theorem close_effect (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : State n KemSK Extra) :
    (close setup seed scalar remember services
      (StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceCompiler.effect work)))).run before =
      (fun result => (result.1, (before.1, (before.2.1, { before.2.2 with world := result.2 })))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.2.2.world := by
  simp only [close, RegistrationNativeKemReferencePrefix.lower, StateT.run, state_lift_apply,
    simulateQ_map, state_map_apply, Functor.map_map]
  have native := effect_program setup seed scalar remember services work before.2.2
  simp only [StateT.run] at native
  rw [native]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Incoming mandatory ML/Ed/hash verification has its literal native source interpretation before every owned replay check. -/
theorem authenticate_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (before : State n KemSK Extra) :
    Prod.map id (project setup created.seed scalar) <$>
      (close setup created.seed scalar remember services (StateT.lift (StateT.lift
        (simulateQ RegistrationBeaconReferenceCompiler.effect
          (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.1.pin packet))))).run before =
      (RegistrationServerNativeSource.authenticate setup codec route verify created packet).run
        (project setup created.seed scalar before) := by
  rw [close_effect, RegistrationAuthenticationCompiler.begin_native setup codec route verify before.1.pin packet]
  have native := congrArg (fun distribution => (fun result => (result.1,
    { project setup created.seed scalar before with world :=
      { (project setup created.seed scalar before).world with world := (result.2, before.2.1.receipts) } })) <$> distribution)
    (RegistrationAuthenticationCoinProjection.begin_mask setup codec route verify before.1.pin packet before.2.2.world)
  simp only [Functor.map_map, Prod.map_def, id_eq, project,
    RegistrationServerOpenReferenceSourceAccept.project, RegistrationServerReferenceSourceRetain.project,
    RegistrationServerReferenceRestore.restore, RegistrationNativeKemReferenceBackend.project,
    RegistrationWorldAgreementProgramCompiler.project, RegistrationWorldAgreementCompiler.join,
    RegistrationWorldAgreementCompiler.mask,
    RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    RegistrationServerFrontendCompiler.restore, RegistrationServerFrontendCompiler.erase,
    StateT.run] at native ⊢
  exact native

set_option maxRecDepth 2048 in
/-- The full actual open Server accept entry is the native SDK source controller, including every verifier, replay, allocation and one-use-session failure. -/
theorem accept_native (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (before : State n KemSK Extra) :
    Prod.map id (project setup created.seed scalar) <$>
      (close setup created.seed scalar remember services
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before =
      (RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run
        (project setup created.seed scalar before) := by
  rw [RegistrationServerOpenReferenceCompiler.accept, close_bind, close_get, pure_bind]
  simp only [RegistrationServerSdkSource.accept, StateT.run_bind]
  rw [← authenticate_native setup codec route verify created scalar remember services packet before, bind_map_left]
  rw [close_bind, map_bind]
  apply bind_congr
  rintro ⟨checked, current⟩
  cases checked with
  | fail error => simp only [close_pure, map_pure]; rfl
  | div => simp only [close_pure, map_pure]; rfl
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict with
      | Rejected => simp only [close_pure, map_pure]; rfl
      | HashRequested _ => simp only [close_pure, map_pure]; rfl
      | MldsaVerificationRequested _ => simp only [close_pure, map_pure]; rfl
      | Ed25519VerificationRequested _ => simp only [close_pure, map_pure]; rfl
      | ServerFingerprintRequested _ => simp only [close_pure, map_pure]; rfl
      | BeaconFingerprintRequested _ => simp only [close_pure, map_pure]; rfl
      | Accepted authenticated =>
          exact RegistrationServerOpenReferenceSourceAccept.after_native setup checks representation correct
            created scalar remember services packet authenticated current

end BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry.close_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry.close_effect
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry.authenticate_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry.authenticate_native
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceEntry.accept_native
