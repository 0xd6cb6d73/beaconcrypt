-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAuthentication
/-! A successful selected corrected OPEN accept retains its own genuine marked collector under the granular source KEM contract. The only separate operation frame is the public reservation's marker frame, discharged by actual public-coin syntax at the source envelope. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetained
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordInterface (Spec liftLocal)
open RegistrationNativePlatformLorSourceRetainedCore (Auxiliary lower)
open RegistrationNativePlatformLorSourceRetainedControl (State close)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Private A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
local notation "localImpl" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal true
local notation "effects" => RegistrationNativePlatformSecretWordOpen.effects localImpl
include contract
attribute [local irreducible] RegistrationAuthenticationCompiler.program PqxdhDeploymentTranscript.acceptedKeys
  RegistrationRootInput.candidate RegistrationNativePlatformServerReferenceAccept.pin

omit contract in
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value,before)) <$> work := bind_pure_comp _ _
omit contract in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

private theorem effects_phase (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (before : Private) (result : A × Private) (supported : result ∈ support ((simulateQ effects work).run before)) :
    (kem result.2).2 = (kem before).2 := by
  exact RegistrationNativePlatformLorSourcePhase.program_phase setup selected pairs publicKey challenge implementation kem input contract
    (simulateQ (liftLocal true) (simulateQ RegistrationNativeSecretWordInterface.effect work))
    (RegistrationNativeSecretWordTargetServerPhase.effect_free true work) before result
    (by simpa only [RegistrationNativePlatformSecretWordOpen.effects,QueryImpl.simulateQ_compose] using supported)

private theorem pin_phase (current : session.ServerAuthenticationPin) (before : Private)
    (result : RegistrationNativeServerPinRecompute.PinReply × Private)
    (supported : result ∈ support ((RegistrationNativePlatformServerReferenceAccept.pin effects current).run before)) :
    (kem result.2).2 = (kem before).2 := by
  rw [RegistrationNativePlatformSecretWordTargetOpenLift.pin,StateT.run_map,support_map] at supported
  obtain ⟨hashed,called,equal⟩ := supported
  have unchanged := effects_phase setup selected pairs publicKey challenge implementation kem input contract
    (((PqxdhRecordLiftInterface.EnvEffects n).query (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _) before hashed
    (by simpa only [simulateQ_spec_query] using called)
  cases equal
  exact unchanged

omit contract in
private theorem lifted_run (work : StateT Private ProbComp A) (before : State Private) :
    (close (StateT.lift (StateT.lift work))).run before =
      (fun result => (result.1,(before.1,(before.2.1,result.2)))) <$> work.run before.2.2 := by
  simp only [RegistrationNativePlatformLorSourceRetainedControl.close,StateT.run,lift_apply,map_apply,Functor.map_map]
  rfl

omit contract in
private theorem lifted_support (work : StateT Private ProbComp A) (before : State Private)
    (result : A × State Private) (supported : result ∈ support ((close (StateT.lift (StateT.lift work))).run before)) :
    (result.1,result.2.2.2) ∈ support (work.run before.2.2) := by
  rw [lifted_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  exact called

omit contract in
private theorem agreement_support (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State Private) (result : RustM (Option ServerReady) × State Private)
    (supported : result ∈ support ((close (RegistrationNativePlatformSecretWordOpen.agreement localImpl setup checks packet authenticated)).run before)) :
    ((result.1,result.2.1),(result.2.2.1,result.2.2.2)) ∈ support
      ((lower localImpl ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run (before.2.1,before.2.2)) := by
  have sourceEq : (close (RegistrationNativePlatformSecretWordOpen.agreement localImpl setup checks packet authenticated)).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (lower localImpl ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run (before.2.1,before.2.2) := by
    simp only [RegistrationNativePlatformLorSourceRetainedControl.close,RegistrationNativePlatformSecretWordOpen.agreement,
      RegistrationNativePlatformLorSourceRetainedCore.lower,StateT.run,Functor.map_map]
  rw [sourceEq,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  exact called

/-- The same selected accept stores its own marked collector, ciphertext and opaque descriptor. -/
theorem accept_retained (verify : MldsaTranscriptAuth.Verify) (reserve : StateT Private ProbComp Bool)
    (reserve_phase : ∀ before result, result ∈ support (reserve.run before) → (kem result.2).2 = (kem before).2)
    (packet : registration.InitPacket) (before after : State Private) (handle : Nat)
    (initial : (kem before.2.2).2 = none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map
      (fun keys => keys.2.pqKey) = some publicKey)
    (supported : (.ok (some handle),after) ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.accept localImpl reserve setup checks verify packet)).run before)) :
    ∃ (ready : ServerReady) (authenticated : registration.AuthenticatedInit)
      (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
      after.1.sessions[handle]? = some (some ready) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
      ready.agreement = ⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain,authenticated.binding⟩ ∧
      collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      collected.kem = Word.atom ∧ ready.reference.kem = Word.atom ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
        some (collected.plain.verified.identity,collected.plain.verified.keys) := by
  obtain ⟨pinned,pinAt,afterPinAt⟩ := RegistrationNativePlatformLorSourceRetainedControl.accept setup checks localImpl reserve packet verify before after handle supported
  have pinSource := lifted_support (RegistrationNativePlatformServerReferenceAccept.pin effects before.1.pin) before pinned pinAt
  have pinMarker := pin_phase setup selected pairs publicKey challenge implementation kem input contract before.1.pin before.2.2 (pinned.1,pinned.2.2.2) pinSource
  obtain ⟨pin,events,authenticated,checked,_pinReply,authenticatedAt,checkedReply,afterAuthenticationAt⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_pin setup checks localImpl reserve packet verify pinned.1 pinned.2 after handle afterPinAt
  have authSource := lifted_support (simulateQ effects (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)) pinned.2 checked authenticatedAt
  have authMarker := effects_phase setup selected pairs publicKey challenge implementation kem input contract
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet) pinned.2.2.2 (checked.1,checked.2.2.2) authSource
  rw [checkedReply] at authSource
  have acceptedKeys := RegistrationNativeSecretWordTargetAuthentication.compiler_accepted (n := n) setup.source.crypto verify effects
    pin packet pinned.2.2.2 checked.2.2.2 events authenticated authSource
  have actualKey : (RegistrationRootInput.keys authenticated.registration).pqKey = publicKey := by
    rw [acceptedKeys,Option.map_some,Option.some.injEq] at matching
    exact matching
  obtain ⟨reserved,ready,agreed,reservedAt,_admitted,agreedAt,agreedReply,_retainedAt,stored⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_authentication setup checks localImpl reserve packet authenticated checked.2 after handle afterAuthenticationAt
  have reserveSource := lifted_support reserve checked.2 reserved reservedAt
  have reserveMarker := reserve_phase checked.2.2.2 (reserved.1,reserved.2.2.2) reserveSource
  have localAgreement := agreement_support setup checks implementation packet authenticated reserved.2 agreed agreedAt
  rw [agreedReply] at localAgreement
  obtain ⟨collected,middle,collectedAt,_rooted,echo,agreement⟩ :=
    RegistrationNativePlatformLorSourceRetainedCore.agreement_receipt setup checks selected pairs publicKey challenge implementation kem input contract
      packet authenticated reserved.2.1 agreed.2.1 (reserved.2.2.1,reserved.2.2.2) (agreed.2.2.1,agreed.2.2.2) ready localAgreement
  have fields := RegistrationNativePlatformLorSourceRetainedCore.collect_atom setup checks selected pairs publicKey challenge implementation kem input contract
    packet authenticated (reserved.2.2.1,reserved.2.2.2) middle collected
    (reserveMarker.trans (authMarker.trans (pinMarker.trans initial))) actualKey collectedAt
  refine ⟨ready,authenticated,collected,stored,echo,agreement,fields.1,fields.2.1,fields.2.2,?_,?_⟩
  · rw [echo]
    exact fields.2.2
  · rw [fields.1]
    exact acceptedKeys

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetained
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetained.accept_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetained.accept_retained
