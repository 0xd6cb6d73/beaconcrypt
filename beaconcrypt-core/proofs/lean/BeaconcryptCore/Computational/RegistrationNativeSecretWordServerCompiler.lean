-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial

/-! The concrete symbolic Server compiler runs the actual mandatory authentication, owned replay and allocation gates, native local callback programs and one-use completion. Its indexed encapsulation getter retains the ciphertext and opaque word separately. Only that word is carried into the private root-service address; no candidate shared-secret value is captured by the executable client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare demand)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationNativeSecretWordServerCollect (Input)
open PqxdhJointIdentity (PeerEncoding)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev M (n : Nat) (KemSK Value : Type) := StateT ServerState
  (StateT Environment (OracleComp (LocalSpec n KemSK))) Value

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT Environment (OracleComp (LocalSpec n KemSK))) :=
  fun query before => simulateQ effect
    ((RegistrationWorldAgreementCompiler.compiler setup.source
      (RegistrationServerRoleBackend.localBackend setup checks) query).run before)

def visit (point : PqxdhBeaconPhase2Preparation.Word32) : StateT Environment (OracleComp (LocalSpec n KemSK)) Unit :=
  fun before => pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] })

noncomputable def ordinaryPrefix (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PeerEncoding)
      (StateT Environment (OracleComp (LocalSpec n KemSK))) :=
  PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (backend setup checks)) visit

noncomputable def prefixImpl (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl (RegistrationNativeSecretWordServerCollect.Spec registration.InitPacket Unit PeerEncoding)
      (StateT Environment (OracleComp (LocalSpec n KemSK)))
  | .encapsulate key => fun before =>
      let nativeKey := RegistrationAgreementRoot.pqArray key
      let checkedKey := RegistrationRootInput.pqKey nativeKey
      if checks.kemKey checkedKey then
        (fun reply => (some (PqxdhAcceptedRegistration.ciphertextArray reply.1, reply.2),
          { before with requests := before.requests ++
            RegistrationWorldAgreement.recorded (.encapsulate (.Some nativeKey)) })) <$>
          RegistrationNativeSecretWordInterface.localKem (.inr (.inr checkedKey))
      else pure (none, { before with requests := before.requests ++
        RegistrationWorldAgreement.recorded (.encapsulate (.Some nativeKey)) })
  | .decode raw => (ordinaryPrefix setup checks) (.decode raw)
  | .identity reader => (ordinaryPrefix setup checks) (.identity reader)
  | .identityPoint key => (ordinaryPrefix setup checks) (.identityPoint key)
  | .pqField reader => (ordinaryPrefix setup checks) (.pqField reader)
  | .preField reader => (ordinaryPrefix setup checks) (.preField reader)
  | .oneField reader => (ordinaryPrefix setup checks) (.oneField reader)
  | .verify key signed => (ordinaryPrefix setup checks) (.verify key signed)
  | .registrationStatus identifier => (ordinaryPrefix setup checks) (.registrationStatus identifier)
  | .reserveRegistration => (ordinaryPrefix setup checks) (.reserveRegistration)
  | .parseDh point => (ordinaryPrefix setup checks) (.parseDh point)
  | .generate => (ordinaryPrefix setup checks) (.generate)
  | .parseKem key => (ordinaryPrefix setup checks) (.parseKem key)
  | .publicConversion key => (ordinaryPrefix setup checks) (.publicConversion key)
  | .privateConversion => (ordinaryPrefix setup checks) (.privateConversion)
  | .staticDh point => (ordinaryPrefix setup checks) (.staticDh point)
  | .ephemeralDh secret point => (ordinaryPrefix setup checks) (.ephemeralDh secret point)

noncomputable def collect (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT Environment (OracleComp (LocalSpec n KemSK)) (Option (Input registration.InitPacket Unit PeerEncoding)) :=
  simulateQ (prefixImpl setup checks)
    (RegistrationNativeSecretWordServerCollect.collect (RegistrationRootInput.verified packet authenticated))

/-- The concrete symbolic prefix restores the original ordered collector under evaluation, retaining its complete environment and all callback effects. -/
theorem collect_source (setup : Setup base KemSK) (checks : Checks)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    simulateQ (prefixImpl (n := n) setup checks ∘ₛ RegistrationNativeSecretWordServerCollect.realize candidate)
      (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) =
      Option.map (RegistrationNativeSecretWordServerCollect.eval candidate) <$> collect setup checks packet authenticated :=
  RegistrationNativeSecretWordServerCollect.collect_program (prefixImpl setup checks) candidate
    (RegistrationRootInput.verified packet authenticated)

noncomputable def agreement (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M n KemSK (RustM (Option ServerReady)) := do
  match ← StateT.lift (collect setup checks packet authenticated) with
  | none => pure (.ok none)
  | some input => StateT.lift (StateT.lift (simulateQ prepare
      (RegistrationNativeSecretWordServerRoot.client authenticated.binding input)))

def retain (ready : ServerReady) : M n KemSK (RustM (Option Nat)) := fun before =>
  match RegistrationNativeSecretWordServerMaterial.retain ready before with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, after)

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M n KemSK (RustM (Option Nat)) := do
  let before ← get
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else if checks.reserveRegistration then do
    let accepted ← agreement setup checks packet authenticated
    match accepted with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok none => pure (.ok none)
    | .ok (some ready) => retain ready
  else pure (.ok none)

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : M n KemSK (RustM (Option Nat)) := do
  let before ← get
  let checked ← StateT.lift (StateT.lift (simulateQ effect
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet)))
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks packet authenticated
  | .ok _ => pure (.ok none)

def service (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n)
      (StateT Environment (OracleComp (LocalSpec n KemSK)))
  | .inl reference => StateT.lift (demand reference)
  | .inr query => RegistrationNativeCommonCompiler.common effect hkdf wire.frameWrite sign query

noncomputable def build (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) : M n KemSK RegistrationNativeSecretWordServerMaterial.Result := fun before =>
  simulateQ (service hkdf wire sign)
    ((RegistrationNativeSecretWordServerMaterial.build wire checks.reservePeer handle application).run before)

/-- Replay rejection precedes every symbolic getter, preparation and material query. -/
theorem replay_rejected (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (replayed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env) = pure ((.ok none, before), env) := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, replayed, ite_true]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler.collect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler.replay_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler.replay_rejected
