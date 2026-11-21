-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners

/-! The whole symbolic frontend runs the original raw secrecy compiler and ledger above the actual mandatory authentication, parsed-attempt routing, one-use Server tokens, mixed owner lifecycle and record commands. Only private references and indexed KEM secret replies carry opaque words. The executable state and handlers take no candidate shared-secret bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (PeerEncoding)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal)
open PqxdhRecordLiftInterface (RecordQuery)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (State source) (OracleComp (Spec n KemSK))

def effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    OracleComp (Spec n KemSK) ((PqxdhRecordLiftInterface.EnvEffects n).Range query) :=
  (Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr query)))))

def serverOpen {source : RegistrationNativeMldsa.Source} {Result : Type} (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Result) : M n KemSK source Result := fun before =>
  (fun result => (result.1.1, { before with server := result.1.2, environment := result.2 })) <$>
    simulateQ (liftLocal selected) ((work.run before.server).run before.environment)

def beacon {source : RegistrationNativeMldsa.Source} {Result : Type}
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Result) :
    M n KemSK source Result := fun before =>
  (fun result => (result.1.1, { before with beacons := result.1.2, environment := result.2 })) <$>
    simulateQ (liftLocal false) ((work.run before.beacons).run before.environment)

def record {source : RegistrationNativeMldsa.Source} (query : RecordQuery) :
    M n KemSK source ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) := fun before =>
  match query with
  | .inl query => (fun reply => (reply, before)) <$>
      ((Spec n KemSK).query (.inr (.inl query)) : OracleComp (Spec n KemSK) _)
  | .inr (owner, .inl plaintext) => match before.beacons[owner]? with
      | none => pure (none, before)
      | some owner => (fun reply => (reply, before)) <$>
          ((Spec n KemSK).query (.inr (.inr (owner.view.worldOwner, .inl plaintext))) : OracleComp (Spec n KemSK) _)
  | .inr (owner, .inr raw) => match before.beacons[owner]? with
      | none => pure (.None, before)
      | some owner => (fun reply => (reply, before)) <$>
          ((Spec n KemSK).query (.inr (.inr (owner.view.worldOwner, .inr raw))) : OracleComp (Spec n KemSK) _)

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (M n KemSK source)
  | .inl coin => StateT.lift (effect (.inl coin))
  | .inr (.create edPin mlPin keyId) => beacon
      (RegistrationNativeSecretWordOwners.create setup source selectedOwner publicPrekey edPin mlPin keyId)
  | .inr (.bundle owner) => beacon
      (RegistrationNativeSecretWordOwners.bundle setup source wire selectedOwner publicPrekey owner)
  | .inr (.accept packet) => do
      let before ← get
      modify fun current => { current with parsedAccepts := current.parsedAccepts + 1 }
      serverOpen (decide (before.parsedAccepts = selectedAccept))
        (RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet)
  | .inr (.build handle application) => serverOpen false
      (RegistrationNativeSecretWordServerCompiler.build setup.source wire checks sign handle application)
  | .inr (.finish owner packet) => beacon (RegistrationNativeSecretWordOwners.finish setup source owner packet)
  | .inr (.hmac key bytes) => pure (setup.hmac.eval key bytes)
  | .inr (.hash bytes) => StateT.lift (effect (.inr (.hash bytes)))
  | .inr (.serverSend keyId plaintext) => record (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => record (.inl (.inr raw))
  | .inr (.beaconSend owner plaintext) => record (.inr (owner, .inl plaintext))
  | .inr (.beaconRaw owner raw) => record (.inr (owner, .inr raw))

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    OracleComp (Spec n KemSK) ((Value × RegistrationNativeLedger.State) × State source) :=
  (simulateQ (handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before

/-- The original complete ledger runs directly above this concrete typed handler. -/
theorem run_compiled (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before =
      (simulateQ (handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
        (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before := rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend.run_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend.run_compiled
