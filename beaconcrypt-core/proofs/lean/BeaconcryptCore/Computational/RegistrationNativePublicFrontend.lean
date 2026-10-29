-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwners
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemRouting
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler

/-! The public reference frontend is one adaptive client for both native roles and the unchanged original secrecy ledger. Its state has no selected Server identity seed, selected Beacon prekey scalar, prepared root, generated hidden seed or concrete protected kernel. Every native parsed accept is counted before authentication; actual local constructor/publication operations retain their effects. This executable client does not itself assert a source-game equality or an alias-reuse security bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects RecordQuery)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev LocalSpec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK
abbrev RoutedKem (KemSK : Type) := RegistrationNativeKemInterface.Spec
  (RegistrationNativeKemInterface.OtherSpec + RegistrationNativeKemInterface.EncapsulationSpec) KemSK
abbrev RoutedLocalSpec (n : Nat) (KemSK : Type) := RegistrationServerReferenceRoot.PrepareSpec +
  (RegistrationNativePairedServerService.PublicSpec n + RoutedKem KemSK)
abbrev Spec (n : Nat) (KemSK : Type) := RoutedLocalSpec n KemSK + PqxdhRecordLiftInterface.RecordSpec .O

structure State (source : RegistrationNativeMldsa.Source) where
  server : RegistrationServerMaterialFrontend.State
  beacons : RegistrationNativePublicOwners.State source
  environment : RegistrationServerReferenceCompiler.Environment
  parsedAccepts : Nat

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Value : Type) :=
  StateT (State source) (OracleComp (Spec n KemSK)) Value

def liftRoutedKem : QueryImpl (RoutedKem KemSK) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl (.inr (.inr query)))

def liftLocal (selected : Bool) : QueryImpl (LocalSpec n KemSK) (OracleComp (Spec n KemSK))
  | .inl message => (Spec n KemSK).query (.inl (.inl message))
  | .inr (.inl query) => (Spec n KemSK).query (.inl (.inr (.inl query)))
  | .inr (.inr query) => simulateQ liftRoutedKem (RegistrationNativeKemRouting.route selected query)

def liftServer : QueryImpl (RegistrationServerReferenceCompiler.Spec n) (OracleComp (LocalSpec n KemSK))
  | .inl query => (LocalSpec n KemSK).query (.inl query)
  | .inr query => (LocalSpec n KemSK).query (.inr (.inl query))

def effect (query : (EnvEffects n).Domain) : OracleComp (Spec n KemSK) ((EnvEffects n).Range query) :=
  liftLocal false (.inr (.inl (.inr (.inr query))))

def server {source : RegistrationNativeMldsa.Source} {Result : Type}
    (work : RegistrationServerReferenceCompiler.M n Result) : M n KemSK source Result := fun before =>
  (fun result => (result.1.1, { before with server := result.1.2, environment := result.2 })) <$>
    simulateQ (liftLocal false ∘ₛ liftServer) ((work.run before.server).run before.environment)

def serverOpen {source : RegistrationNativeMldsa.Source} {Result : Type} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Result) : M n KemSK source Result := fun before =>
  (fun result => (result.1.1, { before with server := result.1.2, environment := result.2 })) <$>
    simulateQ (liftLocal selected) ((work.run before.server).run before.environment)

def beacon {source : RegistrationNativeMldsa.Source} {Result : Type}
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Result) :
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

/-- Source execution and public owner handles remain distinct from selected family and private KEM handles. -/
noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) : QueryImpl TypedSpec (M n KemSK source)
  | .inl coin => StateT.lift (effect (.inl coin))
  | .inr (.create edPin mlPin keyId) => beacon
      (RegistrationNativePublicOwners.create setup source selectedOwner publicPrekey edPin mlPin keyId)
  | .inr (.bundle owner) => beacon
      (RegistrationNativePublicOwners.bundle setup source wire selectedOwner publicPrekey owner)
  | .inr (.accept packet) => do
      let before ← get
      modify fun current => { current with parsedAccepts := current.parsedAccepts + 1 }
      serverOpen (decide (before.parsedAccepts = selectedAccept))
        (RegistrationServerOpenReferenceCompiler.accept setup checks source.verify packet)
  | .inr (.build handle application) => serverOpen false
      (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)
  | .inr (.finish owner packet) => beacon (RegistrationNativePublicOwners.finish setup source owner packet)
  | .inr (.hmac key bytes) => pure (setup.hmac.eval key bytes)
  | .inr (.hash bytes) => StateT.lift (effect (.inr (.hash bytes)))
  | .inr (.serverSend keyId plaintext) => record (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => record (.inl (.inr raw))
  | .inr (.beaconSend owner plaintext) => record (.inr (owner, .inl plaintext))
  | .inr (.beaconRaw owner raw) => record (.inr (owner, .inr raw))

/-- The original hidden-bit/fresh-message controller and complete ML-pin-aware transcript execute above the reference frontend without alteration. -/
noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source) :
    OracleComp (Spec n KemSK) ((Value × RegistrationNativeLedger.State) × State source) :=
  (simulateQ (handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before

end BeaconcryptCore.Computational.RegistrationNativePublicFrontend
