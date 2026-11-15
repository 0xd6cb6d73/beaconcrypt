-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconMaterial

/-! The executable arbitrary-pin Beacon compiler retains the actual terminal lifecycle and mandatory response authentication. Its indexed decapsulation returns an opaque word; all public metadata, DH operands and chronological environment effects remain the original native data. No candidate shared-secret value is an argument to this compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCompiler
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare)
open RegistrationNativeSecretWordMessage (BeaconReady)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev M (n : Nat) (KemSK Auxiliary Value : Type) := StateT (EnvState Auxiliary) (OracleComp (LocalSpec n KemSK)) Value

noncomputable def ordinaryPrefix (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :=
  (RegistrationNativeSecretWordServerSource.realize RegistrationNativeSecretWordMessage.zero).mapStateTBase
    (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.backend (n := n) (Auxiliary := Auxiliary) setup owner oneTime)
        authenticated) RegistrationBeaconReferenceCompiler.visit)

noncomputable def prefixImpl (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    QueryImpl (RegistrationNativeSecretWordBeaconCollect.Spec Unit Unit Unit Unit registration.AuthenticatedResponse)
      (M n KemSK Auxiliary)
  | .decapsulate ciphertext _ => fun before =>
      (fun reply => (reply, { before with requests := before.requests ++
        RegistrationWorldAgreement.recorded (.decapsulate (.Some ciphertext)) })) <$>
        RegistrationNativeSecretWordInterface.localKem
          (.inr (.inl (.decapsulate owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext))))
  | .decode raw => ordinaryPrefix setup owner oneTime authenticated (.decode raw)
  | .ciphertext response => ordinaryPrefix setup owner oneTime authenticated (.ciphertext response)
  | .ephemeral response => ordinaryPrefix setup owner oneTime authenticated (.ephemeral response)
  | .serverIdentity response => ordinaryPrefix setup owner oneTime authenticated (.serverIdentity response)
  | .publicConversion key => ordinaryPrefix setup owner oneTime authenticated (.publicConversion key)
  | .privateConversion identity => ordinaryPrefix setup owner oneTime authenticated (.privateConversion identity)
  | .dhPair pair key => ordinaryPrefix setup owner oneTime authenticated (.dhPair pair key)
  | .dhIdentity identity key => ordinaryPrefix setup owner oneTime authenticated (.dhIdentity identity key)
  | .selected point => ordinaryPrefix setup owner oneTime authenticated (.selected point)
  | .assignedId response => ordinaryPrefix setup owner oneTime authenticated (.assignedId response)
  | .eraseShared secrets => ordinaryPrefix setup owner oneTime authenticated (.eraseShared secrets)

noncomputable def collect (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    M n KemSK Auxiliary (Option (RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)) :=
  simulateQ (prefixImpl setup owner oneTime authenticated)
    (RegistrationNativeSecretWordBeaconPrepare.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])

/-- This actual callback interpreter restores the complete ordered preparation and every reached environment field. -/
theorem collect_source (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    simulateQ (prefixImpl (n := n) (Auxiliary := Auxiliary) setup owner oneTime authenticated ∘ₛ
      RegistrationNativeSecretWordBeaconCollect.realize candidate)
      (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) =
      Option.map (RegistrationNativeSecretWordBeaconPrepare.eval candidate) <$> collect setup owner oneTime authenticated :=
  RegistrationNativeSecretWordBeaconPrepare.prepare_program (completedBinding := authenticated.binding) (prefixImpl setup owner oneTime authenticated) candidate
    authenticated.control () () () []

noncomputable def agreement (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    M n KemSK Auxiliary (RustM (Option BeaconReady)) := do
  match ← collect setup owner oneTime authenticated with
  | none => pure (.ok none)
  | some pending => StateT.lift (simulateQ prepare (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))

noncomputable def finishPreparation (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) : StateT (SelectedOwner source) (M n KemSK Auxiliary) (RustM (Option BeaconReady)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending oneTime =>
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
          set ({ owner with phase := .aborted aborted } : SelectedOwner source)
          let accepted ← StateT.lift (StateT.lift (simulateQ effect
            (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
              (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some packet => .Some packet)))))
          match accepted with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.Err _) => pure (.ok none)
          | .ok (.Ok authenticated) => StateT.lift (agreement setup owner oneTime authenticated)
  | _ => pure (.ok none)


noncomputable def complete (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {source : RegistrationNativeMldsa.Source} (owner : SelectedOwner source) (ready : BeaconReady) :
    StateT (SelectedOwner source) (M n KemSK Auxiliary) (RustM (Option Pqxdh.Bytes)) := fun current env =>
  simulateQ RegistrationNativeSecretWordInterface.paired
    (((RegistrationNativeSecretWordBeaconMaterial.complete hkdf owner ready).run current).run env)

def abort {source : RegistrationNativeMldsa.Source} (owner : SelectedOwner source) :
    StateT (SelectedOwner source) (M n KemSK Auxiliary) Unit := do
  let _ ← StateT.lift (StateT.lift (effect (.inr (.advanceOwner owner.worldOwner .aborted))))
  pure ()

noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) : StateT (SelectedOwner source) (M n KemSK Auxiliary) (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending _ =>
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok _ => do
          let prepared ← finishPreparation setup source packet
          match prepared with
          | .fail error => abort owner *> pure (.fail error)
          | .div => abort owner *> pure .div
          | .ok none => abort owner *> pure (.ok none)
          | .ok (some ready) => complete setup.source owner ready
  | _ => pure (.ok none)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCompiler.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCompiler.collect_source
