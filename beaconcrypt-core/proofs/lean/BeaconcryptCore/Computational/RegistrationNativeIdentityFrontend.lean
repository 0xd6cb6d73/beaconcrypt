-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBirth
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner

/-! Native Beacon operations with generated Ed25519 credentials held behind indexed joint signing/static-DH services. The executable owner state has no Ed25519 seed or converted secret. All source controller requests, optional failures, signing attempts and phase updates remain explicit; ordinary prekey, one-time and KEM material is independent auxiliary state for the joint-EUF reduction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeBeaconFrontend (Phase pqArray)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeWire (Wire)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

structure Owner (source : RegistrationNativeMldsa.Source) where
  pin : session.ServerAuthenticationPin
  identity : RegistrationNativeIdentityInterface.Credential
  prekeyScalar : ScalarBytes
  prekeyPublic : Std.Array U8 32#usize
  kemHandle : Nat
  kemPublic : PqxdhKemIndCca.MlKem768PublicKey
  worldOwner : Nat
  phase : Phase
  edHistory : History

abbrev State (source : RegistrationNativeMldsa.Source) := List (Owner source)
abbrev Ambient (n : Nat) (KemSK : Type) := RegistrationNativeBeaconFrontend.Trusted n KemSK
abbrev Trusted (n : Nat) (KemSK : Type) := RegistrationNativeIdentityInterface.Spec (Ambient n KemSK)
abbrev M (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (State source) (StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)))

def ambientLift : QueryImpl (Ambient n KemSK) (OracleComp (Trusted n KemSK)) :=
  fun query => (Trusted n KemSK).query (.inl query)

def effect {source : RegistrationNativeMldsa.Source} (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    M n KemSK Auxiliary source ((PqxdhRecordLiftInterface.EnvEffects n).Range query) :=
  StateT.lift (StateT.lift ((Trusted n KemSK).query (.inl (.inl query))))

def kem {source : RegistrationNativeMldsa.Source}
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    M n KemSK Auxiliary source
      ((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Range query) :=
  StateT.lift (StateT.lift ((Trusted n KemSK).query (.inl (.inr query))))

def sample {source : RegistrationNativeMldsa.Source} (work : ProbComp Value) : M n KemSK Auxiliary source Value :=
  simulateQ (fun query => effect (.inl query)) work

def updateEnv {source : RegistrationNativeMldsa.Source} (change : EnvState Auxiliary → EnvState Auxiliary) :
    M n KemSK Auxiliary source Unit := StateT.lift (modify change)

def updatePhase {source : RegistrationNativeMldsa.Source} (index : Nat) (phase : Phase) : M n KemSK Auxiliary source Unit :=
  modify fun owners => match owners[index]? with
    | none => owners
    | some current => owners.set index { current with phase }

def logEd {source : RegistrationNativeMldsa.Source} (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) : M n KemSK Auxiliary source Unit :=
  modify fun owners => match owners[index]? with
    | none => owners
    | some current => owners.set index { current with edHistory := current.edHistory ++ [.signed message signature] }

def hash {source : RegistrationNativeMldsa.Source} (request : registration.HashRequest) :
    M n KemSK Auxiliary source CtxRomAuth.CtxDigest :=
  effect (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))

def restore {source : RegistrationNativeMldsa.Source} (seed : IdentitySeed) (owner : Owner source) :
    RegistrationNativeBeaconFrontend.Owner source :=
  ⟨owner.pin, seed, owner.prekeyScalar, owner.prekeyPublic, owner.kemHandle,
    owner.kemPublic, owner.worldOwner, owner.phase, owner.edHistory⟩

def dummyIdentity : IdentitySeed := ⟨List.replicate 32 0, by simp⟩

/-- This adapter is used for the existing owner-independent primitive/record callbacks; its executable inputs contain only a fixed dummy identity. -/
noncomputable def liftOld {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : M n KemSK Auxiliary source Value :=
  StateT.lift fun env => simulateQ ambientLift ((Prod.fst <$> work.run []).run env)

structure Prepared (source : RegistrationNativeMldsa.Source) where
  pin : session.ServerAuthenticationPin
  identity : RegistrationNativeIdentityInterface.Credential
  prekey : ScalarBytes

noncomputable def prepare (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    M n KemSK Auxiliary source (RustM (Option (Prepared source))) := do
  match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok pin =>
      let identity ← StateT.lift (StateT.lift (RegistrationNativeIdentityInterface.create (Ambient n KemSK)))
      match identity with
      | none => pure (.ok none)
      | some identity => do
          let prekey ← sample PqxdhJointGapDh.sampleScalar
          pure (.ok (some ⟨pin, identity, prekey⟩))

noncomputable def create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    M n KemSK Auxiliary source (RustM (Option Nat)) := do
  match ← prepare source edPin mlPin keyId with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok none => pure (.ok none)
  | .ok (some prepared) => do
      let born ← kem (.inr (.inl .create))
      let worldOwner ← effect (.inr (.appendOwner keyId edPin .fresh))
      let owners ← get
      let owner : Owner source := ⟨prepared.pin, prepared.identity, prepared.prekey,
        PqxdhRootTableInitialization.rootArray (setup.dh.publicKey prepared.prekey), born.1, born.2, worldOwner, .fresh, []⟩
      set (owners ++ [owner])
      pure (.ok (some owners.length))

noncomputable def outgoing (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) : QueryImpl RegistrationBeaconInitExecutor.Spec (M n KemSK Auxiliary source)
  | .inl (.hash request) => hash request
  | .inl (.sign _ _ _) => pure .None
  | .inr request => by
      classical
      exact if request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519 then do
        let message := TranscriptAuthParts.absSlice request.message
        let signature ← StateT.lift (StateT.lift
          (RegistrationNativeIdentityInterface.sign (Ambient n KemSK) owner.identity message))
        match signature with
        | none => pure .None
        | some signature => do
            logEd index message signature
            pure (RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ message)))
      else pure .None

def inputs {source : RegistrationNativeMldsa.Source} (owner : Owner source) : pqxdh.BeaconStartInputs :=
  ⟨PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519, owner.prekeyPublic, pqArray owner.kemPublic⟩

noncomputable def bundle (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) : M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner =>
      let selected : Option (Option ScalarBytes) := match owner.phase with
        | .fresh => some none
        | .freshWithCoins scalar => some (some scalar)
        | _ => none
      match selected with
      | none => pure (.ok none)
      | some supplied => do
          let oneTime ← match supplied with | some scalar => pure scalar | none => sample PqxdhJointGapDh.sampleScalar
          let published ← simulateQ (outgoing setup source index owner)
            (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs owner)
              ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
          match published with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.Err _) => pure (.ok none)
          | .ok (.Ok finished) => do
              updatePhase index (.initSent finished.pending oneTime)
              let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
              pure (.ok (some finished.encoded))

noncomputable def authentication (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (M n KemSK Auxiliary source)
  | .hash request => do
      let digest ← hash request
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa source.verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request)

noncomputable def primitive (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : Owner source) (oneTime : ScalarBytes) : QueryImpl RegistrationAgreementShared.PrimitiveSpec (M n KemSK Auxiliary source)
  | .convertSecret .LocalIdentity => pure true
  | .dh request => match request.secret_role with
      | .LocalIdentity => StateT.lift (StateT.lift
          (RegistrationNativeIdentityCallbacks.dh (Ambient n KemSK) owner.identity request.public_key))
      | _ => liftOld (RegistrationNativeBeaconFrontend.primitive setup (restore dummyIdentity owner) oneTime (.dh request))
  | query => liftOld (RegistrationNativeBeaconFrontend.primitive setup (restore dummyIdentity owner) oneTime query)

noncomputable def agreementCore (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : Owner source) (oneTime : ScalarBytes) : QueryImpl RegistrationAgreementExecutor.Spec (M n KemSK Auxiliary source)
  | .convertPublic key => primitive setup owner oneTime (.convertPublic key)
  | .convertSecret role => primitive setup owner oneTime (.convertSecret role)
  | .generate role => primitive setup owner oneTime (.generate role)
  | .encapsulate key => primitive setup owner oneTime (.encapsulate key)
  | .decapsulate ciphertext => primitive setup owner oneTime (.decapsulate ciphertext)
  | .dh request => primitive setup owner oneTime (.dh request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

noncomputable def agreement (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : Owner source) (oneTime : ScalarBytes) : QueryImpl RegistrationAgreementExecutor.Spec (M n KemSK Auxiliary source) := fun query => do
  updateEnv fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query }
  agreementCore setup owner oneTime query

noncomputable def record (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (wire : Wire) : QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK Auxiliary source) :=
  fun query => liftOld (RegistrationNativeBeaconFrontend.record setup wire query)

def abort {source : RegistrationNativeMldsa.Source} (owner : Owner source) : M n KemSK Auxiliary source Unit := do
  let _ ← effect (.inr (.advanceOwner owner.worldOwner .aborted))
  pure ()

noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) : M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => match owner.phase with
    | .initSent pending oneTime => match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
          updatePhase index (.aborted aborted)
          let authenticated ← simulateQ (authentication setup source)
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
          match authenticated with
          | .fail error => abort owner *> pure (.fail error)
          | .div => abort owner *> pure .div
          | .ok (.Err _) => abort owner *> pure (.ok none)
          | .ok (.Ok accepted) => do
              let agreed ← simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
              match agreed with
              | .fail error => abort owner *> pure (.fail error)
              | .div => abort owner *> pure .div
              | .ok (.BeaconComplete completed) => do
                  let opened ← simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
                  match opened with
                  | .fail error => abort owner *> pure (.fail error)
                  | .div => abort owner *> pure .div
                  | .ok (.Err _) => abort owner *> pure (.ok none)
                  | .ok (.Ok established) => do
                      let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner
                        ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩ (.known established.kernel)))
                      if installed then
                        updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
                        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
                      else abort owner *> pure (.ok none)
              | .ok _ => abort owner *> pure (.ok none)
    | _ => pure (.ok none)

end BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend
