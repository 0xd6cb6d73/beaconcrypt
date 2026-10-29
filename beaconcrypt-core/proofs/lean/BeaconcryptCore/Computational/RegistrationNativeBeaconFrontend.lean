-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsa
import BeaconcryptCore.Computational.RegistrationNativeKemBackend
import BeaconcryptCore.Computational.RegistrationNativeWire
import BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor
import BeaconcryptCore.Computational.RegistrationResponseExecutor
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor
import BeaconcryptCore.Computational.RegistrationBeaconSeed

/-! The concrete native Beacon family owns birth material and runs the extracted outgoing, response-authentication, agreement and first-record controllers. SDK source primitives and the indexed KEM service remain explicit. The real source owner keeps its scalar; the selected-scalar-free related-root view erases it separately. Finish consumes InitSent before inspecting its optional decoded packet, matching the runtime's terminal malformed-response behavior. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeWire (Wire)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

abbrev Trusted (n : Nat) (KemSK : Type) := EnvEffects n +
  RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK

inductive Phase where
  | fresh
  | freshWithCoins (oneTime : ScalarBytes)
  | initSent (pending : registration.BeaconPending) (oneTime : ScalarBytes)
  | established (completed : RegistrationBeaconSeed.PublicCompleted)
  | aborted (control : pqxdh.BeaconAborted)

/-- Real source state. KEM secret keys remain solely in the indexed private service. -/
structure Owner (mldsaSource : RegistrationNativeMldsa.Source) where
  pin : session.ServerAuthenticationPin
  mldsa : RegistrationNativeMldsa.Credential mldsaSource
  identitySeed : IdentitySeed
  prekeyScalar : ScalarBytes
  prekeyPublic : Std.Array U8 32#usize
  kemHandle : Nat
  kemPublic : PqxdhKemIndCca.MlKem768PublicKey
  worldOwner : Nat
  phase : Phase
  edHistory : PqxdhJointIdentity.History

abbrev State (mldsaSource : RegistrationNativeMldsa.Source) := List (Owner mldsaSource)
abbrev M (n : Nat) (KemSK : Type) (mldsaSource : RegistrationNativeMldsa.Source) (Auxiliary Result : Type) :=
  StateT (State mldsaSource) (StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK))) Result

def effect {mldsaSource : RegistrationNativeMldsa.Source} (query : (EnvEffects n).Domain) :
    M n KemSK mldsaSource Auxiliary ((EnvEffects n).Range query) :=
  StateT.lift (StateT.lift ((Trusted n KemSK).query (.inl query)))

def kem {mldsaSource : RegistrationNativeMldsa.Source}
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    M n KemSK mldsaSource Auxiliary
      ((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Range query) :=
  StateT.lift (StateT.lift ((Trusted n KemSK).query (.inr query)))

def sample {mldsaSource : RegistrationNativeMldsa.Source} {Result : Type} (work : ProbComp Result) :
    M n KemSK mldsaSource Auxiliary Result :=
  simulateQ (fun query => effect (.inl query)) work

def updateEnv {mldsaSource : RegistrationNativeMldsa.Source} (change : EnvState Auxiliary → EnvState Auxiliary) :
    M n KemSK mldsaSource Auxiliary Unit := StateT.lift (modify change)

def put {mldsaSource : RegistrationNativeMldsa.Source} (index : Nat) (owner : Owner mldsaSource) :
    M n KemSK mldsaSource Auxiliary Unit := modify (fun before => before.set index owner)

def updatePhase {mldsaSource : RegistrationNativeMldsa.Source} (index : Nat) (phase : Phase) :
    M n KemSK mldsaSource Auxiliary Unit := modify fun owners => match owners[index]? with
  | none => owners
  | some current => owners.set index { current with phase }

/-- A signing receipt updates only the current stored owner's chronological history, before any native resume or writer can reject. -/
def logEd {mldsaSource : RegistrationNativeMldsa.Source} (index : Nat)
    (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    M n KemSK mldsaSource Auxiliary Unit := modify fun owners => match owners[index]? with
  | none => owners
  | some current => owners.set index { current with edHistory := current.edHistory ++ [.signed message signature] }

def pqArray (bytes : PqxdhKemIndCca.MlKem768PublicKey) : Std.Array U8 1184#usize :=
  ⟨bytes.toList.map BeaconcryptCore.Refinement.ProtocolComposition.concreteByte, by simp⟩

def hash {mldsaSource : RegistrationNativeMldsa.Source} (request : registration.HashRequest) :
    M n KemSK mldsaSource Auxiliary CtxRomAuth.CtxDigest :=
  effect (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))

/-- The exact suffix after all constructor preflights and ordinary identity draws. -/
def appendBorn (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (keyId : U64)
    (pin : session.ServerAuthenticationPin) (credentials : RegistrationNativeMldsa.Credential mldsaSource)
    (identity : IdentitySeed) (prekey : ScalarBytes) :
    M n KemSK mldsaSource Auxiliary (RustM (Option Nat)) := do
  let born ← kem (.inr (.inl .create))
  let worldOwner ← effect (.inr (.appendOwner keyId edPin .fresh))
  let owners ← get
  let owner : Owner mldsaSource := ⟨pin, credentials, identity, prekey,
    PqxdhRootTableInitialization.rootArray (setup.dh.publicKey prekey), born.1, born.2, worldOwner, .fresh, []⟩
  set (owners ++ [owner])
  pure (.ok (some owners.length))

/-- Source-only constructor prefix, retained privately until indexed key creation. -/
structure Prepared (mldsaSource : RegistrationNativeMldsa.Source) where
  credentials : RegistrationNativeMldsa.Credential mldsaSource
  pin : session.ServerAuthenticationPin
  identity : IdentitySeed
  prekey : ScalarBytes

noncomputable def prepare (mldsaSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    M n KemSK mldsaSource Auxiliary (RustM (Option (Prepared mldsaSource))) := do
  let generated ← sample (RegistrationNativeMldsa.generate mldsaSource)
  match generated with
  | none => pure (.ok none)
  | some credentials =>
    match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok pending => match pending.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok request => do
        let digest ← hash request
        match pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
        | .fail error => pure (.fail error)
        | .div => pure .div
        | .ok .None => pure (.ok none)
        | .ok (.Some pin) => do
          let identity ← sample PqxdhJointIdentity.sampleSeed
          let prekey ← sample PqxdhJointGapDh.sampleScalar
          pure (.ok (some ⟨credentials, pin, identity, prekey⟩))

/-- Actual constructor order: ML keygen, native pin fingerprint, identity, prekey, indexed KEM keygen, then public owner allocation. -/
noncomputable def create (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    M n KemSK mldsaSource Auxiliary (RustM (Option Nat)) := do
  match ← prepare mldsaSource edPin mlPin keyId with
  | .ok (some prepared) =>
      appendBorn setup mldsaSource edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey
  | .ok none => pure (.ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div

noncomputable def outgoing (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner mldsaSource) : QueryImpl RegistrationBeaconInitExecutor.Spec (M n KemSK mldsaSource Auxiliary)
  | .inl (.hash request) => hash request
  | .inl (.sign request payload digest) => do
      let reply ← sample (RegistrationNativeMldsa.owned mldsaSource owner.mldsa request)
      updateEnv fun env => { env with receipts := env.receipts ++
        [⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes reply⟩, digest⟩] }
      pure reply
  | .inr request => by
      classical
      exact if request.public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519 then
        do
          let message := TranscriptAuthParts.absSlice request.message
          let signature := setup.joint.sign owner.identitySeed message
          logEd index message signature
          pure (RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ message)))
      else pure .None

def inputs (setup : Setup base KemSK) {mldsaSource : RegistrationNativeMldsa.Source} (owner : Owner mldsaSource) :
    pqxdh.BeaconStartInputs :=
  ⟨PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
    owner.prekeyPublic, pqArray owner.kemPublic⟩

noncomputable def bundle (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) : M n KemSK mldsaSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
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
      let oneTime ← match supplied with
        | some scalar => pure scalar
        | none => sample PqxdhJointGapDh.sampleScalar
      let published ← simulateQ (outgoing setup mldsaSource index owner)
        (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
      match published with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
        updatePhase index (.initSent finished.pending oneTime)
        let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
        pure (.ok (some finished.encoded))

noncomputable def authentication (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (M n KemSK mldsaSource Auxiliary)
  | .hash request => do
      let digest ← hash request
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa mldsaSource.verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request)

/-- Ordinary non-KEM operations run on the actual owner's local state; only indexed KEM operations leave for the private service. -/
noncomputable def primitive (setup : Setup base KemSK) {mldsaSource : RegistrationNativeMldsa.Source}
    (owner : Owner mldsaSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (M n KemSK mldsaSource Auxiliary) := fun query =>
  simulateQ (fun lower => match lower with
    | .inl other => sample (Prod.fst <$>
        (RegistrationNativeKemBackend.beaconOther setup owner.prekeyScalar other).run
          ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩)
    | .inr other => kem (.inr other))
    (RegistrationNativeKemInterface.beacon (some owner.kemHandle) query)

noncomputable def agreementCore (setup : Setup base KemSK) {mldsaSource : RegistrationNativeMldsa.Source}
    (owner : Owner mldsaSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (M n KemSK mldsaSource Auxiliary)
  | .convertPublic key => primitive setup owner oneTime (.convertPublic key)
  | .convertSecret role => primitive setup owner oneTime (.convertSecret role)
  | .generate role => primitive setup owner oneTime (.generate role)
  | .encapsulate key => primitive setup owner oneTime (.encapsulate key)
  | .decapsulate ciphertext => primitive setup owner oneTime (.decapsulate ciphertext)
  | .dh request => primitive setup owner oneTime (.dh request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

noncomputable def agreement (setup : Setup base KemSK) {mldsaSource : RegistrationNativeMldsa.Source}
    (owner : Owner mldsaSource) (oneTime : ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (M n KemSK mldsaSource Auxiliary) := fun query => do
  updateEnv fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query }
  agreementCore setup owner oneTime query

private noncomputable def recordCore (setup : Setup base KemSK) {mldsaSource : RegistrationNativeMldsa.Source}
    (wire : Wire) : QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK mldsaSource Auxiliary)
  | .hash transcript => do
      let digest ← hash (.Single (Std.Array.to_slice transcript.bytes))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | other => sample (Prod.fst <$>
      (RegistrationRecordPrimitives.implementation setup.source wire.frameWrite other).run ((), ∅))

noncomputable def record (setup : Setup base KemSK) {mldsaSource : RegistrationNativeMldsa.Source}
    (wire : Wire) : QueryImpl RegistrationRecordPrimitives.Spec (M n KemSK mldsaSource Auxiliary) := fun query => do
  updateEnv fun env => { env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query] }
  recordCore setup wire query

def abort {mldsaSource : RegistrationNativeMldsa.Source} (owner : Owner mldsaSource) : M n KemSK mldsaSource Auxiliary Unit := do
  let _ ← effect (.inr (.advanceOwner owner.worldOwner .aborted))
  pure ()

/-- InitSent is consumed before packet admission. Every later failure keeps that terminal state and all reached crypto/cache effects. -/
noncomputable def finish (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK mldsaSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => match owner.phase with
    | .initSent pending oneTime => do
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
        updatePhase index (.aborted aborted)
        let authenticated ← simulateQ (authentication setup mldsaSource)
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
              let shell : BeaconShell := ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩
              let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known established.kernel)))
              if installed then
                updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
                pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
              else abort owner *> pure (.ok none)
          | .ok _ => abort owner *> pure (.ok none)
    | _ => pure (.ok none)

end BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
