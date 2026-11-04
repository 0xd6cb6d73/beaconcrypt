-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompilerJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
/-! One adaptive public reference frontend shares persistent platform state across registration and all ongoing record routes. The source-derived Server build, indexed accept, corrected Beacon finish and actual stateful Init writer replace the earlier fixed-codec callbacks. This executable definition does not assert initialized source or hybrid-game equality. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeWire (Wire)
open PqxdhRecordLiftInterface (EnvEffects RecordQuery)
variable {n : Nat} {E Platform ι KemSK A : Type} {base : OracleSpec ι}

abbrev Spec (n : Nat) (KemSK : Type) := RegistrationNativePublicFrontend.Spec n KemSK + unifSpec
abbrev LocalSpec (n : Nat) (KemSK : Type) := RegistrationNativePublicFrontend.RoutedLocalSpec n KemSK + unifSpec
abbrev State (source : RegistrationNativeMldsa.Source) (Platform : Type) := RegistrationNativePublicFrontend.State source × Platform
abbrev Base (n : Nat) (KemSK Platform : Type) := StateT Platform (OracleComp (LocalSpec n KemSK))
abbrev M (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) := StateT (State source Platform) (OracleComp (Spec n KemSK))
abbrev LocalM (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) := StateT (State source Platform) (OracleComp (LocalSpec n KemSK))

def old : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl query)
def publicCoin : QueryImpl unifSpec (OracleComp (Spec n KemSK)) := fun query => (Spec n KemSK).query (.inr query)
def localCoin : QueryImpl unifSpec (OracleComp (LocalSpec n KemSK)) := fun query => (LocalSpec n KemSK).query (.inr query)
def localQuery (selected : Bool) : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (OracleComp (LocalSpec n KemSK))
  | .inl message => (LocalSpec n KemSK).query (.inl (.inl message))
  | .inr (.inl query) => (LocalSpec n KemSK).query (.inl (.inr (.inl query)))
  | .inr (.inr query) => simulateQ
      (fun routed => ((LocalSpec n KemSK).query (.inl (.inr (.inr routed))) : OracleComp (LocalSpec n KemSK) _))
      (RegistrationNativeKemRouting.route selected query)
def localHandler (selected : Bool) : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (Base n KemSK Platform) :=
  fun query => StateT.lift (localQuery selected query)
def effect (query : (EnvEffects n).Domain) : OracleComp (LocalSpec n KemSK) ((EnvEffects n).Range query) :=
  localQuery false (.inr (.inl (.inr (.inr query))))
def trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (Base n KemSK Platform) :=
  fun query => StateT.lift (simulateQ (localQuery false) (RegistrationBeaconReferenceCompiler.trustedLift query))
def platform (work : StateT Platform ProbComp A) : Base n KemSK Platform A :=
  fun previous => simulateQ localCoin (work.run previous)
def writer (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (Base n KemSK Platform) :=
  fun query => platform (implementation query)

def beacon {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State (Base n KemSK Platform) A) :
    LocalM n KemSK Platform source A := fun before =>
  (fun result => (result.1.1.1, ({ before.1 with beacons := result.1.1.2, environment := result.1.2 }, result.2))) <$>
    (((work.run before.1.beacons).run before.1.environment).run before.2)

def serverOpen {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformServerReferenceAccept.PublicM (Base n KemSK Platform) A) :
    LocalM n KemSK Platform source A := fun before =>
  (fun result => (result.1.1.1, ({ before.1 with server := result.1.1.2, environment := result.1.2 }, result.2))) <$>
    (((work.run before.1.server).run before.1.environment).run before.2)

def buildEmbedding : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n) (OracleComp (LocalSpec n KemSK))
  | .inl message => localQuery false (.inr (.inl (.inl message)))
  | .inr (.inl query) => effect query
  | .inr (.inr query) => localCoin query

def bundleBytes (reply : RustM (Option (alloc.vec.Vec U8))) : RustM (Option Pqxdh.Bytes) :=
  reply >>= fun optional => .ok (optional.map TranscriptAuthParts.absSlice)

def responseBytes (reply : RustM (Option (U64 × alloc.vec.Vec U8))) : RustM (Option (U64 × Pqxdh.Bytes)) :=
  reply >>= fun optional => .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2))

noncomputable def build [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (source : RegistrationNativeMldsa.Source) : LocalM n KemSK Platform source (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  (fun result => (responseBytes result.1.1,
    ({ before.1 with server := result.1.2, environment := { before.1.environment with receipts := result.2.1, recordRequests := [] } }, result.2.2))) <$>
    simulateQ buildEmbedding
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign implementation reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.server)).run
          (before.1.environment.receipts, before.2))

noncomputable def finish (setup : Setup base KemSK) (wire : Wire) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State (Base n KemSK Platform) (RustM (Option Pqxdh.Bytes)) :=
  fun owners env => match owners[index]? with
  | none => pure ((.ok none, owners), env)
  | some owner =>
      let work := ((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run env
      let changed := match owner.scalar with
        | none => work
        | some scalar => simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work
      (fun result => ((result.1.1, owners.set index { owner with view := result.1.2 }), result.2)) <$>
        simulateQ (localHandler false) changed

def embedLocal : QueryImpl (LocalSpec n KemSK) (OracleComp (Spec n KemSK))
  | .inl query => (Spec n KemSK).query (.inl (.inl query))
  | .inr coin => publicCoin coin

def executeLocal {source : RegistrationNativeMldsa.Source} (work : LocalM n KemSK Platform source A) : M n KemSK Platform source A :=
  fun before => simulateQ embedLocal (work.run before)

def platformFull (work : StateT Platform ProbComp A) : StateT Platform (OracleComp (Spec n KemSK)) A :=
  fun previous => simulateQ publicCoin (work.run previous)

noncomputable def record {source : RegistrationNativeMldsa.Source}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery) :
    M n KemSK Platform source ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) := fun before =>
  match query with
  | .inl (.inl send) => do
      let result ← old (.inr (.inl (.inl send)))
      let result ← (RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (reserve amount))
        (fun value => value.ciphertext.length) result).run before.2
      pure (result.1, (before.1, result.2))
  | .inl (.inr raw) => (fun result => (result, before)) <$> old (.inr (.inl (.inr raw)))
  | .inr (index, .inl plaintext) => match before.1.beacons[index]? with
      | none => pure (none, before)
      | some owner => do
        let result ← old (.inr (.inr (owner.view.worldOwner, .inl plaintext)))
        let result ← (RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (reserve amount))
          (fun value => value.ciphertext.length) result).run before.2
        pure (result.1, (before.1, result.2))
  | .inr (index, .inr raw) => match before.1.beacons[index]? with
      | none => pure (.None, before)
      | some owner => (fun result => (result, before)) <$>
          old (.inr (.inr (owner.view.worldOwner, .inr raw)))

noncomputable def handler [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (M n KemSK Platform source)
  | .inl coin => executeLocal (StateT.lift (effect (.inl coin)))
  | .inr (.create edPin mlPin keyId) => executeLocal (beacon
      (RegistrationNativePlatformPublicOwners.create trusted setup source selectedOwner publicPrekey edPin mlPin keyId))
  | .inr (.bundle index) =>
      executeLocal (bundleBytes <$>
        beacon (RegistrationNativePlatformPublicOwners.bundle trusted (writer implementation) setup source selectedOwner publicPrekey index))
  | .inr (.accept packet) => executeLocal (do
      let before ← get
      modify fun current => ({ current.1 with parsedAccepts := current.1.parsedAccepts + 1 }, current.2)
      serverOpen (RegistrationNativePlatformServerOpenControl.accept (localHandler (decide (before.1.parsedAccepts = selectedAccept)))
        (platform reserveRegistration) setup checks source.verify packet))
  | .inr (.build handle application) => executeLocal (build setup sign view failure allocation erased helper implementation reservePeer handle application source)
  | .inr (.finish index packet) => executeLocal (beacon (finish setup wire source index packet))
  | .inr (.hmac key bytes) => pure (setup.hmac.eval key bytes)
  | .inr (.hash bytes) => executeLocal (StateT.lift (effect (.inr (.hash bytes))))
  | .inr (.serverSend keyId plaintext) => record reserveFrame (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => record reserveFrame (.inl (.inr raw))
  | .inr (.beaconSend index plaintext) => record reserveFrame (.inr (index, .inl plaintext))
  | .inr (.beaconRaw index raw) => record reserveFrame (.inr (index, .inr raw))


noncomputable def run [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform) :
    OracleComp (Spec n KemSK) ((A × RegistrationNativeLedger.State) × State source Platform) :=
  (simulateQ (handler setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      serverKeyId bounds mode work)).run before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
