-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView
/-! The candidate-independent Word frontend uses the corrected stateful public callbacks. Accept retains symbolic one-use root references, build executes the actual dynamic source compiler, and finish retains corrected assigned identifiers. Ordinary callbacks are the separate proved actual-source Word transport. No candidate root value is an input to this executable tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformSecretWordOrdinary (State M evaluate platform)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Base (n : Nat) (KemSK Platform : Type) := StateT Platform (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))

def serverOpen (work : RegistrationNativePlatformSecretWordOpen.PublicM (Base n KemSK Platform) A) : M n KemSK source Platform A :=
  fun before => (fun result => (result.1.1.1,
    ({ before.1 with server := result.1.1.2, environment := result.1.2 }, result.2))) <$>
      (((work.run before.1.server).run before.1.environment).run before.2)

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedAccept : Nat) (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket) :
    M n KemSK source Platform (RustM (Option Nat)) := do
  let before ← get
  modify fun current => ({ current.1 with parsedAccepts := current.1.parsedAccepts + 1 }, current.2)
  serverOpen (RegistrationNativePlatformSecretWordOpen.accept
    (wordLocal (decide (before.1.parsedAccepts = selectedAccept))) (platform reserve) setup checks source.verify packet)

noncomputable def build [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (source : RegistrationNativeMldsa.Source) : M n KemSK source Platform (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    ({ before.1 with server := result.1.2, environment := { before.1.environment with receipts := result.2.1, recordRequests := [] } }, result.2.2))) <$>
    simulateQ (RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativePlatformSecretWordBuild.wordEmbedding)
      (((RegistrationNativePlatformSecretWordBuild.body setup.source view failure allocation erased helper sign writer reserve handle application).run
        before.1.server).run (before.1.environment.receipts, before.2))

noncomputable def finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) : M n KemSK source Platform (RustM (Option Pqxdh.Bytes)) :=
  fun before => match before.1.beacons[index]? with
  | none => pure (.ok none, before)
  | some owner =>
    let work := ((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner.view).run before.1.environment
    let changed := match owner.scalar with
      | none => work
      | some scalar => simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work
    (fun result => (result.1.1,
      ({ before.1 with beacons := before.1.beacons.set index { owner with view := result.1.2 }, environment := result.2 }, before.2))) <$>
      simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) changed

noncomputable def handler [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (M n KemSK source Platform)
  | .inr (.accept packet) => accept setup checks source selectedAccept reserveRegistration packet
  | .inr (.build handle application) => build setup sign view failure allocation erased helper writer reservePeer handle application source
  | .inr (.finish index packet) => finish setup wire source index packet
  | query => RegistrationNativePlatformSecretWordOrdinary.handler setup source selectedOwner publicPrekey reserveFrame writer query

noncomputable def run [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform) :=
  (simulateQ (handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      serverKeyId bounds mode work)).run before

/-- The complete new dispatcher uses the exact proved ordinary route outside its three material controllers. -/
theorem ordinary [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (allowed : RegistrationNativePlatformSecretWordOrdinary.Ordinary query) :
    handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query =
      RegistrationNativePlatformSecretWordOrdinary.handler setup source selectedOwner publicPrekey reserveFrame writer query := by
  cases query with
  | inl coin => rfl
  | inr query => cases query <;> first | exact allowed.elim | rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend.ordinary
