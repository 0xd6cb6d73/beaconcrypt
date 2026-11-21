-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativeConcreteReaders
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
/-! The selected raw public-adapter target fixes the actual codec and sender decoder, retains original raw bytes and uses the unchanged extracted dictionary. Its local equations connect the concrete wrapper factories without a caller-supplied callback law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
attribute [local irreducible] RegistrationNativePlatformExtractedExperiment.record
  RegistrationNativePlatformExtractedAuthentication.accept RegistrationNativePlatformExtractedBundle.bundle
  RegistrationNativePlatformExtractedFinish.finish RegistrationNativeConcreteCodec.wire
  RegistrationNativePlatformPublicAdapterRouting.route
open BeaconcryptCore.Refinement
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route

noncomputable def typed : QueryImpl TypedSpec (RegistrationNativePlatformExtractedExperiment.M n KemSK source Platform) :=
  RegistrationNativePlatformExtractedExperiment.handler setup checks wire route representation created source credential view failure
    allocation reserveRegistration reservePeer reserveFrame erased helper writer

noncomputable def raw : QueryImpl RegistrationNativeInterface.Spec
    (RegistrationNativePlatformExtractedExperiment.M n KemSK source Platform) :=
  typed setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    ∘ₛ RegistrationNativeRawAdapter.adapter wire

theorem accept (input : Slice U8) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.accept (TranscriptAuthParts.absSlice input)))=
    RegistrationNativeRawAdapter.resultOption <$>
      RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup (RegistrationNativeWire.ledgerCodec (canonicalWire wire))
        checks reserveRegistration route source.verify representation created input := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter]
  rw [RegistrationNativeConcreteReaders.init]
  unfold RegistrationNativePlatformExtractedSdkServer.Accept.native
  cases (wire).decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>rfl
  | some packet=>
    rw [simulateQ_map,simulateQ_spec_query]
    rfl

theorem bundle (index : Nat) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.bundle index))=
    RegistrationNativeRawAdapter.resultOption <$>
      RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source writer index := rfl

theorem finish (index : Nat) (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.finish index bytes))=
    RegistrationNativeRawAdapter.resultOption <$>
      RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source (canonicalWire wire) index
            ((wire).decodeResponse bytes))) := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter]
  rw [RegistrationNativeConcreteReaders.response]
  rfl

theorem server_send (keyId : U64) (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.serverSend keyId bytes))=
    RegistrationNativePlatformExtractedExperiment.record setup wire reserveFrame view failure erased route (.inl (.inl (bytes,keyId))) source := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem server_receive (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.serverRaw bytes))=
    RegistrationNativePlatformExtractedExperiment.record setup wire reserveFrame view failure erased route (.inl (.inr bytes)) source := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem beacon_send (index : Nat) (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.beaconSend index bytes))=
    RegistrationNativePlatformExtractedExperiment.record setup wire reserveFrame view failure erased route (.inr (index,.inl bytes)) source := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem beacon_receive (index : Nat) (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.beaconRaw index bytes))=
    RegistrationNativePlatformExtractedExperiment.record setup wire reserveFrame view failure erased route (.inr (index,.inr bytes)) source := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem coin (query : unifSpec.Domain) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inl query)=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects (.inl query))) := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem hash (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.hash bytes))=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects (.inr (.hash bytes)))) := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem hmac (key : PqxdhSecretInputKdf.HmacBlock) (bytes : Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.hmac key bytes))=pure (setup.hmac.eval key bytes) := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_spec_query]
  rfl

theorem build (handle : Nat) (payload : Option Pqxdh.Bytes) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.build handle payload))=
    RegistrationNativeRawAdapter.responseOption <$>
      typed setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (.inr (.build handle (RegistrationNativeRawAdapter.application payload))) := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,simulateQ_map,simulateQ_spec_query]

theorem create (edPin mlPin : Pqxdh.Bytes) (keyId : U64) :
    raw (n:=n) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (.inr (.create edPin mlPin keyId))=
    match PqxdhDeploymentInterface.parsePin edPin,RegistrationNativeWire.parseMldsaPin mlPin with
    | some edPin,some mlPin=>RegistrationNativeRawAdapter.resultOption <$>
        RegistrationNativePlatformExperiment.liftNative coins
          (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))
    | _,_=>pure none := by
  simp only [raw,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter]
  cases PqxdhDeploymentInterface.parsePin edPin with
  | none=>rfl
  | some parsed=>cases RegistrationNativeWire.parseMldsaPin mlPin with
    | none=>rfl
    | some parsedMl=>
      rw [simulateQ_map,simulateQ_spec_query]
      rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.server_send
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.server_receive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.beacon_send
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.beacon_receive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.coin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.hash
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.hmac
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel.create
