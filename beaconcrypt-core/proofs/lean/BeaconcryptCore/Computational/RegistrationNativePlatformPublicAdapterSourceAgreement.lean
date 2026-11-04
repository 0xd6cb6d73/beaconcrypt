-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication
import BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers
import BeaconcryptCore.Computational.RegistrationNativeCompletionContents
/-! Agreement is a property of actual source operations. A partner is an earlier response-signing source callback, not a completed publication or installation. The finish initializer and first-record result are the actual source-stage values, while protection remains qualification by the configured ML public key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
open RegistrationNativePlatformPublicAdapterSourceAuthentication (stages)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK R P AD PT CT :Type}
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

/-- The complete Build callback containing the response sign occurs strictly before this Finish callback opens. Its later writer or installation may fail. -/
def Partner (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source :PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverPublic :Std.Array U8 1952#usize) (earlier :Events)
    (pending :registration.BeaconPending) (packet :registration.ResponsePacket)
    (application :Pqxdh.Bytes) (finishStages :List Stage) :Prop :=
  ∃(handle :Nat) (payload :Option (Slice U8)) (beforeBuild :Store n KemSK R P)
    (leading :Events) (buildStages :List Stage) (trailing :Events)
    (buildReply :RustM (Option PqxdhServerRegistrationPublication.Response×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R))
    (backend :RegistrationNativePlatformSdkReification.Backend n KemSK×P),
    earlier=leading++Event.opened (.inl (.inr (.build handle payload))) beforeBuild::
      (buildStages.map Event.stage++Event.closed (.inl (.inr (.build handle payload))) buildReply backend::trailing) ∧
    ∃token serverInitial hashed request digest signature beaconInitial completed,
      beforeBuild.tokens handle=some token ∧
      Stage.firstRecord serverInitial (.ok (.Ok hashed))∈buildStages ∧
      Stage.sign request (RegistrationSigningTrace.Command.payload (.server hashed)) digest signature∈buildStages ∧
      request.public_key=serverPublic ∧
      Stage.beaconFirstRecord beaconInitial (.ok (.Ok completed))∈finishStages ∧
      RegistrationNativeCompletionContents.Outcome serverInitial ⟨pending,packet⟩ beaconInitial.agreement completed application ∧
      token.registration.agreement.root.bytes=beaconInitial.agreement.root.bytes ∧
      RegistrationNativeInitializedInitializers.Initializers crypto source token.registration.agreement
        beaconInitial.agreement serverInitial beaconInitial

/-- Every protected successful source Finish has a strict-earlier response-signing partner in the same source log. This is non-injective and makes no claim that the partner publication succeeded. -/
def AllOwners (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source :PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverPublic :Std.Array U8 1952#usize) (events :Events) :Prop :=
  ∀(index :Nat) (input :Slice U8) (packet :registration.ResponsePacket) (application :Pqxdh.Bytes)
    (before :Store n KemSK R P) (leading :Events) (finishStages :List Stage) (trailing :Events)
    (objects :RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R)
    (backend :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair),
    events=leading++Event.opened (.inl (.inr (.finish index input))) before::
      (finishStages.map Event.stage++Event.closed (.inl (.inr (.finish index input))) (.ok (some application,objects)) backend::trailing) →
    RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)=some packet →
    before.beacons index=some self →self.state=.InitSent pending prekey oneTime kem →
    pending.binding.server_pin.public_key=serverPublic →
    Partner crypto source serverPublic leading pending packet application finishStages

noncomputable def flag (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source :PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverPublic :Std.Array U8 1952#usize) (events :Events) :Bool :=by
  classical
  exact decide (¬AllOwners crypto source serverPublic events)


theorem flag_iff (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source :PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverPublic :Std.Array U8 1952#usize) (events :Events) :
    flag crypto source serverPublic events=true ↔¬AllOwners crypto source serverPublic events :=by
  simp only [flag,decide_eq_true_eq]

/-- The exported source partner really contains its signing operation in the strict earlier callback prefix. -/
theorem sign_before (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source :PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverPublic :Std.Array U8 1952#usize) (earlier :Events)
    (pending :registration.BeaconPending) (packet :registration.ResponsePacket)
    (application :Pqxdh.Bytes) (finishStages :List Stage)
    (held :Partner crypto source serverPublic earlier pending packet application finishStages) :
    ∃request hashed digest signature,
      Event.stage (Stage.sign request (RegistrationSigningTrace.Command.payload (.server hashed)) digest signature)∈earlier ∧
      request.public_key=serverPublic :=by
  obtain ⟨handle,payload,beforeBuild,leading,buildStages,trailing,buildReply,backend,same,
    token,serverInitial,hashed,request,digest,signature,beaconInitial,completed,
    _token,_record,signed,key,_finished,_contents,_root,_initializers⟩:=held
  refine ⟨request,hashed,digest,signature,?_,key⟩
  rw [same]
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨_,signed,rfl⟩

/-- Both source initializers and the finished source record are explicit values in this one source-log property. -/
theorem records (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source :PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverPublic :Std.Array U8 1952#usize) (earlier :Events)
    (pending :registration.BeaconPending) (packet :registration.ResponsePacket)
    (application :Pqxdh.Bytes) (finishStages :List Stage)
    (held :Partner crypto source serverPublic earlier pending packet application finishStages) :
    ∃(token :beaconcrypt_public_wrapper.server.RegistrationOutput),∃serverInitial hashed beaconInitial completed,
      Event.stage (Stage.firstRecord serverInitial (.ok (.Ok hashed)))∈earlier ∧
      Stage.beaconFirstRecord beaconInitial (.ok (.Ok completed))∈finishStages ∧
      RegistrationNativeCompletionContents.Outcome serverInitial ⟨pending,packet⟩ beaconInitial.agreement completed application ∧
      token.registration.agreement.root.bytes=beaconInitial.agreement.root.bytes ∧
      RegistrationNativeInitializedInitializers.Initializers crypto source token.registration.agreement
        beaconInitial.agreement serverInitial beaconInitial :=by
  obtain ⟨handle,payload,beforeBuild,leading,buildStages,trailing,buildReply,backend,same,
    token,serverInitial,hashed,request,digest,signature,beaconInitial,completed,
    _token,recorded,_signed,_key,finished,contents,root,initializers⟩:=held
  refine ⟨token,serverInitial,hashed,beaconInitial,completed,?_,finished,contents,root,initializers⟩
  rw [same]
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨_,recorded,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement.flag_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement.flag_iff

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement.sign_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement.sign_before

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement.records
