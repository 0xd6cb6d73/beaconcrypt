-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin
/-! A protected successful source Finish outside the actual source authentication flag has an unsigned response-signing observation strictly before that callback opens. The proof uses the literal source monitor and exact callback block; signing success, publication success and distinct prior observations are not required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementIssued
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
open RegistrationNativePlatformPublicAdapterSourceAuthentication (stages)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor (run step initial closed)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable {n :Nat} {KemSK R P :Type} {source :RegistrationNativeMldsa.Source}
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

private theorem persistent (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize)
    (current :RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.State n KemSK R P)
    (events :Events) (held :current.bad=true) :
    (run view serverPublic current events).bad=true :=by
  induction events generalizing current with
  | nil=>exact held
  | cons head tail ih=>
    apply ih
    cases head <;>simp only [step,held,Bool.true_or]

theorem issued (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize) (events :Events)
    (quiet :RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag view serverPublic events=false)
    (index :Nat) (input :Slice U8) (packet :registration.ResponsePacket) (application :Pqxdh.Bytes)
    (before :Store n KemSK R P) (leading :Events) (middle :List Stage) (trailing :Events)
    (objects :RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R)
    (backend :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (observed :events=leading++Event.opened (.inl (.inr (.finish index input))) before::
      (middle.map Event.stage++Event.closed (.inl (.inr (.finish index input))) (.ok (some application,objects)) backend::trailing))
    (decoded :RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)=some packet)
    (found :before.beacons index=some self) (phase :self.state=.InitSent pending prekey oneTime kem)
    (protectedKey :pending.binding.server_pin.public_key=serverPublic) :
    MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationNativePlatformPublicAdapterSourceSigningHistory.history (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) (stages leading))) :=by
  classical
  by_contra absent
  let command:=RegistrationNativePlatformPublicAdapterInterface.Command.finish index input
  have bad :RegistrationNativePlatformPublicAdapterSourceAuthentication.Bad view serverPublic (stages leading)
      command before (some application) (RegistrationNativePlatformPublicAdapterSourceRuntime.join objects backend):=
    .finish index input packet application before _ self pending prekey oneTime kem decoded found phase protectedKey absent
  have history :(run view serverPublic (initial (n:=n) (KemSK:=KemSK) (R:=R) (P:=P)) leading).stages=stages leading:=by
    simpa only [initial,List.nil_append] using
      RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.history_run view serverPublic initial leading
  have closedBad :closed view serverPublic
      (some (before,(run view serverPublic initial leading).stages)) (.inl (.inr command))
      (.ok (some application,objects)) backend=true :=by
    rw [history]
    exact (RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed_iff view serverPublic before (stages leading) command (some application) objects backend).mpr bad
  let block :Events:=[Event.opened (.inl (.inr command)) before]++middle.map Event.stage++
    [Event.closed (.inl (.inr command)) (.ok (some application,objects)) backend]
  have afterBlock :(run view serverPublic (run view serverPublic initial leading) block).bad=true:=by
    rw [show block=[Event.opened (.inl (.inr command)) before]++middle.map Event.stage++
      [Event.closed (.inl (.inr command)) (.ok (some application,objects)) backend] from rfl,
      RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.callback_bad,closedBad,Bool.or_true]
  have afterAll :=persistent view serverPublic _ trailing afterBlock
  have allEq :events=leading++block++trailing:=by
    simpa only [block,command,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using observed
  unfold RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag at quiet
  rw [allEq,RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_append,
    RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_append] at quiet
  rw [afterAll] at quiet
  cases quiet

theorem sign (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (serverPublic :Std.Array U8 1952#usize) (events :Events)
    (quiet :RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag view serverPublic events=false)
    (index :Nat) (input :Slice U8) (packet :registration.ResponsePacket) (application :Pqxdh.Bytes)
    (before :Store n KemSK R P) (leading :Events) (middle :List Stage) (trailing :Events)
    (objects :RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R)
    (backend :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (observed :events=leading++Event.opened (.inl (.inr (.finish index input))) before::
      (middle.map Event.stage++Event.closed (.inl (.inr (.finish index input))) (.ok (some application,objects)) backend::trailing))
    (decoded :RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)=some packet)
    (found :before.beacons index=some self) (phase :self.state=.InitSent pending prekey oneTime kem)
    (protectedKey :pending.binding.server_pin.public_key=serverPublic) :
    ∃request digest reply,
      Event.stage (Stage.sign request (RegistrationResponseExecutor.payload pending packet) digest reply)∈leading ∧
      request.public_key=serverPublic :=by
  have prior:=issued view serverPublic events quiet index input packet application before leading middle trailing objects backend
    self pending prekey oneTime kem observed decoded found phase protectedKey
  obtain ⟨request,digest,reply,present,key⟩:=RegistrationNativePlatformPublicAdapterSourceSigningOrigin.issued_sign
    (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) true (stages leading)
    (RegistrationResponseExecutor.payload pending packet) (PqxdhRefinement.absBytes packet.signature) prior
  have sourceKey :request.public_key=pending.binding.server_pin.public_key:=Subtype.ext ((PqxdhRefinement.absBytes_inj_iff _ _).mp key)
  refine ⟨request,digest,reply,?_,sourceKey.trans protectedKey⟩
  obtain ⟨event,member,same⟩:=List.mem_filterMap.mp present
  cases event with
  | opened _ _ | closed _ _ _=>cases same
  | stage actual=>
    have actualEq:=Option.some.inj same
    cases actualEq
    exact member

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementIssued
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementIssued.issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementIssued.issued

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementIssued.sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementIssued.sign
