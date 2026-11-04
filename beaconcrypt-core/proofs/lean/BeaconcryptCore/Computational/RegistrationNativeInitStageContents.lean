-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseStageContents

/-! The actual outgoing fingerprint continuation binds the complete attached Init fields and both selected Server public keys. Source-stage payload equality determines those bytes and the numeric Server identity; this alone does not assert equality of later hash fingerprints or completed peers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitStageContents
open BeaconcryptCore.Refinement.RegistrationSigningContinuations (retainedFields)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)
open BeaconcryptCore.Refinement.RegistrationAuthentication (initFields initPreimage)

def sourcePayload (state : registration.BeaconInitState) : MldsaTranscriptAuth.Payload :=
  MldsaTranscriptAuth.initPayload (TranscriptAuthRefinement.absInit (retainedFields state))
    (TranscriptAuthRefinement.absId state.server_pin.binding.identity_key_id)
    (absBytes state.server_pin.binding.identity_public_key) (absBytes state.server_pin.public_key)

/-- The actual source fingerprint continuation yields the complete canonical Init payload before its ML hash/sign stages. -/
theorem fingerprint_payload (before : registration.BeaconFingerprint) (reply : Std.Array U8 64#usize) :
    ∃ hashed, before.resume (.Some reply) = .ok (.HashRequested hashed) ∧
      hashed.state = before.state ∧ Command.payload (.beacon hashed) = sourcePayload before.state := by
  obtain ⟨hashed, resumed, state, _fingerprint, request, requested, bytes⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_fingerprint_some_exact before reply
  have literal : request = .Single (Std.Array.to_slice hashed.input) := by
    exact RustM.ok.inj requested.symm
  rw [literal] at bytes
  refine ⟨hashed, resumed, state, ?_⟩
  exact congrArg (MldsaTranscriptAuth.Payload.mk .beacon) bytes

private theorem source_valid (state : registration.BeaconInitState) :
    (TranscriptAuthRefinement.absInit (retainedFields state)).WellFormed := by
  constructor <;> simp [TranscriptAuthRefinement.absInit, retainedFields, absBytes]

private theorem packet_valid (packet : registration.InitPacket) : (initFields packet).WellFormed := by
  constructor <;> simp [initFields, absBytes]

/-- A native accepted Init with the same unsigned source payload has all original attached fields, the exact provisioned numeric identity and both Server public keys. -/
theorem native_fields (state : registration.BeaconInitState) (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket)
    (payloadSame : sourcePayload state = (⟨.beacon, initPreimage pin packet⟩ : MldsaTranscriptAuth.Payload)) :
    state.started.message.identity_key = packet.identity_key ∧ state.pre_key = packet.pre_key ∧
      state.one_time_key = packet.one_time_key ∧ state.pq_key = packet.pq_key ∧
      state.beacon_mldsa = packet.mldsa_public_key ∧
      state.server_pin.binding.identity_key_id = pin.binding.identity_key_id ∧
      state.server_pin.binding.identity_public_key = pin.binding.identity_public_key ∧
      state.server_pin.public_key = pin.public_key := by
  have same := congrArg MldsaTranscriptAuth.Payload.transcript payloadSame
  change Pqxdh.TranscriptAuth.initTranscript
      (TranscriptAuthRefinement.absInit (retainedFields state))
      (TranscriptAuthRefinement.absId state.server_pin.binding.identity_key_id)
      (absBytes state.server_pin.binding.identity_public_key) (absBytes state.server_pin.public_key) =
    Pqxdh.TranscriptAuth.initTranscript (initFields packet)
      (TranscriptAuthRefinement.absId pin.binding.identity_key_id)
      (absBytes pin.binding.identity_public_key) (absBytes pin.public_key) at same
  obtain ⟨fields, ids, ed, ml⟩ := Pqxdh.TranscriptAuth.initTranscript_inj
    (source_valid state) (packet_valid packet) (by simp [absBytes]) (by simp [absBytes]) same
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Subtype.ext ((absBytes_inj_iff _ _).mp ed),
    Subtype.ext ((absBytes_inj_iff _ _).mp ml)⟩
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.identityKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.preKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.oneTimeKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.pqKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.mldsaPublicKey fields))
  · apply UScalar.eq_of_val_eq
    have numeric := congrArg UInt64.toNat ids
    simpa only [TranscriptAuthRefinement.absId_toNat] using numeric

/-- The original fingerprint-to-hash continuation, rather than an arbitrary hash capability, supplies that exact contents correspondence. -/
theorem reached_fields (before : registration.BeaconFingerprint) (reply : Std.Array U8 64#usize)
    (hashed : registration.BeaconInitHash)
    (resumed : before.resume (.Some reply) = .ok (.HashRequested hashed))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (payloadSame : Command.payload (.beacon hashed) = (⟨.beacon, initPreimage pin packet⟩ : MldsaTranscriptAuth.Payload)) :
    sourcePayload before.state = (⟨.beacon, initPreimage pin packet⟩ : MldsaTranscriptAuth.Payload) ∧
      before.state.beacon_mldsa = packet.mldsa_public_key ∧ before.state.server_pin.public_key = pin.public_key := by
  obtain ⟨actual, actualResume, _state, payload⟩ := fingerprint_payload before reply
  have same : actual = hashed := by simpa using actualResume.symm.trans resumed
  subst actual
  have aligned := payload.symm.trans payloadSame
  have fields := native_fields before.state pin packet aligned
  exact ⟨aligned, fields.2.2.2.2.1, fields.2.2.2.2.2.2.2⟩

end BeaconcryptCore.Computational.RegistrationNativeInitStageContents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitStageContents.fingerprint_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitStageContents.fingerprint_payload

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitStageContents.native_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitStageContents.native_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitStageContents.reached_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitStageContents.reached_fields
