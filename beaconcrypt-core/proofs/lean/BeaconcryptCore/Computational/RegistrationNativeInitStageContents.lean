-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.MldsaTranscriptAuth
import BeaconcryptCore.Refinement.RegistrationAuthentication
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! The actual retained request payload binds the complete attached Init fields and both selected Server public keys. Source-stage payload equality determines those bytes and the numeric Server identity; this alone does not assert equality of hash digests or completed peers. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitStageContents
open BeaconcryptCore.Refinement.RegistrationSigningContinuations (retainedFields)
open BeaconcryptCore.Refinement.RegistrationAuthentication (initFields initPreimage)

def sourcePayload (state : registration.BeaconInitState) : MldsaTranscriptAuth.Payload :=
  MldsaTranscriptAuth.initPayload (TranscriptAuthRefinement.absInit (retainedFields state))
    (TranscriptAuthRefinement.absId state.server_pin.binding.identity_key_id)
    (absBytes state.server_pin.binding.identity_public_key) (absBytes state.server_pin.public_key)

/-- A current hash capability is canonical only with the retained source builder receipt. -/
def Canonical (pending : registration.BeaconInitHash) : Prop :=
  absBytes pending.input = (sourcePayload pending.state).transcript

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
  refine ⟨?_, ?_, ?_, ?_, ?_, Subtype.ext ((absBytes_inj_iff _ _).mp ed),
    Subtype.ext ((absBytes_inj_iff _ _).mp ml)⟩
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.identityKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.preKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.oneTimeKey fields))
  · exact Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Pqxdh.TranscriptAuth.InitFields.pqKey fields))
  · apply UScalar.eq_of_val_eq
    have numeric := congrArg UInt64.toNat ids
    simpa only [TranscriptAuthRefinement.absId_toNat] using numeric

end BeaconcryptCore.Computational.RegistrationNativeInitStageContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitStageContents.native_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitStageContents.native_fields
