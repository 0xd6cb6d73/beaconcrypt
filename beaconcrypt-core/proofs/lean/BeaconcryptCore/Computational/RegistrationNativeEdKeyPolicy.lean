-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdRequests
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy
open PqxdhEd25519EufCma
open BeaconcryptCore.Refinement.RegistrationSigning

def Allowed (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) (message : Pqxdh.Bytes) : Prop :=
  message = prekeyMessage prekey ∨ message = pqMessage pq ∨ ∃ oneTime : X25519PublicKey, message = oneTimeMessage oneTime

def Shape (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) (started : pqxdh.BeaconStart) : Prop :=
  absBytes started.message.prekey = prekeyMessage prekey ∧
    (∃ key : X25519PublicKey, absBytes started.message.one_time_key = oneTimeMessage key) ∧
    absBytes started.message.pq_key = pqMessage pq

/-- Every reached Ed request retains both exact fixed source public keys; only retry one-time keys can vary. -/
theorem request (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)
    (pending : registration.BeaconEd25519Signing) (shape : Shape prekey pq pending.state.started)
    (request : registration.Ed25519SigningRequest) (requested : pending.request = .ok request) :
    Allowed prekey pq (TranscriptAuthParts.absSlice request.message) := by
  obtain ⟨actual, exactRequest, _key, _role, message⟩ := ed_request_exact pending
  have equal : actual = request := RustM.ok.inj (exactRequest.symm.trans requested)
  subst request
  simp only [TranscriptAuthParts.absSlice, message]
  cases stage : pending.stage
  all_goals simp only [signingMessageValues, stage]
  · change Allowed prekey pq (absBytes pending.state.started.message.prekey)
    exact Or.inl shape.1
  · change Allowed prekey pq (absBytes pending.state.started.message.one_time_key)
    exact Or.inr (Or.inr shape.2.1)
  · change Allowed prekey pq (absBytes pending.state.started.message.pq_key)
    exact Or.inr (Or.inl shape.2.2)

/-- The actual Core begin derives the stronger fixed-prekey/fixed-PQ shape from its original source inputs, retaining pin rejection. -/
theorem begin_shape (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (prekey oneTime : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)
    (prekeyBytes : absBytes inputs.prekey_public_key = prekey.toList)
    (oneTimeBytes : absBytes coins.one_time_public_key = oneTime.toList)
    (pqBytes : absBytes inputs.pq_public_key = pq.toList)
    (pending : registration.BeaconEd25519Signing)
    (begun : registration.begin_beacon_init control inputs coins pin mldsa = .ok (.Ed25519SigningRequested pending)) :
    Shape prekey pq pending.state.started := by
  obtain ⟨started, built, _pin, _identity, pre, one, kem⟩ := PqxdhJointPhase1SourceWriter.beacon_start_unsigned control inputs coins
  obtain ⟨actual, actualBuild, exactBegin⟩ := BeaconcryptCore.Refinement.RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  have same : started = actual := RustM.ok.inj (built.symm.trans actualBuild)
  subst actual
  rw [exactBegin] at begun
  split at begun
  · cases begun
  · have equal := registration.BeaconInitEffect.Ed25519SigningRequested.inj (RustM.ok.inj begun)
    subst pending
    refine ⟨?_, ⟨oneTime, ?_⟩, ?_⟩
    · simpa only [prekeyBytes, prekeyMessage] using pre
    · simpa only [oneTimeBytes, oneTimeMessage] using one
    · simpa only [pqBytes, pqMessage] using kem

/-- The source role tags separate both fixed fields from every admitted retry one-time message. -/
theorem decoded_fixed (prekey changedPre : X25519PublicKey) (pq changedPq : PqxdhKemIndCca.MlKem768PublicKey)
    (pre : Allowed prekey pq (prekeyMessage changedPre)) (kem : Allowed prekey pq (pqMessage changedPq)) :
    changedPre = prekey ∧ changedPq = pq := by
  rcases pre with same | wrong | ⟨one, wrong⟩
  · have preEq := prekeyMessage_injective same
    refine ⟨preEq, ?_⟩
    rcases kem with wrong | same | ⟨one, wrong⟩
    · exact False.elim ((prekeyMessage_ne_pqMessage prekey changedPq) wrong.symm)
    · exact pqMessage_injective same
    · exact False.elim ((oneTimeMessage_ne_pqMessage one changedPq) wrong.symm)
  · exact False.elim ((prekeyMessage_ne_pqMessage changedPre pq) wrong)
  · exact False.elim ((prekeyMessage_ne_oneTimeMessage changedPre one) wrong)
end BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy.request
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy.begin_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy.begin_shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy.decoded_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy.decoded_fixed
