-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdRequests
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! Every possible source path through the actual three attached-signing continuations requests only the owner's fixed prekey message or a properly tagged one-time/PQ message. This includes replies that later reject and attempts whose final ML signature or encoder fails. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds
open RegistrationBeaconInitExecutor
open RegistrationNativeEdRequests (Shape)
open RegistrationNativeEdOrigin (Allowed)
open PqxdhEd25519EufCma (X25519PublicKey)
variable {Encoded : Type}

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.begin_beacon_init
  RegistrationBeaconInitExecutor.ready RegistrationBeaconInitExecutor.fromSigning
  RegistrationBeaconInitExecutor.fromHash RegistrationBeaconInitExecutor.fromFingerprint

def AllowedQuery (prekey : X25519PublicKey) : Spec.Domain → Prop
  | .inl _ => True
  | .inr request => Allowed prekey (TranscriptAuthParts.absSlice request.message)

private theorem continue_all {Input : Type} (prekey : X25519PublicKey) (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (good : ∀ value, AllQueriesSatisfy (next value) (AllowedQuery prekey)) :
    AllQueriesSatisfy (continueWith action next) (AllowedQuery prekey) := by
  cases action with
  | ok value => exact good value
  | fail error => trivial
  | div => trivial

private theorem ready_all (prekey : X25519PublicKey)
    (encode : registration.SignedInitView → core.option.Option Encoded) (pending : registration.BeaconInitReady) :
    AllQueriesSatisfy (ready encode pending) (AllowedQuery prekey) := by
  unfold ready
  exact continue_all prekey _ _ (fun _ => by trivial)

private theorem signing_all (prekey : X25519PublicKey)
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    AllQueriesSatisfy (fromSigning encode payload digest pending) (AllowedQuery prekey) := by
  unfold fromSigning
  apply continue_all prekey
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun signature => ?_⟩
  apply continue_all prekey
  intro effect
  cases effect with
  | Ready selected => exact ready_all prekey encode selected
  | _ => trivial

private theorem hash_all (prekey : X25519PublicKey)
    (encode : registration.SignedInitView → core.option.Option Encoded) (pending : registration.BeaconInitHash) :
    AllQueriesSatisfy (fromHash encode pending) (AllowedQuery prekey) := by
  unfold fromHash
  apply continue_all prekey
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_all prekey
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing_all prekey encode _ _ selected
  | _ => trivial

private theorem fingerprint_all (prekey : X25519PublicKey)
    (encode : registration.SignedInitView → core.option.Option Encoded) (pending : registration.BeaconFingerprint) :
    AllQueriesSatisfy (fromFingerprint encode pending) (AllowedQuery prekey) := by
  unfold fromFingerprint
  apply continue_all prekey
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_all prekey
  intro effect
  cases effect with
  | HashRequested selected => exact hash_all prekey encode selected
  | _ => trivial

theorem ed_all (prekey : X25519PublicKey)
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) (shape : Shape prekey pending.state.started) :
    AllQueriesSatisfy (fromEd encode pending) (AllowedQuery prekey) := by
  rw [fromEd.eq_def]
  obtain ⟨request, requested, _⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact pending
  rw [requested]
  change AllQueriesSatisfy (do
    let reply ← (Spec.query (.inr request) : OracleComp Spec RegistrationSigningShared.SignReply)
    match _actual : pending.resume reply with
    | .ok (.Rejected previous) => pure (.ok (.Err previous))
    | .ok (.Ed25519SigningRequested next) => fromEd encode next
    | .ok (.FingerprintRequested selected) => fromFingerprint encode selected
    | .ok _ => pure .div
    | .fail error => pure (.fail error)
    | .div => pure .div) (AllowedQuery prekey)
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨RegistrationNativeEdRequests.request_allowed prekey pending shape request requested, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error => trivial
  | div => trivial
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next =>
          exact ed_all prekey encode next
            ((congrArg (Shape prekey) (RegistrationNativeEdRequests.resume_started pending next reply actual)).mpr shape)
      | FingerprintRequested selected => exact fingerprint_all prekey encode selected
      | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- The actual native begin gate derives the allowed-message bound from the original source public inputs. -/
theorem begin_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (prekey oneTime : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)
    (prekeyBytes : PqxdhRefinement.absBytes inputs.prekey_public_key = prekey.toList)
    (oneTimeBytes : PqxdhRefinement.absBytes coins.one_time_public_key = oneTime.toList)
    (pqBytes : PqxdhRefinement.absBytes inputs.pq_public_key = pq.toList) :
    AllQueriesSatisfy (begin encode control inputs coins pin mldsa) (AllowedQuery prekey) := by
  unfold begin
  cases actual : registration.begin_beacon_init control inputs coins pin mldsa with
  | fail error => trivial
  | div => trivial
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested pending =>
          exact ed_all prekey encode pending
            (RegistrationNativeEdRequests.begin_shape control inputs coins pin mldsa prekey oneTime pq
              prekeyBytes oneTimeBytes pqBytes pending actual)
      | _ => trivial

end BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds.ed_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds.ed_all

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds.begin_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdSigningBounds.begin_all
