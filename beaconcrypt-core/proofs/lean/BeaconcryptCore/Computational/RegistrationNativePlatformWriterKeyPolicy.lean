-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy
open RegistrationNativePlatformWriter (Spec cryptoLift init)
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (edRank ed_rank)
open PqxdhEd25519EufCma (X25519PublicKey)
open RegistrationNativeEdKeyPolicy (Allowed Shape)
variable {E : Type}
attribute [local irreducible] registration.BeaconInitHash.resume
  registration.begin_beacon_init
  RegistrationNativePlatformBeaconPublication.ready
  RegistrationNativePlatformBeaconPublication.fromHash
variable (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)

def AllowedQuery : (Spec E).Domain → Prop
  | .inl (.inr request) => Allowed prekey pq (TranscriptAuthParts.absSlice request.message)
  | _ => True

private theorem continue_all {Input : Type} (action : RustM Input)
    (next : Input → OracleComp (Spec E) (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))))
    (good : ∀ value, (next value).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq)) :
    (continueWith action next).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq) := by
  cases action with
  | ok value => exact good value
  | fail error => trivial
  | div => trivial

private theorem writer_all (work : OracleComp (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (RustM (core.option.Option (alloc.vec.Vec U8)))) :
    (simulateQ RegistrationNativePlatformWriter.writerLift work).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformWriter.writerLift]
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨trivial, ih⟩

private theorem ready_all (pending : registration.BeaconInitReady) :
    (ready (init E) pending).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq) := by
  unfold ready
  apply continue_all prekey pq
  intro view
  apply allQueriesSatisfy_bind (writer_all prekey pq _)
  intro _
  trivial

private theorem hash_all (pending : registration.BeaconInitHash) :
    (fromHash cryptoLift (init E) pending).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq) := by
  unfold fromHash
  apply continue_all prekey pq
  intro request
  rw [cryptoLift, allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun digest => ?_⟩
  apply continue_all prekey pq
  intro effect
  cases effect with
  | Ready selected => exact ready_all prekey pq selected
  | _ => trivial

/-- The actual dynamic writer controller signs only its two original fixed fields or tagged retry one-time messages, including every failed Ed/ML/writer prefix. -/
theorem ed_all (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)
    (pending : registration.BeaconEd25519Signing) (shape : Shape prekey pq pending.state.started) :
    (fromEd cryptoLift (init E) pending).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq) := by
  rw [fromEd.eq_def]
  obtain ⟨request, requested, _⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact pending
  rw [requested]
  change AllQueriesSatisfy (do
    let reply ← ((Spec E).query (.inl (.inr request)) : OracleComp (Spec E) RegistrationSigningShared.SignReply)
    match _actual : pending.resume reply with
    | .ok (.Rejected previous) => pure (RustM.ok (.Err previous) : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    | .ok (.Ed25519SigningRequested next) => fromEd cryptoLift (init E) next
    | .ok (.HashRequested selected) => fromHash cryptoLift (init E) selected
    | .ok _ => pure .div
    | .fail error => pure (.fail error)
    | .div => pure .div) (AllowedQuery (E := E) prekey pq)
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨RegistrationNativeEdKeyPolicy.request prekey pq pending shape request requested, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error => trivial
  | div => trivial
  | ok effect =>
    cases effect with
    | Ed25519SigningRequested next =>
      exact ed_all prekey pq next ((congrArg (Shape prekey pq)
        (RegistrationNativeEdRequests.resume_started pending next reply actual)).mpr shape)
    | HashRequested selected => exact hash_all prekey pq selected
    | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- Both fixed keys are derived from the literal actual source inputs before any dynamic signing or writer outcome. -/
theorem begin_all (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (oneTime : X25519PublicKey) (prekeyBytes : PqxdhRefinement.absBytes inputs.prekey_public_key = prekey.toList)
    (oneTimeBytes : PqxdhRefinement.absBytes coins.one_time_public_key = oneTime.toList)
    (pqBytes : PqxdhRefinement.absBytes inputs.pq_public_key = pq.toList) :
    (RegistrationNativePlatformWriter.begin E control inputs coins pin).AllQueriesSatisfy (AllowedQuery (E := E) prekey pq) := by
  unfold RegistrationNativePlatformWriter.begin RegistrationNativePlatformBeaconPublication.begin
  cases actual : registration.begin_beacon_init control inputs coins pin with
  | fail error => trivial
  | div => trivial
  | ok effect =>
    cases effect with
    | Ed25519SigningRequested pending =>
      exact ed_all prekey pq pending (RegistrationNativeEdKeyPolicy.begin_shape control inputs coins pin
        prekey oneTime pq prekeyBytes oneTimeBytes pqBytes pending actual)
    | _ => trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy.ed_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy.ed_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy.begin_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWriterKeyPolicy.begin_all
