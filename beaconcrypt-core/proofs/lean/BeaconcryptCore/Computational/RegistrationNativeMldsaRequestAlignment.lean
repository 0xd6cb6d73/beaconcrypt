-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared
import BeaconcryptCore.Computational.RegistrationWorldServerPublication
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! Every actual outgoing Init and response hash/sign controller sends the complete native ML request for its own recorded unsigned payload and returned digest. This holds on all source paths, including failed signatures and failed encoding, before any ordinary-EUF freshness argument is applied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {Encoded : Type}

def Correct (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload)
    (digest : CtxRomAuth.CtxDigest) : Prop :=
  TranscriptAuthInputsRefinement.absRole request.role = payload.role ∧
    absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
    absBytes request.input = Pqxdh.TranscriptAuth.signatureInput payload.role digest.toList

def SharedQuery : RegistrationSigningShared.Spec.Domain → Prop
  | .sign request payload digest => Correct request payload digest
  | .hash _ => True

def BeaconQuery : RegistrationBeaconInitExecutor.Spec.Domain → Prop
  | .inl query => SharedQuery query
  | .inr _ => True

namespace Beacon
open RegistrationBeaconInitExecutor
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.begin_beacon_init

private theorem continue_all {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded)))
    (good : ∀ value, AllQueriesSatisfy (next value) BeaconQuery) :
    AllQueriesSatisfy (continueWith action next) BeaconQuery := by
  cases action with
  | ok value => exact good value
  | fail error => trivial
  | div => trivial

private theorem ready_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) : AllQueriesSatisfy (ready encode pending) BeaconQuery := by
  unfold ready
  exact continue_all _ _ (fun _ => by trivial)

private theorem signing_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning)
    (request : registration.MldsaSigningRequest) (requested : pending.request = .ok request)
    (correct : Correct request payload digest) : AllQueriesSatisfy (fromSigning encode payload digest pending) BeaconQuery := by
  unfold fromSigning
  rw [requested]
  change AllQueriesSatisfy (do
    let signature ← (Spec.query (.inl (.sign request payload digest)) : OracleComp Spec RegistrationSigningShared.SignReply)
    continueWith (pending.resume signature) fun effect => match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .Ready selected => ready encode selected
      | _ => pure .div) BeaconQuery
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨correct, fun _ => ?_⟩
  apply continue_all
  intro effect
  cases effect with
  | Ready selected => exact ready_all encode selected
  | _ => trivial

/-- Every ML request reached after the actual Init hash has exactly that returned digest, Beacon role and native FIPS context. -/
theorem hash_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) : AllQueriesSatisfy (fromHash encode pending) BeaconQuery := by
  obtain ⟨request, requested, _bytes⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.beacon pending)
  change pending.request = .ok request at requested
  unfold fromHash
  rw [requested]
  change AllQueriesSatisfy (do
    let digest ← (Spec.query (.inl (.hash request)) : OracleComp Spec CtxRomAuth.CtxDigest)
    continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .MldsaSigningRequested selected => fromSigning encode ⟨.beacon, hashBytes request⟩ digest selected
      | _ => pure .div) BeaconQuery
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun digest => ?_⟩
  obtain ⟨selected, resumed, _state, _fingerprint, _hash, signing, signed, _key, role, _context, contextBytes, inputBytes⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact pending
      (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed]
  apply signing_all encode _ digest selected signing signed
  refine ⟨?_, contextBytes, ?_⟩
  · simp only [role, TranscriptAuthInputsRefinement.absRole]
  · simpa only [RegistrationAuthenticationShared.digest_array_bytes] using inputBytes

private theorem fingerprint_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) : AllQueriesSatisfy (fromFingerprint encode pending) BeaconQuery := by
  unfold fromFingerprint
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun _ => ?_⟩
  apply continue_all
  intro effect
  cases effect with
  | HashRequested selected => exact hash_all encode selected
  | _ => trivial

/-- Optional Ed failures and all three attached-signing stages retain complete ML-request alignment at every later reached native leaf. -/
theorem ed_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) : AllQueriesSatisfy (fromEd encode pending) BeaconQuery := by
  rw [fromEd.eq_def]
  apply continue_all
  intro request
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun reply => ?_⟩
  cases actual : pending.resume reply with
  | fail error | div => trivial
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_all encode next
    | FingerprintRequested selected => exact fingerprint_all encode selected
    | _ => trivial
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- The whole actual outgoing Init program is aligned without a publication-success premise. -/
theorem begin_all (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    AllQueriesSatisfy (begin encode control inputs coins pin mldsa) BeaconQuery := by
  unfold begin
  apply continue_all
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed_all encode selected
  | _ => trivial
end Beacon

namespace Server
open RegistrationWorldServerPublication
private theorem continue_all {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (Result Encoded)))
    (good : ∀ value, AllQueriesSatisfy (next value) SharedQuery) :
    AllQueriesSatisfy (continueWith action next) SharedQuery := by
  cases action with
  | ok value => exact good value
  | fail error | div => trivial
private theorem result_all {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (Result Encoded)))
    (good : ∀ value, AllQueriesSatisfy (next value) SharedQuery) :
    AllQueriesSatisfy (continueResult action next) SharedQuery := by
  cases action with
  | ok value => cases value with
    | Ok value => exact good value
    | Err _ => trivial
  | fail error | div => trivial
private theorem ready_all (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) : AllQueriesSatisfy (ready encode pending) SharedQuery := by
  unfold ready
  exact continue_all _ _ (fun _ => by trivial)
private theorem signing_all (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.ServerResponseSigning)
    (request : registration.MldsaSigningRequest) (requested : pending.request = .ok request)
    (correct : Correct request payload digest) : AllQueriesSatisfy (signing encode payload digest pending) SharedQuery := by
  unfold signing
  rw [requested]
  change AllQueriesSatisfy (do
    let signature ← (RegistrationSigningShared.Spec.query (.sign request payload digest) :
      OracleComp RegistrationSigningShared.Spec RegistrationSigningShared.SignReply)
    continueResult (pending.resume signature) (ready encode)) SharedQuery
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨correct, fun _ => ?_⟩
  exact result_all _ _ (ready_all encode)

/-- Every actual response signing request uses the reached response digest, selected Server role and native FIPS context, including optional signature and encoding failure. -/
theorem program_all (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) : AllQueriesSatisfy (program encode pending) SharedQuery := by
  obtain ⟨request, requested, _bytes⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  unfold program
  rw [requested]
  change AllQueriesSatisfy (do
    let digest ← (RegistrationSigningShared.Spec.query (.hash request) :
      OracleComp RegistrationSigningShared.Spec CtxRomAuth.CtxDigest)
    continueResult (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))
      (signing encode ⟨.server, hashBytes request⟩ digest)) SharedQuery
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨trivial, fun digest => ?_⟩
  obtain ⟨selected, resumed, _candidate, _binding, _kernel, _ciphertext, inputBytes, requested⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending
      (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed]
  apply signing_all encode _ digest selected _ requested
  exact ⟨rfl, TranscriptAuthInputsRefinement.signing_context_abs,
    by simpa only [RegistrationAuthenticationShared.digest_array_bytes] using inputBytes⟩
end Server

/-- A reached cached receipt translates complete source-request alignment into the exact message used by ordinary ML unforgeability. -/
theorem cached_message (request : registration.MldsaSigningRequest) (payload : MldsaTranscriptAuth.Payload)
    (digest : CtxRomAuth.CtxDigest) (cache : CtxRomAuth.CtxRO.QueryCache)
    (correct : Correct request payload digest) (cached : cache ((), payload.transcript) = some digest) :
    absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
      absBytes request.input = payload.message (MldsaSharedAuthentication.cacheHash cache) := by
  refine ⟨correct.2.1, ?_⟩
  rw [MldsaTranscriptAuth.Payload.message, MldsaSharedAuthentication.cache_hash_reconstruct _ _ digest cached]
  exact correct.2.2

end BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Beacon.hash_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Beacon.hash_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Beacon.ed_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Beacon.ed_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Beacon.begin_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Beacon.begin_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Server.program_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.Server.program_all
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.cached_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment.cached_message
