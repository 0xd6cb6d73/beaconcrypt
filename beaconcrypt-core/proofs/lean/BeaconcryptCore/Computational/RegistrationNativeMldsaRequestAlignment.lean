-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared
import BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax
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

/-- The outgoing Init has no ML request; shared request alignment is therefore vacuous on this actor. -/
theorem begin_all (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    AllQueriesSatisfy (begin encode control inputs coins pin) BeaconQuery := by
  apply (RegistrationNativeMldsaRoleSyntax.begin_all encode control inputs coins pin).mono
  intro query allowed
  cases query with
  | inl shared => cases shared with
    | hash _ => trivial
    | sign _ _ _ => exact False.elim allowed
  | inr _ => trivial
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
