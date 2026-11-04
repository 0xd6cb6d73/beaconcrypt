-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication

/-! The actual stateful publication controllers preserve the positionwise primitive-request/native-payload history relation. Complete FIPS request alignment is derived from the reached source hash continuations; arbitrary terminal encoding failures and persistent platform state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativeMldsaRequestAlignment (Correct SharedQuery BeaconQuery)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaTableProgram (runState)
variable {Native Platform Value Next Encoded : Type} (source : RegistrationNativeMldsa.Source)

def Keeps (receipts : Native → List RegistrationSigningShared.Receipt)
    (work : StateT Native (M (handleSource source) Platform) Value) : Prop :=
  ∀ before previous pool result, Aligned pool.signing (receipts before) →
    result ∈ support (runState source work before previous pool) → Aligned result.2.signing (receipts result.1.1.2)

/-- Pure continuations retain both exact chronological histories. -/
theorem pure_keeps (receipts : Native → List RegistrationSigningShared.Receipt) (value : Value) :
    Keeps (Platform := Platform) source receipts (pure value) := by
  intro before previous pool result aligned supported
  rw [RegistrationNativePlatformMldsaTableProgram.run_pure] at supported
  simp only [support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact aligned

/-- Both full poststates and the reached table are threaded into every adaptive continuation. -/
theorem bind_keeps (receipts : Native → List RegistrationSigningShared.Receipt)
    (work : StateT Native (M (handleSource source) Platform) Value)
    (next : Value → StateT Native (M (handleSource source) Platform) Next)
    (first : Keeps source receipts work) (rest : ∀ value, Keeps source receipts (next value)) :
    Keeps source receipts (work >>= next) := by
  intro before previous pool result aligned supported
  rw [RegistrationNativePlatformMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact rest middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 result
    (first before previous pool middle aligned called) continued

/-- Ordinary source effects retain the private signer table and the complete receipt list. -/
theorem closed (receipts : Native → List RegistrationSigningShared.Receipt)
    (work : StateT Native (StateT Platform ProbComp) Value)
    (unchanged : ∀ before previous result, result ∈ support ((work.run before).run previous) → receipts result.1.2 = receipts before) :
    Keeps source receipts (RegistrationNativePlatformMldsaProgram.lift work) := by
  intro before previous pool result aligned supported
  rw [RegistrationNativePlatformMldsaTableProgram.run_lift, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  rw [unchanged before previous inner called]
  exact aligned

namespace Beacon
open RegistrationNativePlatformBeaconPublication
attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init
variable (receipts : Native → List RegistrationSigningShared.Receipt)
variable (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT Native (M (handleSource source) Platform)))
variable (encode : registration.SignedInitView → StateT Native (M (handleSource source) Platform) (RustM (core.option.Option Encoded)))
variable (queries : ∀ query, BeaconQuery query → Keeps source receipts (impl query))
variable (encoding : ∀ view, Keeps source receipts (encode view))

private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → StateT Native (M (handleSource source) Platform) (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps source receipts (next value)) : Keeps source receipts (continueWith action next) := by
  cases action with
  | ok value => exact law value
  | fail error | div => exact pure_keeps source receipts _

include encoding in
private theorem ready_keeps (pending : registration.BeaconInitReady) : Keeps source receipts (ready encode pending) := by
  unfold ready
  exact continue_keeps source receipts _ _ (fun _ => bind_keeps source receipts _ _ (encoding _) (fun _ => pure_keeps source receipts _))

include queries encoding
private theorem signing_keeps (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (request : registration.MldsaSigningRequest)
    (requested : pending.request = .ok request) (correct : Correct request payload digest) :
    Keeps source receipts (fromSigning impl encode payload digest pending) := by
  unfold fromSigning
  rw [requested]
  apply bind_keeps source receipts _ _ (queries (.inl (.sign request payload digest)) correct)
  intro reply
  apply continue_keeps
  intro effect
  cases effect with
  | Ready next => exact ready_keeps source receipts encode encoding next
  | _ => exact pure_keeps source receipts _

/-- Every reached source Init signing request is aligned with its actual hash reply before the effectful writer can execute. -/
theorem hash_keeps (pending : registration.BeaconInitHash) : Keeps source receipts (fromHash impl encode pending) := by
  obtain ⟨request, requested, _bytes⟩ := BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.beacon pending)
  change pending.request = .ok request at requested
  unfold fromHash
  rw [requested]
  apply bind_keeps source receipts _ _ (queries (.inl (.hash request)) trivial)
  intro digest
  obtain ⟨selected, resumed, _state, _fingerprint, _hash, signing, signed, _key, role, _context, contextBytes, inputBytes⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact pending
      (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed]
  apply signing_keeps source receipts impl encode queries encoding _ digest selected signing signed
  refine ⟨?_, contextBytes, ?_⟩
  · simp only [role, TranscriptAuthInputsRefinement.absRole]
  · simpa only [RegistrationAuthenticationShared.digest_array_bytes] using inputBytes

private theorem fingerprint_keeps (pending : registration.BeaconFingerprint) :
    Keeps source receipts (fromFingerprint impl encode pending) := by
  unfold fromFingerprint
  apply continue_keeps
  intro request
  apply bind_keeps source receipts _ _ (queries (.inl (.hash request)) trivial)
  intro digest
  apply continue_keeps
  intro effect
  cases effect with
  | HashRequested next => exact hash_keeps source receipts impl encode queries encoding next
  | _ => exact pure_keeps source receipts _

/-- All three Ed stages, including optional failures, retain same-position raw-request/native-payload receipts through the actual effectful publication. -/
theorem ed_keeps (pending : registration.BeaconEd25519Signing) : Keeps source receipts (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps
  intro request
  apply bind_keeps source receipts _ _ (queries (.inr request) trivial)
  intro reply
  cases actual : pending.resume reply with
  | fail error | div => exact pure_keeps source receipts _
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_keeps next
    | FingerprintRequested next => exact fingerprint_keeps source receipts impl encode queries encoding next
    | _ => exact pure_keeps source receipts _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- Complete actual stateful Init publication derives request alignment internally and retains every failed prefix. -/
theorem begin_keeps (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Keeps source receipts (begin impl encode control inputs coins pin mldsa) := by
  unfold begin
  apply continue_keeps
  intro effect
  cases effect with
  | Ed25519SigningRequested next => exact ed_keeps source receipts impl encode queries encoding next
  | _ => exact pure_keeps source receipts _
end Beacon

namespace Server
open RegistrationNativePlatformServerPublication
attribute [local irreducible] registration.ServerResponseHash.resume registration.ServerResponseHash.request
  registration.ServerResponseSigning.resume registration.ServerResponseSigning.request
variable (receipts : Native → List RegistrationSigningShared.Receipt)
variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT Native (M (handleSource source) Platform)))
variable (encode : registration.SignedResponseView → StateT Native (M (handleSource source) Platform) (RustM (core.option.Option Encoded)))
variable (queries : ∀ query, SharedQuery query → Keeps source receipts (impl query))
variable (encoding : ∀ view, Keeps source receipts (encode view))

private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → StateT Native (M (handleSource source) Platform) (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (law : ∀ value, Keeps source receipts (next value)) : Keeps source receipts (continueWith action next) := by
  cases action with
  | ok value => exact law value
  | fail error | div => exact pure_keeps source receipts _

private theorem result_keeps {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT Native (M (handleSource source) Platform) (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (law : ∀ value, Keeps source receipts (next value)) : Keeps source receipts (continueResult action next) := by
  cases action with
  | ok answer => cases answer with
    | Ok value => exact law value
    | Err previous => exact pure_keeps source receipts _
  | fail error | div => exact pure_keeps source receipts _

include encoding in
private theorem ready_keeps (pending : registration.ServerResponseReady) : Keeps source receipts (ready encode pending) := by
  unfold ready
  exact continue_keeps source receipts _ _ (fun _ => bind_keeps source receipts _ _ (encoding _) (fun _ => pure_keeps source receipts _))

include queries encoding
private theorem signing_keeps (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (request : registration.MldsaSigningRequest)
    (requested : pending.request = .ok request) (correct : Correct request payload digest) :
    Keeps source receipts (signing impl encode payload digest pending) := by
  unfold signing
  rw [requested]
  apply bind_keeps source receipts _ _ (queries (.sign request payload digest) correct)
  intro reply
  exact result_keeps source receipts _ _ (ready_keeps source receipts encode encoding)

/-- The complete actual effectful response publication sends the full request for its own reached digest and payload, before any source encoding outcome. -/
theorem program_keeps (pending : registration.ServerResponseHash) : Keeps source receipts (program impl encode pending) := by
  obtain ⟨request, requested, _bytes⟩ := BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  unfold program
  rw [requested]
  apply bind_keeps source receipts _ _ (queries (.hash request) trivial)
  intro digest
  obtain ⟨selected, resumed, _candidate, _binding, _kernel, _ciphertext, inputBytes, requested⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending
      (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed]
  apply signing_keeps source receipts impl encode queries encoding _ digest selected _ requested
  exact ⟨rfl, TranscriptAuthInputsRefinement.signing_context_abs,
    by simpa only [RegistrationAuthenticationShared.digest_array_bytes] using inputBytes⟩
end Server

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.pure_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.pure_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.bind_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.bind_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Beacon.hash_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Beacon.hash_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Beacon.ed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Beacon.ed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Beacon.begin_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Beacon.begin_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Server.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology.Server.program_keeps
