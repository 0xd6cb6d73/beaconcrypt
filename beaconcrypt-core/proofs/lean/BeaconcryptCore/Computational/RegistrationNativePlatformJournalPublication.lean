-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication
/-! The actual stateful Beacon and Server publication stages recover their unsigned ML payload and digest from the preceding private chronological hash cut. Source request-only signing equals the explicit native metadata-bearing signing call through arbitrary effectful serialization, including all later failures and complete shared poststates. No codec law, encoder purity, hash-cache inversion or caller-provided transcript-alignment premise is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open RegistrationNativePlatformSigningJournal
variable {n : Nat} {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
attribute [local irreducible] registration.BeaconFingerprint.resume registration.BeaconFingerprint.request
  registration.BeaconInitHash.resume registration.BeaconInitHash.request
  registration.BeaconMldsaSigning.resume registration.BeaconMldsaSigning.request
  registration.BeaconEd25519Signing.resume registration.BeaconEd25519Signing.request
  registration.ServerResponseHash.resume registration.ServerResponseHash.request
  registration.ServerResponseSigning.resume registration.ServerResponseSigning.request
variable (coins : QueryImpl unifSpec m) (primitive : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

def extended (impl : QueryImpl RegistrationSigningShared.Spec (StateT (State n) m))
    (ed : registration.Ed25519SigningRequest → StateT (State n) m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (State n) m)
  | .inl query => impl query
  | .inr request => ed request

omit [LawfulMonad m] in
private theorem sign_aligned (request : registration.MldsaSigningRequest)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (cut : Cut)
    (aligned : cut.payload request.role = payload) (sameDigest : cut.digest = digest)
    (before : RegistrationWorldSigning.State n) :
    ((source coins primitive) (.sign request payload digest)).run (before, some cut) =
      ((forward coins primitive) (.sign request payload digest)).run (before, some cut) := by
  change (liftNative coins (RegistrationWorldSigning.outgoing primitive (.sign request (cut.payload request.role) cut.digest))).run _ = _
  rw [aligned, sameDigest]
  rfl

omit [LawfulMonad m] in
private theorem beacon_signing
    (ed : registration.Ed25519SigningRequest → StateT (State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconMldsaSigning) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (cut : Cut) (aligned : ∀ request, pending.request = .ok request → cut.payload request.role = payload)
    (sameDigest : cut.digest = digest) (before : RegistrationWorldSigning.State n) :
    (RegistrationNativePlatformBeaconPublication.fromSigning (extended (source coins primitive) ed) encode payload digest pending).run
      (before, some cut) =
    (RegistrationNativePlatformBeaconPublication.fromSigning (extended (forward coins primitive) ed) encode payload digest pending).run
      (before, some cut) := by
  unfold RegistrationNativePlatformBeaconPublication.fromSigning
  cases requested : pending.request with
  | fail error | div => rfl
  | ok request =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, extended, StateT.run_bind]
      rw [sign_aligned coins primitive request payload digest cut (aligned request requested) sameDigest]

theorem beacon_hash
    (ed : registration.Ed25519SigningRequest → StateT (State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) (before : State n) :
    (RegistrationNativePlatformBeaconPublication.fromHash (extended (source coins primitive) ed) encode pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromHash (extended (forward coins primitive) ed) encode pending).run before := by
  obtain ⟨request, requested, transcript⟩ := BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.beacon pending)
  change pending.request = .ok request at requested
  unfold RegistrationNativePlatformBeaconPublication.fromHash
  rw [requested]
  simp only [RegistrationNativePlatformBeaconPublication.continueWith, extended, source, forward,
    StateT.run_bind]
  rw [hash_run]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  obtain ⟨signing, resumed, _state, _fingerprint, _digest, selected, selectedRun, _key, role, _context, _contextBytes, _input⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray result.1)
  rw [resumed]
  simp only
  apply beacon_signing coins primitive ed encode signing ⟨.beacon, hashBytes request⟩ result.1 _ _ rfl result.2
  intro other otherRun
  have same : other = selected := RustM.ok.inj (otherRun.symm.trans selectedRun)
  subst other
  simp only [Cut.payload, role, TranscriptAuthInputsRefinement.absRole]

omit [LawfulMonad m] in
private theorem server_signing
    (encode : registration.SignedResponseView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseSigning) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (cut : Cut) (aligned : ∀ request, pending.request = .ok request → cut.payload request.role = payload)
    (sameDigest : cut.digest = digest) (before : RegistrationWorldSigning.State n) :
    (RegistrationNativePlatformServerPublication.signing (source coins primitive) encode payload digest pending).run (before, some cut) =
      (RegistrationNativePlatformServerPublication.signing (forward coins primitive) encode payload digest pending).run (before, some cut) := by
  unfold RegistrationNativePlatformServerPublication.signing
  cases requested : pending.request with
  | fail error | div => rfl
  | ok request =>
      simp only [RegistrationNativePlatformServerPublication.continueWith, StateT.run_bind]
      rw [sign_aligned coins primitive request payload digest cut (aligned request requested) sameDigest]

theorem server
    (encode : registration.SignedResponseView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (before : State n) :
    (RegistrationNativePlatformServerPublication.program (source coins primitive) encode pending).run before =
      (RegistrationNativePlatformServerPublication.program (forward coins primitive) encode pending).run before := by
  obtain ⟨request, requested, transcript⟩ := BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  unfold RegistrationNativePlatformServerPublication.program
  rw [requested]
  simp only [RegistrationNativePlatformServerPublication.continueWith, source, forward,
    StateT.run_bind]
  rw [hash_run]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  obtain ⟨signing, resumed, _candidate, _binding, _kernel, _ciphertext, _message, signingRun⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending (RegistrationAuthenticationShared.digestArray result.1)
  rw [resumed]
  simp only [RegistrationNativePlatformServerPublication.continueResult]
  apply server_signing coins primitive encode signing ⟨.server, hashBytes request⟩ result.1 _ _ rfl result.2
  intro selected selectedRun
  have same : selected = _ := RustM.ok.inj (selectedRun.symm.trans signingRun)
  subst selected
  rfl

theorem beacon_fingerprint
    (ed : registration.Ed25519SigningRequest → StateT (State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconFingerprint) (before : State n) :
    (RegistrationNativePlatformBeaconPublication.fromFingerprint (extended (source coins primitive) ed) encode pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromFingerprint (extended (forward coins primitive) ed) encode pending).run before := by
  unfold RegistrationNativePlatformBeaconPublication.fromFingerprint
  cases requested : pending.request with
  | fail error | div => rfl
  | ok request =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, extended, source, forward, StateT.run_bind]
      apply bind_congr
      intro result
      obtain ⟨hashing, resumed, _state, _fingerprint, _request⟩ :=
        BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_fingerprint_some_exact pending
          (RegistrationAuthenticationShared.digestArray result.1)
      rw [resumed]
      exact beacon_hash coins primitive ed encode hashing result.2

theorem beacon_ed
    (ed : registration.Ed25519SigningRequest → StateT (State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) (before : State n) :
    (RegistrationNativePlatformBeaconPublication.fromEd (extended (source coins primitive) ed) encode pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd (extended (forward coins primitive) ed) encode pending).run before := by
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def,
    RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  cases requested : pending.request with
  | fail error | div => rfl
  | ok request =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, extended, StateT.run_bind]
      apply bind_congr
      intro result
      cases resumed : pending.resume result.1 with
      | fail error | div => rfl
      | ok effect => cases effect with
        | Ed25519SigningRequested next => exact beacon_ed ed encode next result.2
        | FingerprintRequested next => exact beacon_fingerprint coins primitive ed encode next result.2
        | _ => rfl
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending result.1 next resumed

theorem beacon_begin
    (ed : registration.Ed25519SigningRequest → StateT (State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) (before : State n) :
    (RegistrationNativePlatformBeaconPublication.begin (extended (source coins primitive) ed) encode control inputs scalar pin mldsa).run before =
      (RegistrationNativePlatformBeaconPublication.begin (extended (forward coins primitive) ed) encode control inputs scalar pin mldsa).run before := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  cases begun : registration.begin_beacon_init control inputs scalar pin mldsa with
  | fail error | div => rfl
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact beacon_ed coins primitive ed encode next before
    | _ => rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_fingerprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_ed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication.beacon_begin
