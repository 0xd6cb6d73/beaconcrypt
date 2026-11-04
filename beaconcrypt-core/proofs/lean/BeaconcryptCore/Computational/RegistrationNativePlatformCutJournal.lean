-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSigningJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication
/-! A private source hash-cut journal for arbitrary stateful signing interpreters. The actual stateful Beacon and Server publication stages recover their unsigned ML payload and digest from the preceding private chronological hash cut. Source request-only signing equals the explicit native metadata-bearing signing call through arbitrary effectful serialization, including all later failures and complete shared poststates. No codec law, encoder purity, hash-cache inversion or caller-provided transcript-alignment premise is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open RegistrationNativePlatformSigningJournal (Cut)
variable {S : Type} {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
attribute [local irreducible] registration.BeaconFingerprint.resume registration.BeaconFingerprint.request
  registration.BeaconInitHash.resume registration.BeaconInitHash.request
  registration.BeaconMldsaSigning.resume registration.BeaconMldsaSigning.request
  registration.BeaconEd25519Signing.resume registration.BeaconEd25519Signing.request
  registration.ServerResponseHash.resume registration.ServerResponseHash.request
  registration.ServerResponseSigning.resume registration.ServerResponseSigning.request
abbrev State (S : Type) := S × Option Cut

def liftNative {Value : Type} (work : StateT S m Value) : StateT (State S) m Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
variable (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)

def hash (request : registration.HashRequest) : StateT (State S) m CtxRomAuth.CtxDigest := do
  let digest ← liftNative (impl (.hash request))
  modify fun before => (before.1, some ⟨request, digest⟩)
  pure digest

noncomputable def sign (request : registration.MldsaSigningRequest) : StateT (State S) m RegistrationSigningShared.SignReply := fun before =>
  match before.2 with
  | none => (liftNative (fallback request)).run before
  | some cut => (liftNative (impl (.sign request (cut.payload request.role) cut.digest))).run before

noncomputable def forward : QueryImpl RegistrationSigningShared.Spec (StateT (State S) m)
  | .hash request => hash impl request
  | .sign request payload digest => liftNative (impl (.sign request payload digest))

noncomputable def source : QueryImpl RegistrationSigningShared.Spec (StateT (State S) m)
  | .hash request => hash impl request
  | .sign request _ _ => sign impl fallback request

theorem hash_run (request : registration.HashRequest) (before : State S) :
    (hash impl request).run before =
      (fun result => (result.1, (result.2, some (⟨request, result.1⟩ : Cut)))) <$> (impl (.hash request)).run before.1 := by
  simp only [hash, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
  change ((fun result => (result.1, (result.2, before.2))) <$> (impl (.hash request)).run before.1 >>=
    fun result => pure (result.1, (result.2.1, some (⟨request, result.1⟩ : Cut)))) = _
  simp only [bind_pure_comp, Functor.map_map]


def extended (impl : QueryImpl RegistrationSigningShared.Spec (StateT (State S) m))
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (State S) m)
  | .inl query => impl query
  | .inr request => ed request

omit [LawfulMonad m] in
private theorem sign_aligned (request : registration.MldsaSigningRequest)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (cut : Cut)
    (aligned : cut.payload request.role = payload) (sameDigest : cut.digest = digest)
    (before : S) :
    ((source impl fallback) (.sign request payload digest)).run (before, some cut) =
      ((forward impl) (.sign request payload digest)).run (before, some cut) := by
  change (liftNative (impl (.sign request (cut.payload request.role) cut.digest))).run _ = _
  rw [aligned, sameDigest]
  rfl

omit [LawfulMonad m] in
private theorem beacon_signing
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconMldsaSigning) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (cut : Cut) (aligned : ∀ request, pending.request = .ok request → cut.payload request.role = payload)
    (sameDigest : cut.digest = digest) (before : S) :
    (RegistrationNativePlatformBeaconPublication.fromSigning (extended (source impl fallback) ed) encode payload digest pending).run
      (before, some cut) =
    (RegistrationNativePlatformBeaconPublication.fromSigning (extended (forward impl) ed) encode payload digest pending).run
      (before, some cut) := by
  unfold RegistrationNativePlatformBeaconPublication.fromSigning
  cases requested : pending.request with
  | fail error | div => rfl
  | ok request =>
      simp only [RegistrationNativePlatformBeaconPublication.continueWith, extended, StateT.run_bind]
      rw [sign_aligned impl fallback request payload digest cut (aligned request requested) sameDigest]

theorem beacon_hash
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) (before : State S) :
    (RegistrationNativePlatformBeaconPublication.fromHash (extended (source impl fallback) ed) encode pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromHash (extended (forward impl) ed) encode pending).run before := by
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
  apply beacon_signing impl fallback ed encode signing ⟨.beacon, hashBytes request⟩ result.1 _ _ rfl result.2
  intro other otherRun
  have same : other = selected := RustM.ok.inj (otherRun.symm.trans selectedRun)
  subst other
  simp only [Cut.payload, role, TranscriptAuthInputsRefinement.absRole]

omit [LawfulMonad m] in
private theorem server_signing
    (encode : registration.SignedResponseView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseSigning) (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (cut : Cut) (aligned : ∀ request, pending.request = .ok request → cut.payload request.role = payload)
    (sameDigest : cut.digest = digest) (before : S) :
    (RegistrationNativePlatformServerPublication.signing (source impl fallback) encode payload digest pending).run (before, some cut) =
      (RegistrationNativePlatformServerPublication.signing (forward impl) encode payload digest pending).run (before, some cut) := by
  unfold RegistrationNativePlatformServerPublication.signing
  cases requested : pending.request with
  | fail error | div => rfl
  | ok request =>
      simp only [RegistrationNativePlatformServerPublication.continueWith, StateT.run_bind]
      rw [sign_aligned impl fallback request payload digest cut (aligned request requested) sameDigest]

theorem server
    (encode : registration.SignedResponseView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (before : State S) :
    (RegistrationNativePlatformServerPublication.program (source impl fallback) encode pending).run before =
      (RegistrationNativePlatformServerPublication.program (forward impl) encode pending).run before := by
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
  apply server_signing impl fallback encode signing ⟨.server, hashBytes request⟩ result.1 _ _ rfl result.2
  intro selected selectedRun
  have same : selected = _ := RustM.ok.inj (selectedRun.symm.trans signingRun)
  subst selected
  rfl

theorem beacon_fingerprint
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconFingerprint) (before : State S) :
    (RegistrationNativePlatformBeaconPublication.fromFingerprint (extended (source impl fallback) ed) encode pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromFingerprint (extended (forward impl) ed) encode pending).run before := by
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
      exact beacon_hash impl fallback ed encode hashing result.2

theorem beacon_ed
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) (before : State S) :
    (RegistrationNativePlatformBeaconPublication.fromEd (extended (source impl fallback) ed) encode pending).run before =
      (RegistrationNativePlatformBeaconPublication.fromEd (extended (forward impl) ed) encode pending).run before := by
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
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
        | FingerprintRequested next => exact beacon_fingerprint impl fallback ed encode next result.2
        | _ => rfl
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending result.1 next resumed

private theorem beacon_start
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (action : RustM registration.BeaconInitEffect) (before : State S) :
    (RegistrationNativePlatformBeaconPublication.continueWith (Encoded := Encoded) (m := StateT (State S) m) action (fun effect => match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .Ed25519SigningRequested selected => RegistrationNativePlatformBeaconPublication.fromEd (extended (source impl fallback) ed) encode selected
      | _ => pure .div)).run before =
    (RegistrationNativePlatformBeaconPublication.continueWith (Encoded := Encoded) (m := StateT (State S) m) action (fun effect => match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .Ed25519SigningRequested selected => RegistrationNativePlatformBeaconPublication.fromEd (extended (forward impl) ed) encode selected
      | _ => pure .div)).run before := by
  let left : registration.BeaconInitEffect → StateT (State S) m (RustM (RegistrationBeaconInitExecutor.Result Encoded)) := fun effect =>
    match effect with
    | .Rejected previous => pure (.ok (.Err previous))
    | .Ed25519SigningRequested selected => RegistrationNativePlatformBeaconPublication.fromEd (extended (source impl fallback) ed) encode selected
    | _ => pure .div
  let right : registration.BeaconInitEffect → StateT (State S) m (RustM (RegistrationBeaconInitExecutor.Result Encoded)) := fun effect =>
    match effect with
    | .Rejected previous => pure (.ok (.Err previous))
    | .Ed25519SigningRequested selected => RegistrationNativePlatformBeaconPublication.fromEd (extended (forward impl) ed) encode selected
    | _ => pure .div
  have same : left = right := by
    funext effect
    cases effect with
    | Ed25519SigningRequested next =>
        apply StateT.ext
        intro current
        exact beacon_ed impl fallback ed encode next current
    | _ => rfl
  exact congrArg (fun next => (RegistrationNativePlatformBeaconPublication.continueWith
    (Encoded := Encoded) (m := StateT (State S) m) action next).run before) same

theorem beacon_begin
    (ed : registration.Ed25519SigningRequest → StateT (State S) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (State S) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) (before : State S) :
    (RegistrationNativePlatformBeaconPublication.begin (extended (source impl fallback) ed) encode control inputs scalar pin mldsa).run before =
      (RegistrationNativePlatformBeaconPublication.begin (extended (forward impl) ed) encode control inputs scalar pin mldsa).run before := by
  exact beacon_start impl fallback ed encode (registration.begin_beacon_init control inputs scalar pin mldsa) before
end BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.hash_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.hash_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_fingerprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_ed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal.beacon_begin
