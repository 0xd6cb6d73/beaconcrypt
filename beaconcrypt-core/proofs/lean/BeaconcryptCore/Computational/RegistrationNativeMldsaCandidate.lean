-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaEuf

/-! Executable complete-request extraction from native public verification operands and the retained shared cache. The extractor needs neither a generated secret nor a signing reply. Native weak message freshness transfers through the actual chronological primitive log, including failures. Actual selection of reached trials is a separate controller obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate
open RegistrationNativeMldsaEuf (PublicKey Forgery Fresh Valid)
open RegistrationNativeMldsaChronology (Aligned)
open MldsaTranscriptAuth (Trial Accepted WeakForgery)
open CtxRomAuth (CtxRO)

def role : Pqxdh.TranscriptAuth.Role → authentication.AuthRole
  | .beacon => .Beacon
  | .server => .Server

def digest (cache : CtxRO.QueryCache) (trial : Trial) : CtxRomAuth.CtxDigest :=
  (cache ((), trial.candidate.transcript)).getD (List.Vector.replicate 64 0)

/-- Run the deployed pure signing-input builder with the actual retained digest; fail closed on any unexpected source failure. -/
def extract (publicKey : PublicKey) (cache : CtxRO.QueryCache) (trial : Trial) : Option Forgery :=
  match authentication.build_signature_input (role trial.candidate.role)
      (RegistrationAuthenticationShared.digestArray (digest cache trial)) with
  | .ok input => some ⟨⟨publicKey, role trial.candidate.role, input, authentication.SIGNING_CONTEXT⟩, trial.signature⟩
  | .fail _ | .div => none

/-- Extraction is total and retains the exact FIPS context, role-separated message and candidate signature. -/
theorem extract_exact (publicKey : PublicKey) (cache : CtxRO.QueryCache) (trial : Trial) :
    ∃ forgery, extract publicKey cache trial = some forgery ∧
      forgery.request.public_key = publicKey ∧
      absBytes forgery.request.context = Pqxdh.TranscriptAuth.signingContext ∧
      absBytes forgery.request.input = trial.candidate.message (MldsaSharedAuthentication.cacheHash cache) ∧
      forgery.signature = trial.signature := by
  obtain ⟨input, built, bytes⟩ := TranscriptAuthInputsRefinement.build_signature_input_abs
    (role trial.candidate.role) (RegistrationAuthenticationShared.digestArray (digest cache trial))
  refine ⟨⟨⟨publicKey, role trial.candidate.role, input, authentication.SIGNING_CONTEXT⟩, trial.signature⟩,
    by simp only [extract, built], rfl, TranscriptAuthInputsRefinement.signing_context_abs, ?_, rfl⟩
  rw [bytes, RegistrationAuthenticationShared.digest_array_bytes]
  have sameRole : TranscriptAuthInputsRefinement.absRole (role trial.candidate.role) = trial.candidate.role := by
    cases trial.candidate.role <;> rfl
  rw [sameRole]
  rfl

/-- An actual accepted native trial yields a valid ordinary complete-request forgery at its displayed key. -/
theorem extract_valid (source : RegistrationNativeMldsa.Source) (publicKey : PublicKey)
    (cache : CtxRO.QueryCache) (trial : Trial) (forgery : Forgery)
    (extracted : extract publicKey cache trial = some forgery)
    (key : trial.publicKey = absBytes publicKey)
    (accepted : Accepted (MldsaSharedAuthentication.cacheHash cache) source.verify trial) :
    Valid source publicKey forgery := by
  obtain ⟨found, same, keyEq, context, input, signature⟩ := extract_exact publicKey cache trial
  have equal : found = forgery := Option.some.inj (same.symm.trans extracted)
  subst found
  exact ⟨keyEq, signature ▸ accepted.2.2.1, by rw [context, input, signature, ← key]; exact accepted.2.2.2⟩

/-- All reached raw requests to a displayed public key, retaining even failed replies. -/
def requestsFor (publicKey : PublicKey) (attempts : List RegistrationNativeMldsaOpaque.Attempt) :
    List registration.MldsaSigningRequest :=
  (attempts.filter fun attempt => absBytes attempt.request.public_key == absBytes publicKey).map (·.request)

/-- Actual chronological native weak freshness implies ordinary complete-request freshness for every same-key primitive attempt. -/
theorem extract_fresh (publicKey : PublicKey) (attempts : List RegistrationNativeMldsaOpaque.Attempt)
    (state : RegistrationSigningShared.State) (aligned : Aligned attempts state.1)
    (cached : RegistrationSigningShared.Cached state) (trial : Trial) (verify : MldsaTranscriptAuth.Verify)
    (history : trial.history = RegistrationSigningShared.historyFor trial.publicKey state)
    (weak : WeakForgery (MldsaSharedAuthentication.cacheHash state.2) verify trial)
    (key : trial.publicKey = absBytes publicKey) (forgery : Forgery)
    (extracted : extract publicKey state.2 trial = some forgery) :
    Fresh (requestsFor publicKey attempts) forgery := by
  obtain ⟨found, same, _public, _context, input, _signature⟩ := extract_exact publicKey state.2 trial
  have equal : found = forgery := Option.some.inj (same.symm.trans extracted)
  subst found
  intro request member equal
  obtain ⟨attempt, selected, requestEq⟩ := List.mem_map.mp member
  obtain ⟨reached, target⟩ := List.mem_filter.mp selected
  have targetEq : absBytes attempt.request.public_key = trial.publicKey := by
    rw [key]
    simpa only [beq_iff_eq] using target
  have fresh := RegistrationNativeMldsaChronology.fresh attempts state aligned cached trial verify history weak attempt reached targetEq
  apply fresh
  rw [requestEq]
  exact (congrArg absBytes (congrArg Prod.snd equal)).trans input

/-- The verifier may add hashes after the earlier signing prefix. Its actual cache extension retains precisely the freshness needed by extraction. -/
theorem extract_fresh_extended (publicKey : PublicKey) (attempts : List RegistrationNativeMldsaOpaque.Attempt)
    (state : RegistrationSigningShared.State) (after : CtxRO.QueryCache)
    (aligned : Aligned attempts state.1) (cached : RegistrationSigningShared.Cached state)
    (extension : state.2 ≤ after) (trial : Trial) (verify : MldsaTranscriptAuth.Verify)
    (history : trial.history = RegistrationSigningShared.historyFor trial.publicKey state)
    (weak : WeakForgery (MldsaSharedAuthentication.cacheHash after) verify trial)
    (key : trial.publicKey = absBytes publicKey) (forgery : Forgery)
    (extracted : extract publicKey after trial = some forgery) :
    Fresh (requestsFor publicKey attempts) forgery :=
  extract_fresh publicKey attempts (state.1, after) aligned
    (RegistrationSigningShared.cached_extend state.1 state.2 after extension cached) trial verify history weak key forgery extracted

/-- A chosen-key oracle may retain a subsequence of same-key raw requests; its complete-request freshness follows without deleting any attempted raw query. -/
theorem fresh_sublist (forgery : Forgery) (full selected : List registration.MldsaSigningRequest)
    (fresh : Fresh full forgery) (included : ∀ request ∈ selected, request ∈ full) : Fresh selected forgery :=
  fun request member => fresh request (included request member)

end BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.fresh_sublist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.fresh_sublist

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_fresh_extended' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate.extract_fresh_extended
