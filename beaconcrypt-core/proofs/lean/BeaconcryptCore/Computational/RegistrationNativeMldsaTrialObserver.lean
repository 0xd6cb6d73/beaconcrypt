-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate
import BeaconcryptCore.Computational.RegistrationNativeInitFinal
import BeaconcryptCore.Computational.RegistrationNativeResponseFinish

/-! A deterministic observer inspects the actual completed typed accept/finish callback, its displayed public authentication operands and retained shared cache. It selects only a matching challenge public key with native weak message freshness, using the actual prior unsigned signing prefix. No secret credential is read and no future signing history is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver
open RegistrationNativeMldsaEuf (PublicKey Forgery)
open RegistrationNativeMldsaCandidate (extract)
open CtxRomAuth (CtxRO)
open MldsaTranscriptAuth (Trial WeakForgery Accepted)
variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}

/-- Only finite public request operands, verification and already retained history/cache are tested. -/
def eligible (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey) (cache : CtxRO.QueryCache) (trial : Trial) : Bool :=
  trial.publicKey == absBytes publicKey && trial.protectedKey && decide (trial.publicKey.length = 1952) &&
    decide (trial.signature.length = 3309) &&
    verify trial.publicKey Pqxdh.TranscriptAuth.signingContext
      (trial.candidate.message (MldsaSharedAuthentication.cacheHash cache)) trial.signature &&
    trial.history.all (fun call => call.payload.message (MldsaSharedAuthentication.cacheHash cache) !=
      trial.candidate.message (MldsaSharedAuthentication.cacheHash cache))

theorem eligible_iff (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey) (cache : CtxRO.QueryCache) (trial : Trial) :
    eligible verify publicKey cache trial = true ↔ trial.publicKey = absBytes publicKey ∧
      WeakForgery (MldsaSharedAuthentication.cacheHash cache) verify trial := by
  simp only [eligible, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    WeakForgery, Accepted]
  tauto

def choose (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey) (cache : CtxRO.QueryCache) (trial : Trial) : Option Forgery :=
  if eligible verify publicKey cache trial then extract publicKey cache trial else none

/-- Every selected candidate is the exact pure extraction of a same-key, native weak forgery at this callback cut. -/
theorem choose_sound (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey) (cache : CtxRO.QueryCache)
    (trial : Trial) (forgery : Forgery) (chosen : choose verify publicKey cache trial = some forgery) :
    extract publicKey cache trial = some forgery ∧ trial.publicKey = absBytes publicKey ∧
      WeakForgery (MldsaSharedAuthentication.cacheHash cache) verify trial := by
  unfold choose at chosen
  split at chosen
  · exact ⟨chosen, (eligible_iff verify publicKey cache trial).mp ‹_›⟩
  · cases chosen

/-- Every same-key native weak forgery is selected, with no signature-success or publication assumption added. -/
theorem choose_complete (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey) (cache : CtxRO.QueryCache)
    (trial : Trial) (key : trial.publicKey = absBytes publicKey)
    (weak : WeakForgery (MldsaSharedAuthentication.cacheHash cache) verify trial) :
    ∃ forgery, choose verify publicKey cache trial = some forgery := by
  obtain ⟨forgery, extracted, _rest⟩ := RegistrationNativeMldsaCandidate.extract_exact publicKey cache trial
  exact ⟨forgery, by rw [choose, ite_eq_left ((eligible_iff verify publicKey cache trial).mpr ⟨key, weak⟩), extracted]⟩

/-- The concrete reached trial for a successful original typed authentication callback. Other replies select nothing. -/
def trial (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) : Option Trial :=
  match query with
  | .inr (.accept packet) => match reply with
    | .ok (some _) => some (RegistrationAuthenticationNative.trial true before.server.pin packet
        (RegistrationSigningShared.historyFor (absBytes packet.mldsa_public_key) (RegistrationNativeMldsaShared.nativeProject before)))
    | _ => none
  | .inr (.finish index (some packet)) => match reply with
    | .ok (some _) => match before.beacons[index]? with
      | some owner => match owner.phase with
        | .initSent pending _ => some (RegistrationResponseExecutor.trial true pending packet
            (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key)
              (RegistrationNativeMldsaShared.nativeProject before)))
        | _ => none
      | none => none
    | _ => none
  | _ => none

/-- Every constructed trial uses exactly the target key's pre-callback native unsigned history. -/
theorem trial_history (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (candidate : Trial)
    (selected : trial query before reply = some candidate) :
    candidate.history = RegistrationSigningShared.historyFor candidate.publicKey (RegistrationNativeMldsaShared.nativeProject before) := by
  cases query with
  | inl coin => cases selected
  | inr query => cases query with
    | accept packet =>
        cases reply with
        | fail error | div => cases selected
        | ok option => cases option with
          | none => cases selected
          | some session =>
              simp only [trial, Option.some.injEq] at selected
              subst candidate
              rfl
    | finish index packet =>
        cases packet with
        | none => cases selected
        | some packet =>
            cases reply with
            | fail error | div => cases selected
            | ok option => cases option with
              | none => cases selected
              | some application =>
                  simp only [trial] at selected
                  cases found : before.beacons[index]? with
                  | none => simp only [found, reduceCtorEq] at selected
                  | some owner =>
                      simp only [found] at selected
                      cases phase : owner.phase with
                      | initSent pending oneTime =>
                          simp only [phase, Option.some.injEq] at selected
                          subst candidate
                          rfl
                      | _ => simp only [phase, reduceCtorEq] at selected
    | _ => cases selected

/-- The online observer takes the actual post-callback cache and the exact pre-callback trial operands. -/
def observe (verify : MldsaTranscriptAuth.Verify) (publicKey : PublicKey)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (after : RegistrationNativeExperiment.State n KemSK source) : Option Forgery :=
  (trial query before reply).bind fun candidate => choose verify publicKey after.server.world.world.1.primitive.2 candidate

/-- Actual selection produces a valid ordinary-EUF candidate immediately, without inspecting a private secret or future state. -/
theorem observe_valid (publicKey : PublicKey) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : RegistrationNativeExperiment.State n KemSK source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (forgery : Forgery)
    (selected : observe source.verify publicKey query before reply after = some forgery) :
    RegistrationNativeMldsaEuf.Valid source publicKey forgery := by
  unfold observe at selected
  cases reached : trial query before reply with
  | none => simp only [reached, Option.bind_none, reduceCtorEq] at selected
  | some candidate =>
      simp only [reached, Option.bind_some] at selected
      obtain ⟨extracted, key, weak⟩ := choose_sound source.verify publicKey _ candidate forgery selected
      exact RegistrationNativeMldsaCandidate.extract_valid source publicKey _ candidate forgery extracted key weak.1

/-- A selected callback candidate is fresh against all actual same-key primitive attempts preceding that callback, even though verification extends the shared cache. -/
theorem observe_fresh (publicKey : PublicKey) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : RegistrationNativeExperiment.State n KemSK source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (forgery : Forgery)
    (attempts : List RegistrationNativeMldsaOpaque.Attempt)
    (aligned : RegistrationNativeMldsaChronology.Aligned attempts (RegistrationNativeMldsaShared.nativeProject before).1)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (extension : (RegistrationNativeMldsaShared.nativeProject before).2 ≤ after.server.world.world.1.primitive.2)
    (selected : observe source.verify publicKey query before reply after = some forgery) :
    RegistrationNativeMldsaEuf.Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey attempts) forgery := by
  unfold observe at selected
  cases reached : trial query before reply with
  | none => simp only [reached, Option.bind_none, reduceCtorEq] at selected
  | some candidate =>
      simp only [reached, Option.bind_some] at selected
      obtain ⟨extracted, key, weak⟩ := choose_sound source.verify publicKey _ candidate forgery selected
      exact RegistrationNativeMldsaCandidate.extract_fresh_extended publicKey attempts
        (RegistrationNativeMldsaShared.nativeProject before) after.server.world.world.1.primitive.2 aligned cached extension
        candidate source.verify (trial_history query before reply candidate reached) weak key forgery extracted

end BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.eligible_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.eligible_iff

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.choose_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.choose_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.choose_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.choose_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.observe_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.observe_valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.trial_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.trial_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.observe_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver.observe_fresh
