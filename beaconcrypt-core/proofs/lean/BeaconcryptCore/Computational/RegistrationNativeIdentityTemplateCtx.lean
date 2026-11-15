-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReindexedCtx
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateAddress
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture

/-! Each public template is a separate symbolic ROM key. Recognition stops physical/public overlap, while exact framing preserves every repeated hidden alias. Only private realization receives the canonical signature; the executable table, installation and recognition client do not. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx
open PqxdhEd25519EufCma (Ed25519PublicKey Ed25519Signature)
open RegistrationNativeIdentityTemplateAddress (Key Frame Admitted)
open RegistrationNativeIdentityRecognitionCapture (capture)
open RegistrationNativeIdentityReindexedCtx (ByteCache HashSpec State unitCache)
variable {Value : Type}

def WellFormed : Key → Prop
  | .inl _ => True
  | .inr frame => frame.1.length = 2188

def recognize (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) : Key → Option Ed25519Signature
  | .inl input => RegistrationNativeIdentityRecognition.recognize verify publicKey message input
  | .inr _ => none

private theorem captured_query {Index Witness : Type} {queries : OracleSpec Index}
    (recognizer : queries.Domain → Option Witness) (query : queries.Domain)
    (next : queries.Range query → OracleComp queries Value) :
    capture recognizer (queries.query query >>= next) =
      (match recognizer query with
      | some witness => pure (.inl witness)
      | none => do let reply ← queries.query query; capture recognizer (next reply)) := rfl

private theorem guarded (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (work : OracleComp (HashSpec Key) Value)
    (formed : work.AllQueriesSatisfy WellFormed) :
    (capture (recognize verify publicKey message) work).AllQueriesSatisfy (Admitted verify publicKey message) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp formed
    rw [captured_query]
    cases found : recognize verify publicKey message query with
    | some witness => trivial
    | none =>
      apply (allQueriesSatisfy_query_bind_iff _ _ _).mpr
      refine ⟨?_, fun reply => ih reply (later reply)⟩
      cases query with
      | inl input => exact found
      | inr frame => exact first

/-- All guarded templates and unrecognized public addresses have their exact physical cache, input journal and per-call draw costs. -/
theorem source (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (work : OracleComp (HashSpec Key) Value)
    (formed : work.AllQueriesSatisfy WellFormed) (before : State Key) :
    Prod.map id (RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
      (RegistrationNativeIdentityTemplateAddress.abstract signature)) <$>
      (simulateQ RegistrationNativeIdentityReindexedCtx.implementation (capture (recognize verify publicKey message) work)).run before =
      (simulateQ (fun query => RegistrationNativePlatformCtxBackend.physical (RegistrationNativeIdentityTemplateAddress.realize signature query))
        (capture (recognize verify publicKey message) work)).run
          (RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
            (RegistrationNativeIdentityTemplateAddress.abstract signature) before) := by
  apply RegistrationNativeIdentityReindexedCtx.program _ _ (RegistrationNativeIdentityTemplateAddress.realize_abstract signature)
  exact (guarded verify publicKey message work formed).mono fun key admitted =>
    RegistrationNativeIdentityTemplateAddress.abstract_admitted verify publicKey message signature valid key admitted

/-- Recognition is the explicit only loss when the literal physical continuation is compared with this alias-preserving executable table. -/
theorem loss (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (work : OracleComp (HashSpec Key) Value)
    (formed : work.AllQueriesSatisfy WellFormed) (before : State Key)
    (event : Value × RegistrationNativePlatformCtxBackend.State → Prop) :
    Pr{let result ← ((simulateQ (fun query => RegistrationNativePlatformCtxBackend.physical
      (RegistrationNativeIdentityTemplateAddress.realize signature query)) work).run
        (RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
          (RegistrationNativeIdentityTemplateAddress.abstract signature) before))}[event result] ≤
      Pr{let result ← ((simulateQ RegistrationNativeIdentityReindexedCtx.implementation
        (capture (recognize verify publicKey message) work)).run before)}[∃ witness, result.1 = .inl witness] +
      Pr{let result ← ((simulateQ RegistrationNativeIdentityReindexedCtx.implementation
        (capture (recognize verify publicKey message) work)).run before)}[
          ∃ value, result.1 = .inr value ∧ event (value,
            RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
              (RegistrationNativeIdentityTemplateAddress.abstract signature) result.2)] := by
  have upper := RegistrationNativeIdentityRecognitionCapture.cover
    (fun query => RegistrationNativePlatformCtxBackend.physical (RegistrationNativeIdentityTemplateAddress.realize signature query))
    (recognize verify publicKey message) work event
    (RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
      (RegistrationNativeIdentityTemplateAddress.abstract signature) before)
  rw [← source verify publicKey message signature valid work formed before] at upper
  simpa only [prEvent_map, Prod.map_def, id_eq] using upper

/-- Installation copies only existing known-input cache/journal; hidden template entries start empty without receiving a signature. -/
def install (cache : ByteCache) (journal : List Pqxdh.Bytes) : State Key :=
  (⟨fun key => match key with | .inl bytes => cache bytes | .inr _ => none⟩, journal.map Sum.inl)

/-- No earlier recognized address makes private installation preserve the literal warm cache and chronological input list. -/
theorem initial (signature : Ed25519Signature) (cache : ByteCache) (journal : List Pqxdh.Bytes)
    (fresh : ∀ frame : Frame, cache (RegistrationNativeIdentityTemplateAddress.realize signature (.inr frame)) = none) :
    RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
      (RegistrationNativeIdentityTemplateAddress.abstract signature) (install cache journal) = (unitCache cache, journal) := by
  have table : RegistrationNativeIdentityReindexedRom.project (RegistrationNativeIdentityTemplateAddress.abstract signature) (install cache journal).1 = cache := by
    apply QueryCache.ext
    intro input
    change (install cache journal).1 (RegistrationNativeIdentityTemplateAddress.abstract signature input) = cache input
    have actual := RegistrationNativeIdentityTemplateAddress.realize_abstract signature input
    cases indexed : RegistrationNativeIdentityTemplateAddress.abstract signature input with
    | inl bytes =>
      rw [indexed] at actual
      change bytes = input at actual
      change cache bytes = cache input
      cases actual
      rfl
    | inr frame =>
      rw [indexed] at actual
      change none = cache input
      rw [← actual]
      exact (fresh frame).symm
  change (unitCache (RegistrationNativeIdentityReindexedRom.project (RegistrationNativeIdentityTemplateAddress.abstract signature) (install cache journal).1),
    (install cache journal).2.map (RegistrationNativeIdentityTemplateAddress.realize signature)) = (unitCache cache, journal)
  rw [table]
  change (unitCache cache, (journal.map Sum.inl).map (RegistrationNativeIdentityTemplateAddress.realize signature)) = (unitCache cache, journal)
  rw [List.map_map]
  change (unitCache cache, journal.map id) = (unitCache cache, journal)
  rw [List.map_id]

/-- Actual cache provenance and the recorded no-recognition prefix discharge every template cache miss, regardless of how public framing varies. -/
theorem cache_miss (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (signature : Ed25519Signature)
    (valid : verify publicKey message signature = true) (cache : ByteCache) (journal : List Pqxdh.Bytes)
    (known : ∀ input digest, cache input = some digest → input ∈ journal)
    (unrecognized : ∀ input ∈ journal, RegistrationNativeIdentityRecognition.recognize verify publicKey message input = none) :
    ∀ frame : Frame, cache (RegistrationNativeIdentityTemplateAddress.realize signature (.inr frame)) = none := by
  intro frame
  cases stored : cache (RegistrationNativeIdentityTemplateAddress.realize signature (.inr frame)) with
  | none => rfl
  | some digest =>
    have missing := unrecognized _ (known _ digest stored)
    exact False.elim (RegistrationNativeIdentityRecognition.no_hit verify publicKey message frame.1 frame.2 _ signature valid missing rfl)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.loss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.cache_miss' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx.cache_miss
