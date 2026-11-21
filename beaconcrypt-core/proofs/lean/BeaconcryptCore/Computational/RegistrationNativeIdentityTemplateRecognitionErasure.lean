-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure
open PqxdhJointIdentity (Primitives PublicIdentity)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate certify)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev New := RegistrationNativeIdentityTemplateCensorRecognition.Spec
open RegistrationNativeIdentityTemplateCensorRecognition (erase recognize)
variable {Value : Type}

def project (joint : Primitives) (identity : PublicIdentity) : Candidate joint identity ⊕ Value → Ed25519Signature ⊕ Value
  | .inl chosen => .inl chosen.2.val
  | .inr value => .inr value

/-- Public candidate certification returns exactly the same ordinary valid signature bytes as the fixed-message source recognizer. -/
theorem known_recognize (joint : Primitives) (identity : PublicIdentity) (target input : Pqxdh.Bytes) :
    (recognize joint identity (.inr ⟨some target, .inl input⟩)).map (fun chosen => chosen.2.val) =
      RegistrationNativeIdentityRecognition.recognize joint.verify identity.ed25519 target input := by
  change ((certify joint identity target input).map (fun signature => (⟨target, signature⟩ : Candidate joint identity))).map
    (fun chosen => chosen.2.val) = _
  rw [Option.map_map]
  unfold certify
  split <;> simp_all only [Option.map_none, Option.map_some, Function.comp_apply]

/-- Every actual known-input candidate concerns that literal public target. -/
theorem known_message (joint : Primitives) (identity : PublicIdentity) (target input : Pqxdh.Bytes)
    (candidate : Candidate joint identity) (returned : recognize joint identity (.inr ⟨some target, .inl input⟩) = some candidate) :
    candidate.1 = target := by
  cases found : certify joint identity target input with
  | none => simp only [recognize, found, Option.map_none, reduceCtorEq] at returned
  | some signature =>
      simp only [recognize, found, Option.map_some, Option.some.injEq] at returned
      cases returned
      rfl

def ErasedAllowed (target : Pqxdh.Bytes) : New.Domain → Prop
  | .inl (.inr _) => False
  | .inr described => described.message = some target
  | _ => True

private theorem erased_query (selected : Nat) (target : Pqxdh.Bytes) (placeholder : Ed25519Signature) (query : Old.Domain)
    (annotated : RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected target query) :
    (erase placeholder query).AllQueriesSatisfy (ErasedAllowed target) := by
  rcases query with (((protocol | selection) | scanned) | described) | marker
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · exact False.elim annotated
  · exact (allQueriesSatisfy_query_iff _ _).mpr annotated
  · cases marker with
    | omitted handle message => exact allQueriesSatisfy_pure _ _
    | template handle message leading trailing => exact (allQueriesSatisfy_query_iff _ _).mpr annotated

/-- The explicit erased client has no prefix scan and keeps each literal hash target; this follows from the original source annotations. -/
theorem erased_scope (selected : Nat) (target : Pqxdh.Bytes) (placeholder : Ed25519Signature) (work : OracleComp Old Value)
    (annotated : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected target)) :
    (simulateQ (erase placeholder) work).AllQueriesSatisfy (ErasedAllowed target) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp annotated
      rw [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (erased_query selected target placeholder query first) (fun reply => ih reply (later reply))

private theorem query_capture {I Witness Result : Type} {queries : OracleSpec I}
    (recognizer : queries.Domain → Option Witness) (query : queries.Domain)
    (next : queries.Range query → OracleComp queries Result) :
    RegistrationNativeIdentityRecognitionCapture.capture recognizer (queries.query query >>= next) =
      (match recognizer query with
      | some witness => pure (.inl witness)
      | none => do let reply ← queries.query query; RegistrationNativeIdentityRecognitionCapture.capture recognizer (next reply)) := rfl

private theorem pure_capture {I Witness Result : Type} {queries : OracleSpec I}
    (recognizer : queries.Domain → Option Witness) (value : Result) :
    RegistrationNativeIdentityRecognitionCapture.capture recognizer (pure value) = pure (.inr value) := rfl

private theorem query_message (joint : Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes)
    (query : New.Domain) (allowed : ErasedAllowed target query) (candidate : Candidate joint identity)
    (returned : recognize joint identity query = some candidate) : candidate.1 = target := by
  rcases query with ((protocol | selection) | scanned) | described
  · simp only [recognize, reduceCtorEq] at returned
  · simp only [recognize, reduceCtorEq] at returned
  · exact False.elim allowed
  · rcases described with ⟨message, input⟩
    change message = some target at allowed
    subst message
    cases input with
    | inl input => exact known_message joint identity target input candidate returned
    | inr frame => simp only [recognize, reduceCtorEq] at returned

/-- Every captured candidate from the actual annotated erased tree has its same selected message, under arbitrary private interpretation. -/
theorem captured_message {State : Type} (joint : Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes)
    (handler : QueryImpl New (StateT State ProbComp)) (work : OracleComp New Value)
    (allowed : work.AllQueriesSatisfy (ErasedAllowed target)) (before : State)
    (result : (Candidate joint identity ⊕ Value) × State)
    (supported : result ∈ support ((simulateQ handler (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity) work)).run before)) :
    ∀ candidate, result.1 = .inl candidate → candidate.1 = target := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [pure_capture, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      intro candidate returned
      cases returned
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      rw [query_capture] at supported
      cases found : recognize joint identity query with
      | some witness =>
          simp only [found, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          intro candidate returned
          cases returned
          exact query_message joint identity target query first witness found
      | none =>
          simp only [found, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨middle, _called, continued⟩ := supported
          exact ih middle.1 (later middle.1) middle.2 result continued

/-- Capturing the first fixed-target source witness commutes with explicit marker erasure and executable public candidate capture, preserving all adaptive replies and values. -/
theorem capture_erase (joint : Primitives) (identity : PublicIdentity) (selected : Nat) (target : Pqxdh.Bytes)
    (placeholder : Ed25519Signature) (work : OracleComp Old Value)
    (annotated : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected target))
    (sourceScope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed) :
    simulateQ (erase placeholder) (RegistrationNativeIdentityRecognitionCapture.capture
      (RegistrationNativeIdentityTemplateSource.recognize joint.verify identity.ed25519 target) work) =
      project joint identity <$> RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity)
        (simulateQ (erase placeholder) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [pure_capture, simulateQ_pure, map_pure, project]
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp annotated
      obtain ⟨admitted, remaining⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp sourceScope
      rw [query_capture]
      rcases query with (((protocol | selection) | scanned) | described) | marker
      · simp only [RegistrationNativeIdentityTemplateSource.recognize, erase, simulateQ_bind, simulateQ_spec_query,
          query_capture, recognize, map_bind]
        apply bind_congr
        intro reply
        exact ih reply (later reply) (remaining reply)
      · simp only [RegistrationNativeIdentityTemplateSource.recognize, erase, simulateQ_bind, simulateQ_spec_query,
          query_capture, recognize, map_bind]
        apply bind_congr
        intro reply
        exact ih reply (later reply) (remaining reply)
      · exact False.elim first
      · rcases described with ⟨message, supplied⟩
        change message = some target at first
        subst message
        cases supplied with
        | none => simp only [RegistrationNativeIdentityCensorTemplateScope.Allowed, Option.isSome_none, Bool.false_eq_true] at admitted
        | some input =>
            cases found : recognize joint identity (.inr ⟨some target, .inl input⟩) with
            | none =>
                have oldFound : RegistrationNativeIdentityRecognition.recognize joint.verify identity.ed25519 target input = none := by
                  simpa only [found, Option.map_none] using (known_recognize joint identity target input).symm
                simp only [RegistrationNativeIdentityTemplateSource.recognize, erase, simulateQ_bind, simulateQ_spec_query,
                  Option.getD_some, Option.bind_some, oldFound, query_capture, found, map_bind]
                apply bind_congr
                intro reply
                exact ih reply (later reply) (remaining reply)
            | some candidate =>
                have oldFound : RegistrationNativeIdentityRecognition.recognize joint.verify identity.ed25519 target input = some candidate.2.val := by
                  simpa only [found, Option.map_some] using (known_recognize joint identity target input).symm
                simp only [RegistrationNativeIdentityTemplateSource.recognize, erase, simulateQ_bind, simulateQ_spec_query,
                  Option.getD_some, Option.bind_some, oldFound, query_capture, found, simulateQ_pure, map_pure, project]
      · cases marker with
        | omitted handle message =>
            simp only [RegistrationNativeIdentityTemplateSource.recognize, erase, simulateQ_bind, simulateQ_spec_query,
              pure_bind]
            exact ih (some placeholder) (later (some placeholder)) (remaining (some placeholder))
        | template handle message leading trailing =>
            change message = some target at first
            subst message
            simp only [RegistrationNativeIdentityTemplateSource.recognize, erase, simulateQ_bind, simulateQ_spec_query,
              query_capture, recognize, map_bind]
            apply bind_congr
            intro reply
            exact ih reply (later reply) (remaining reply)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.known_recognize' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.known_recognize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.known_message' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.known_message

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.erased_scope' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.erased_scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.captured_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.captured_message

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.capture_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure.capture_erase
