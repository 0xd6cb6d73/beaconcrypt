-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture
import BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor

/-! The ordinary joint-Ed reduction executes its own symbolic lazy table and returns actual recognized signature bytes. Every hash draw is an ordinary public uniform query, and none aliases one private address token. The executable client contains only public messages, symbolic cache keys and returned digests. A candidate is charged only when its message is the actual adaptively selected censor target. Native public-position coverage and private source realization remain separate obligations. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture
open PqxdhJointIdentity (IdentitySeed PublicIdentity History)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveCensor (Policy)
variable {Value Reply : Type}

abbrev HashSpec (Reply : Type) := Option Pqxdh.Bytes →ₒ (Reply × Nat)
abbrev Spec (Reply : Type) := RegistrationNativeIdentityAdaptiveCensor.Spec + HashSpec Reply
abbrev Cache (Reply : Type) := (Option Pqxdh.Bytes →ₒ Reply).QueryCache

def uniform : QueryImpl unifSpec (OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec) :=
  fun query => RegistrationNativeIdentityAdaptiveCensor.Spec.query (.inl (.inl query))

noncomputable def handler (sampler : ProbComp Reply) : QueryImpl (Spec Reply)
    (StateT (Cache Reply) (OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec))
  | .inl query => StateT.lift (RegistrationNativeIdentityAdaptiveCensor.Spec.query query : OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec _)
  | .inr input => fun before => simulateQ uniform
      ((RegistrationNativeIdentitySymbolicRom.counted sampler input).run before)

noncomputable def close (sampler : ProbComp Reply) (work : OracleComp (Spec Reply) Value) (before : Cache Reply) :
    OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec Value :=
  Prod.fst <$> (simulateQ (handler sampler) work).run before

/-- Signature validity is certified by the public scanner, never by a desired security conclusion. -/
abbrev Candidate (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) :=
  (message : Pqxdh.Bytes) × {signature : Ed25519Signature // primitives.verify identity.ed25519 message signature = true}

def certify (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (message input : Pqxdh.Bytes) :
    Option {signature : Ed25519Signature // primitives.verify identity.ed25519 message signature = true} :=
  match found : RegistrationNativeIdentityRecognition.recognize primitives.verify identity.ed25519 message input with
  | none => none
  | some signature => some ⟨signature, RegistrationNativeIdentityRecognition.valid _ _ _ _ _ found⟩

def recognizer (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (message : Pqxdh.Bytes) :
    (Spec Reply).Domain → Option {signature : Ed25519Signature // primitives.verify identity.ed25519 message signature = true}
  | .inr (some input) => certify primitives identity message input
  | _ => none

/-- Stop before the first recognized public hash input; symbolic none queries are internal aliases and remain permitted. -/
def capture (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (message : Pqxdh.Bytes)
    (work : OracleComp (Spec Reply) Value) : OracleComp (Spec Reply) (Option (Candidate primitives identity)) :=
  (fun result => match result with | .inl signature => some ⟨message, signature⟩ | .inr _ => none) <$>
    RegistrationNativeIdentityRecognitionCapture.capture (recognizer primitives identity message) work

/-- A returned witness always concerns this very selected message; no canonical-signature uniqueness is used. -/
theorem captured (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity) (message : Pqxdh.Bytes)
    (work : OracleComp (Spec Reply) Value) (sampler : ProbComp Reply) (before : Cache Reply)
    (result : Option (Candidate primitives identity))
    (possible : result ∈ support (close sampler (capture primitives identity message work) before)) :
    ∀ candidate, result = some candidate → candidate.1 = message := by
  simp only [close, capture, simulateQ_map, StateT.run_map, Functor.map_map, support_map] at possible
  obtain ⟨middle, _reached, same⟩ := possible
  cases same
  intro candidate returned
  cases value : middle.1 with
  | inl signature => simp only [value] at returned; cases returned; rfl
  | inr value => simp only [value] at returned; cases returned

attribute [local irreducible] close handler

noncomputable def work (primitives : PqxdhJointIdentity.Primitives) (sampler : ProbComp Reply)
    (client : (identity : PublicIdentity) → OracleComp (Spec Reply) (Option (Candidate primitives identity)))
    (before : Cache Reply) (identity : PublicIdentity) :
    OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec (Option Ed25519Signature) :=
  (fun candidate => candidate.map (fun selected => selected.2.val)) <$> close sampler (client identity) before

def selected (policy : Policy) {primitives : PqxdhJointIdentity.Primitives} {identity : PublicIdentity}
    (candidate : Option (Candidate primitives identity)) : Bool :=
  candidate.any (fun chosen => policy.target == some chosen.1)

private theorem selected_valid (primitives : PqxdhJointIdentity.Primitives) (identity : PublicIdentity)
    (policy : Policy) (candidate : Option (Candidate primitives identity)) (held : selected policy candidate = true) :
    RegistrationNativeIdentityAdaptiveCensor.recognized primitives identity
      (candidate.map (fun chosen => chosen.2.val)) policy = true := by
  cases returned : candidate with
  | none => simp only [selected, returned, Option.any_none, Bool.false_eq_true] at held
  | some chosen =>
    have target : policy.target = some chosen.1 := by
      simpa only [selected, returned, Option.any_some, beq_iff_eq] using held
    simp only [RegistrationNativeIdentityAdaptiveCensor.recognized, Option.map_some,
      target, Option.any_some, chosen.2.property]

noncomputable def game (primitives : PqxdhJointIdentity.Primitives) (sampler : ProbComp Reply) (placeholder : Ed25519Signature)
    (client : (identity : PublicIdentity) → OracleComp (Spec Reply) (Option (Candidate primitives identity)))
    (before : Cache Reply) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let result ← RegistrationNativeIdentityAdaptiveCensor.execute primitives seed placeholder
    (close sampler (client (primitives.publicKeys seed)) before) {} []
  pure (selected result.1.2 result.1.1)

/-- Actual first-witness capture has one ordinary joint weak-EUF bill. Its symbolic table is executed inside that adversary and target freshness comes from the actual adaptive censor history. -/
theorem bound (primitives : PqxdhJointIdentity.Primitives) (sampler : ProbComp Reply) (placeholder : Ed25519Signature)
    (fallback : PqxdhJointIdentity.Forgery)
    (client : (identity : PublicIdentity) → OracleComp (Spec Reply) (Option (Candidate primitives identity)))
    (before : Cache Reply) :
    Pr{let accepted ← game primitives sampler placeholder client before}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives
        (RegistrationNativeIdentityAdaptiveCensor.reduction placeholder fallback (work primitives sampler client before)) := by
  apply le_trans (b := Pr{let accepted ← (RegistrationNativeIdentityAdaptiveCensor.observed primitives placeholder (work primitives sampler client before))}[accepted = true])
  · unfold game RegistrationNativeIdentityAdaptiveCensor.observed work
    simp only [RegistrationNativeIdentityAdaptiveCensor.execute, simulateQ_map, StateT.run_map,
      bind_map_left]
    apply prEvent_bind_mono_of_forall_le_of_support
    intro seed _
    apply prEvent_bind_mono_of_forall_le_of_support
    intro result _
    by_cases held : selected result.1.2 result.1.1 = true
    · have verified := selected_valid primitives (primitives.publicKeys seed) result.1.2 result.1.1 held
      simp only [prEvent_pure, held, verified, ite_true]
      exact le_rfl
    · simp only [prEvent_pure, held, Bool.false_eq_true, ite_false]
      exact zero_le

  · exact RegistrationNativeIdentityAdaptiveCensor.recognition_bound primitives placeholder fallback _

end BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture.captured' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture.captured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture.bound
