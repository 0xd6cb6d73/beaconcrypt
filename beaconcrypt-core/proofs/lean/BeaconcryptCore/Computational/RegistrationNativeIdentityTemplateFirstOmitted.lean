-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource

/-! The first actual omitted attempt establishes the private canonical realization. Installation itself copies only the reached public-input cache and journal; source cache provenance and the actual prefix recognition check discharge the hidden misses. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityTemplateSource (Private State Spec Held realize)
variable {Value I KemSK : Type} {base : OracleSpec I}

/-- The sole CTX domain tag contains no additional private input. -/
def byteCache (cache : RegistrationNativePlatformCtxBackend.Cache) : RegistrationNativeIdentityReindexedCtx.ByteCache :=
  ⟨fun input => cache ((), input)⟩

def install (before : Private) : RegistrationNativeIdentityReindexedCtx.State RegistrationNativeIdentityTemplateAddress.Key :=
  RegistrationNativeIdentityTemplateCtx.install (byteCache before.hash.1) before.hash.2

private theorem unit_byteCache (cache : RegistrationNativePlatformCtxBackend.Cache) :
    RegistrationNativeIdentityReindexedCtx.unitCache (byteCache cache) = cache := by
  apply QueryCache.ext
  rintro ⟨tag, input⟩
  cases tag
  rfl

def after (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed) (before : Private) : Private :=
  {before with pool := (PqxdhDynamicIdentityPool.record (.inr (.service selected (.sign message)))
    (some (joint.sign seed message)) before.pool), canonical := some (joint.sign seed message)}

/-- The original first suppressed attempt keeps its canonical source receipt privately and returns exactly the known client placeholder. -/
theorem marker (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (before : Private)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message) :
    (RegistrationNativeIdentityCensorSource.censored joint selected placeholder (.inr (.omitted selected message))).run before =
      pure (some placeholder, after joint selected message seed before) :=
  RegistrationNativeIdentityCensorSource.censored_omitted joint selected placeholder message before seed found target

/-- This actual receipt supplies the complete continued-source realization invariant, without a successful writer or publication premise. -/
theorem held (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed) (before : Private)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message) :
    Held joint selected message seed (after joint selected message seed before) := by
  exact ⟨⟨target, found⟩, rfl⟩

/-- The warm cache and chronological prefix are restored literally. The input journal is not reset, and all public template aliases start empty. -/
theorem initial (setup : PqxdhServerAuthExperiment.Setup base KemSK) (selected : Nat)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (before : Private)
    (known : ∀ input digest, before.hash.1 ((), input) = some digest → input ∈ before.hash.2)
    (unrecognized : ∀ input ∈ before.hash.2, RegistrationNativeIdentityRecognition.recognize
      setup.joint.verify (setup.joint.publicKeys seed).ed25519 message input = none) :
    realize (setup.joint.sign seed message) (after setup.joint selected message seed before, install before) =
      after setup.joint selected message seed before := by
  have fresh := RegistrationNativeIdentityTemplateCtx.cache_miss setup.joint.verify (setup.joint.publicKeys seed).ed25519
    message (setup.joint.sign seed message) (RegistrationNativeIdentityRecognitionSource.sign_correct setup seed message)
    (byteCache before.hash.1) before.hash.2 known unrecognized
  have table := RegistrationNativeIdentityTemplateCtx.initial (setup.joint.sign seed message)
    (byteCache before.hash.1) before.hash.2 fresh
  rw [unit_byteCache] at table
  change {after setup.joint selected message seed before with hash :=
    (RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize (setup.joint.sign seed message))
      (RegistrationNativeIdentityTemplateAddress.abstract (setup.joint.sign seed message)) (install before))} = _
  rw [show install before = RegistrationNativeIdentityTemplateCtx.install (byteCache before.hash.1) before.hash.2 from rfl, table]
  rfl

/-- Erasing the new canonical source audit makes the installed continuation independent of the hidden signature, while retaining the actual source-oracle rows and the full symbolic cache/journal. -/
theorem ghost (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed) (before : Private) :
    RegistrationNativeIdentityTemplateGhostView.view (after joint selected message seed before, install before) =
      RegistrationNativeIdentityTemplateGhostView.view (before, install before) := rfl

private theorem capture_query {Index Witness A : Type} {queries : OracleSpec Index}
    (recognizer : queries.Domain → Option Witness) (request : queries.Domain)
    (next : queries.Range request → OracleComp queries A) :
    RegistrationNativeIdentityRecognitionCapture.capture recognizer (queries.query request >>= next) =
      (match recognizer request with
      | some witness => pure (.inl witness)
      | none => do let answer ← queries.query request
                   RegistrationNativeIdentityRecognitionCapture.capture recognizer (next answer)) := rfl

private theorem capture_scope (recognizer : Spec.Domain → Option Ed25519Signature) (work : OracleComp Spec Value)
    (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed) :
    (RegistrationNativeIdentityRecognitionCapture.capture recognizer work).AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp scope
    rw [capture_query]
    cases recognizer request with
    | some witness => trivial
    | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first, fun answer => ih answer (later answer)⟩

/-- The continued guarded observation after the actual omitted call has exactly its explicit erased-client/private-oracle interpretation. Neither the initial symbolic table nor the erased syntax captures the canonical signature. -/
theorem continuation (setup : PqxdhServerAuthExperiment.Setup base KemSK) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (before : Private)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message)
    (known : ∀ input digest, before.hash.1 ((), input) = some digest → input ∈ before.hash.2)
    (unrecognized : ∀ input ∈ before.hash.2, RegistrationNativeIdentityRecognition.recognize
      setup.joint.verify (setup.joint.publicKeys seed).ed25519 message input = none)
    (work : OracleComp Spec Value) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed) :
    Prod.fst <$> (simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateSource.recognize
        setup.joint.verify (setup.joint.publicKeys seed).ed25519 message) work)).run
      (after setup.joint selected message seed before) =
    Prod.fst <$> (simulateQ (RegistrationNativeIdentityTemplateErasure.sourceHandler setup.joint selected placeholder)
      (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
        (RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateSource.recognize
          setup.joint.verify (setup.joint.publicKeys seed).ed25519 message) work))).run
      (RegistrationNativeIdentityTemplateGhostView.view (before, install before)) := by
  have physical := congrArg (fun distribution => Prod.fst <$> distribution)
    (RegistrationNativeIdentityTemplateSource.capture_source setup.joint selected placeholder message seed
      (RegistrationNativeIdentityRecognitionSource.sign_correct setup seed message) work scope
      (after setup.joint selected message seed before, install before) (held setup.joint selected message seed before found target))
  have executable := congrArg (fun distribution => Prod.fst <$> distribution)
    (RegistrationNativeIdentityTemplateErasure.program setup.joint selected placeholder message
      (RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateSource.recognize
        setup.joint.verify (setup.joint.publicKeys seed).ed25519 message) work)
      (capture_scope _ work scope) (after setup.joint selected message seed before, install before) target)
  rw [initial setup selected message seed before known unrecognized] at physical
  rw [ghost] at executable
  simp only [Functor.map_map] at physical executable
  exact physical.symm.trans executable

/-- The actual post-omission source probability is bounded by the explicit erased continuation plus its extracted public-recognition event, with the warm cache and all source failures retained. This is a conditional prefix cut, not an initialized causal-event bound. -/
theorem loss (setup : PqxdhServerAuthExperiment.Setup base KemSK) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (before : Private)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message)
    (known : ∀ input digest, before.hash.1 ((), input) = some digest → input ∈ before.hash.2)
    (unrecognized : ∀ input ∈ before.hash.2, RegistrationNativeIdentityRecognition.recognize
      setup.joint.verify (setup.joint.publicKeys seed).ed25519 message input = none)
    (work : OracleComp Spec Value) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (event : Value → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder) work).run
      (after setup.joint selected message seed before))}[event result.1] ≤
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityTemplateErasure.sourceHandler setup.joint selected placeholder)
      (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
        (RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateSource.recognize
          setup.joint.verify (setup.joint.publicKeys seed).ed25519 message) work))).run
      (RegistrationNativeIdentityTemplateGhostView.view (before, install before)))}[∃ witness, result.1 = .inl witness] +
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityTemplateErasure.sourceHandler setup.joint selected placeholder)
      (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
        (RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateSource.recognize
          setup.joint.verify (setup.joint.publicKeys seed).ed25519 message) work))).run
      (RegistrationNativeIdentityTemplateGhostView.view (before, install before)))}[
        ∃ value, result.1 = .inr value ∧ event value] := by
  have upper := RegistrationNativeIdentityRecognitionCapture.cover
    (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
    (RegistrationNativeIdentityTemplateSource.recognize setup.joint.verify (setup.joint.publicKeys seed).ed25519 message)
    work (fun result => event result.1) (after setup.joint selected message seed before)
  have same (observed : Ed25519Signature ⊕ Value → Prop) := congrArg
    (fun distribution => Pr{let result ← distribution}[observed result])
    (continuation setup selected placeholder message seed before found target known unrecognized work scope)
  simp only [prEvent_map] at same
  dsimp only at upper
  rw [same (fun result => ∃ witness, result = .inl witness),
    same (fun result => ∃ value, result = .inr value ∧ event value)] at upper
  exact upper

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.marker
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.held' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.held
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.initial' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.initial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.ghost' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.ghost

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.continuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted.loss
