-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCtx
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope

/-! A proof-private template-table interpretation retains the actual canonical omitted-signing audit and source key rows. Reindexing changes only the physical hash representation. This intermediate state is not executable E state; erasing its canonical audit against the primitive router remains a separate obligation. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource
open RegistrationNativeIdentityTemplateAddress (Key Frame)
open PqxdhEd25519EufCma (Ed25519Signature Ed25519PublicKey)
abbrev Private := RegistrationNativeIdentityCensorSource.State
abbrev State := Private × RegistrationNativeIdentityReindexedCtx.State Key
abbrev Spec := RegistrationNativeIdentityCensorOperational.Spec
variable {Value : Type}

/-- The selected canonical signature is passed only to this private realization. -/
noncomputable def realize (signature : Ed25519Signature) (before : State) : Private :=
  {before.1 with hash := (RegistrationNativeIdentityReindexedCtx.realize (RegistrationNativeIdentityTemplateAddress.realize signature)
    (RegistrationNativeIdentityTemplateAddress.abstract signature) before.2)}

noncomputable def hash (key : Key) : StateT State ProbComp (CtxRomAuth.CtxDigest × Nat) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationNativeIdentityReindexedCtx.implementation key).run before.2

noncomputable def unchanged (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (query : Spec.Domain) : StateT State ProbComp (Spec.Range query) := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$>
    (RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run before.1

noncomputable def template (frame : Frame) : StateT State ProbComp (CtxRomAuth.CtxDigest × Nat) := fun before =>
  (fun result => (result.1, ({result.2.1 with framing := some frame}, result.2.2))) <$> (hash (.inr frame)).run before

noncomputable def implementation (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) :
    QueryImpl Spec (StateT State ProbComp)
  | .inl (.inr described) => hash (match described.input with | some bytes => .inl bytes | none => .inl [])
  | .inr (.template _ _ leading trailing) => template (leading, trailing)
  | query => unchanged joint selected placeholder query

/-- Source syntax supplies template width; the actual recognition stop supplies the public-input condition. -/
def Allowed (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) : Spec.Domain → Prop
  | .inl (.inr described) => match described.input with
      | some bytes => RegistrationNativeIdentityRecognition.recognize verify publicKey message bytes = none
      | none => False
  | .inr (.template _ _ leading _) => leading.length = 2188
  | _ => True

private theorem hash_source (signature : Ed25519Signature) (key : Key) (before : State)
    (admitted : RegistrationNativeIdentityTemplateAddress.abstract signature (RegistrationNativeIdentityTemplateAddress.realize signature key) = key) :
    Prod.map id (realize signature) <$> (hash key).run before =
      (RegistrationNativeIdentityCensorSource.physical (RegistrationNativeIdentityTemplateAddress.realize signature key)).run (realize signature before) := by
  have law := RegistrationNativeIdentityReindexedCtx.query (RegistrationNativeIdentityTemplateAddress.realize signature)
    (RegistrationNativeIdentityTemplateAddress.abstract signature) (RegistrationNativeIdentityTemplateAddress.realize_abstract signature)
    key before.2 admitted
  have mapped := congrArg (fun distribution => (fun result => (result.1, {before.1 with hash := result.2})) <$> distribution) law
  simpa only [hash, realize, RegistrationNativeIdentityCensorSource.physical, StateT.run, Functor.map_map, Prod.map_def, id_eq] using mapped

private def NoHash : Spec.Domain → Prop
  | .inl (.inr _) | .inr (.template _ _ _ _) => False
  | _ => True

private theorem bind_apply {State A B : Type} {m : Type → Type} [Monad m]
    (work : StateT State m A) (next : A → StateT State m B) (before : State) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {State A : Type} {m : Type → Type} [Monad m] (value : A) (before : State) :
    (pure value : StateT State m A) before = pure (value, before) := rfl

private theorem unchanged_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder signature : Ed25519Signature)
    (query : Spec.Domain) (ordinary : NoHash query) (before : State) :
    Prod.map id (realize signature) <$> (unchanged joint selected placeholder query).run before =
      (RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run (realize signature before) := by
  rcases query with (((protocol | message) | scanned) | described) | marker
  · simp only [unchanged, RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, StateT.run, Functor.map_map, Prod.map_def, id_eq, realize]
  · simp only [unchanged, RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.select, StateT.run, realize]
    split <;> simp only [map_pure, Prod.map_def, id_eq] <;> rfl
  · simp only [unchanged, RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      StateT.run, pure_apply, map_pure, Prod.map_def, id_eq, realize]
  · exact False.elim ordinary
  · cases marker with
    | template handle message leading trailing => exact False.elim ordinary
    | omitted handle message =>
      simp only [unchanged, RegistrationNativeIdentityCensorSource.censored, bind_apply,
        RegistrationNativeIdentityCensorSource.omitted, StateT.run, map_bind, bind_map_left,
        pure_apply, map_pure, Prod.map_def, id_eq, realize]

private theorem template_source (signature : Ed25519Signature) (frame : Frame) (before : State)
    (canonical : before.1.canonical = some signature) (width : frame.1.length = 2188) :
    Prod.map id (realize signature) <$> (template frame).run before =
      (RegistrationNativeIdentityCensorSource.template frame.1 frame.2).run (realize signature before) := by
  have law := hash_source signature (.inr frame) before (RegistrationNativeIdentityTemplateAddress.abstract_hidden signature frame width)
  have mapped := congrArg (fun distribution => (fun result => (result.1, {result.2 with framing := some frame})) <$> distribution) law
  simpa only [template, RegistrationNativeIdentityCensorSource.template, RegistrationNativeIdentityCensorSource.address,
    StateT.run, Functor.map_map, Prod.map_def, id_eq, realize, canonical, Option.getD_some,
    RegistrationNativeIdentityTemplateAddress.realize] using mapped

/-- Each admitted actual private-censored marker call has the literal source reply and full source-state realization. Canonical audit/key rows are retained only in this proof-private intermediate table. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool) (publicKey : Ed25519PublicKey)
    (message : Pqxdh.Bytes) (signature : Ed25519Signature) (valid : verify publicKey message signature = true)
    (request : Spec.Domain) (before : State) (canonical : before.1.canonical = some signature)
    (allowed : Allowed verify publicKey message request) :
    Prod.map id (realize signature) <$> (implementation joint selected placeholder request).run before =
      (RegistrationNativeIdentityCensorSource.censored joint selected placeholder request).run (realize signature before) := by
  rcases request with (((protocol | target) | scanned) | described) | marker
  · exact unchanged_source joint selected placeholder signature (.inl (.inl (.inl (.inl protocol)))) trivial before
  · exact unchanged_source joint selected placeholder signature (.inl (.inl (.inl (.inr target)))) trivial before
  · exact unchanged_source joint selected placeholder signature (.inl (.inl (.inr scanned))) trivial before
  · cases indexed : described.input with
    | none =>
      simp only [Allowed, indexed] at allowed
    | some input =>
      have publicAllowed : RegistrationNativeIdentityRecognition.recognize verify publicKey message input = none := by
        simpa only [Allowed, indexed] using allowed
      simp only [implementation, RegistrationNativeIdentityCensorSource.censored,
        RegistrationNativeIdentityCensorSource.implementation, indexed]
      exact hash_source signature (.inl input) before
        (RegistrationNativeIdentityTemplateAddress.abstract_public verify publicKey message signature valid input publicAllowed)
  · cases marker with
    | omitted handle message => exact unchanged_source joint selected placeholder signature (.inr (.omitted handle message)) trivial before
    | template handle target leading trailing =>
      exact template_source signature (leading, trailing) before canonical allowed

def Held (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed) (before : Private) : Prop :=
  RegistrationNativeIdentityCensorSelectedInvariant.PrivateHeld selected message seed before ∧
    before.canonical = some (joint.sign seed message)

private theorem canonical_held (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (request : Spec.Domain) (before : Private)
    (prior : Held joint selected message seed before) (result : Spec.Range request × Private)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.censored joint selected placeholder request).run before)) :
    result.2.canonical = some (joint.sign seed message) := by
  rcases request with (((protocol | target) | scanned) | described) | marker
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, StateT.run, support_map] at supported
    obtain ⟨actual, _called, rfl⟩ := supported
    exact prior.2
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.select, StateT.run, prior.1.1, reduceCtorEq, false_and, ite_false,
      mem_support_pure_iff] at supported
    cases supported
    exact prior.2
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior.2
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
    obtain ⟨actual, _called, rfl⟩ := supported
    exact prior.2
  · cases marker with
    | template handle target leading trailing =>
      simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.template, RegistrationNativeIdentityCensorSource.physical,
        StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨actual, _called, rfl⟩ := supported
      exact prior.2
    | omitted handle target =>
      by_cases matching : handle = selected ∧ before.target = some target
      · have chosen := matching.2
        have handleEq := matching.1
        subst handle
        have same : target = message := Option.some.inj (chosen.symm.trans prior.1.1)
        subst target
        rw [RegistrationNativeIdentityCensorSource.censored_omitted joint selected placeholder message before seed prior.1.2 prior.1.1,
          mem_support_pure_iff] at supported
        cases supported
        rfl
      · simp only [RegistrationNativeIdentityCensorSource.censored, bind_apply, RegistrationNativeIdentityCensorSource.omitted,
          StateT.run, pure_apply, bind_pure_comp, matching, ite_false, support_map] at supported
        obtain ⟨actual, called, rfl⟩ := supported
        obtain ⟨reply, _queried, rfl⟩ := called
        exact prior.2

/-- Every actual continued private-censored call retains its selected row, message and deterministic canonical reply, including future creations and all failed observations. -/
theorem source_held (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (request : Spec.Domain) (before : Private)
    (prior : Held joint selected message seed before) (result : Spec.Range request × Private)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.censored joint selected placeholder request).run before)) :
    Held joint selected message seed result.2 :=
  ⟨RegistrationNativeIdentityCensorSelectedInvariant.censored_query joint selected placeholder message seed request before prior.1 result supported,
    canonical_held joint selected placeholder message seed request before prior result supported⟩

private theorem implementation_held (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (valid : joint.verify (joint.publicKeys seed).ed25519 message (joint.sign seed message) = true)
    (request : Spec.Domain) (before : State) (prior : Held joint selected message seed before.1)
    (allowed : Allowed joint.verify (joint.publicKeys seed).ed25519 message request)
    (result : Spec.Range request × State)
    (supported : result ∈ support ((implementation joint selected placeholder request).run before)) :
    Held joint selected message seed result.2.1 := by
  have actual : (result.1, realize (joint.sign seed message) result.2) ∈ support
      ((RegistrationNativeIdentityCensorSource.censored joint selected placeholder request).run (realize (joint.sign seed message) before)) := by
    rw [← query joint selected placeholder joint.verify (joint.publicKeys seed).ed25519 message (joint.sign seed message)
      valid request before prior.2 allowed, support_map]
    exact ⟨result, supported, rfl⟩
  exact source_held joint selected placeholder message seed request (realize (joint.sign seed message) before)
    prior (result.1, realize (joint.sign seed message) result.2) actual

/-- Every admitted adaptive marker continuation has the exact actual private-censored source distribution, retaining canonical audit, generated rows, physical cache, chronological inputs and true costs. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (valid : joint.verify (joint.publicKeys seed).ed25519 message (joint.sign seed message) = true)
    (work : OracleComp Spec Value)
    (allowed : work.AllQueriesSatisfy (Allowed joint.verify (joint.publicKeys seed).ed25519 message))
    (before : State) (prior : Held joint selected message seed before.1) :
    Prod.map id (realize (joint.sign seed message)) <$>
      (simulateQ (implementation joint selected placeholder) work).run before =
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run
      (realize (joint.sign seed message) before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query joint selected placeholder joint.verify (joint.publicKeys seed).ed25519 message (joint.sign seed message)
      valid request before prior.2 first]
    rw [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    exact ih middle.1 (later middle.1) middle.2
      (implementation_held joint selected placeholder message seed valid request before prior first middle reached)

def recognize (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) : Spec.Domain → Option Ed25519Signature
  | .inl (.inr described) => described.input.bind (RegistrationNativeIdentityRecognition.recognize verify publicKey message)
  | _ => none

private theorem capture_query {Index Witness A : Type} {queries : OracleSpec Index}
    (recognizer : queries.Domain → Option Witness) (request : queries.Domain)
    (next : queries.Range request → OracleComp queries A) :
    RegistrationNativeIdentityRecognitionCapture.capture recognizer (queries.query request >>= next) =
      (match recognizer request with
      | some witness => pure (.inl witness)
      | none => do let reply ← queries.query request; RegistrationNativeIdentityRecognitionCapture.capture recognizer (next reply)) := rfl

private theorem guarded (verify : Ed25519PublicKey → Pqxdh.Bytes → Ed25519Signature → Bool)
    (publicKey : Ed25519PublicKey) (message : Pqxdh.Bytes) (work : OracleComp Spec Value)
    (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed) :
    (RegistrationNativeIdentityRecognitionCapture.capture (recognize verify publicKey message) work).AllQueriesSatisfy
      (Allowed verify publicKey message) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp scope
    rw [capture_query]
    cases missing : recognize verify publicKey message request with
    | some witness => trivial
    | none =>
      apply (allQueriesSatisfy_query_bind_iff _ _ _).mpr
      refine ⟨?_, fun reply => ih reply (later reply)⟩
      rcases request with (((protocol | target) | scanned) | described) | marker
      · trivial
      · trivial
      · trivial
      · cases indexed : described.input with
        | none => simp only [RegistrationNativeIdentityCensorTemplateScope.Allowed, indexed, Option.isSome_none, Bool.false_eq_true] at first
        | some input => simpa only [Allowed, recognize, indexed, Option.bind_some] using missing
      · cases marker with
        | omitted handle target => trivial
        | template handle target leading trailing => exact first

/-- Capturing public recognition discharges all actual source-hash admission from the generated marker scope, retaining full private signing audit and physical realization. -/
theorem capture_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (valid : joint.verify (joint.publicKeys seed).ed25519 message (joint.sign seed message) = true)
    (work : OracleComp Spec Value) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (before : State) (prior : Held joint selected message seed before.1) :
    Prod.map id (realize (joint.sign seed message)) <$>
      (simulateQ (implementation joint selected placeholder)
        (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint.verify (joint.publicKeys seed).ed25519 message) work)).run before =
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint.verify (joint.publicKeys seed).ed25519 message) work)).run
        (realize (joint.sign seed message) before) :=
  program joint selected placeholder message seed valid _ (guarded joint.verify (joint.publicKeys seed).ed25519 message work scope) before prior

/-- The literal complete private-censored marker execution is bounded by its template-table continuation plus an actual extracted public-recognition witness. This retains canonical source audit privately; it does not erase that audit into executable E. -/
theorem loss (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (valid : joint.verify (joint.publicKeys seed).ed25519 message (joint.sign seed message) = true)
    (work : OracleComp Spec Value) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (before : State) (prior : Held joint selected message seed before.1) (event : Value × Private → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run
      (realize (joint.sign seed message) before))}[event result] ≤
      Pr{let result ← ((simulateQ (implementation joint selected placeholder)
        (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint.verify (joint.publicKeys seed).ed25519 message) work)).run before)}[
          ∃ witness, result.1 = .inl witness] +
      Pr{let result ← ((simulateQ (implementation joint selected placeholder)
        (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint.verify (joint.publicKeys seed).ed25519 message) work)).run before)}[
          ∃ value, result.1 = .inr value ∧ event (value, realize (joint.sign seed message) result.2)] := by
  have upper := RegistrationNativeIdentityRecognitionCapture.cover
    (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
    (recognize joint.verify (joint.publicKeys seed).ed25519 message) work event (realize (joint.sign seed message) before)
  rw [← capture_source joint selected placeholder message seed valid work scope before prior] at upper
  simpa only [prEvent_map, Prod.map_def, id_eq] using upper

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.source_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.source_held

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.capture_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.capture_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource.loss
