-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy

/-! The actual first canonical omission has a public symbolic-table continuation with the genuine signing history outside the compiler. Recognition and the continued output form one event of that same public execution. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityReindexedCtx (State)
open RegistrationNativeIdentityTemplateAddress (Key)
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open PqxdhDynamicIdentityPool (SourceState)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
variable {A I KemSK : Type} {base : OracleSpec I}

def client (joint : Primitives) (identity : PublicIdentity) (placeholder : Ed25519Signature) (work : OracleComp Old A) :
    OracleComp Spec (Candidate joint identity ⊕ A) :=
  RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work)

noncomputable def execute (joint : Primitives) (identity : PublicIdentity) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Old A) (policy : Policy) (hash : State Key) (pool : SourceState) :
    ProbComp (((Candidate joint identity ⊕ A) × Public) × SourceState) :=
  (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
    ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) (client joint identity placeholder work)).run (policy, hash))).run pool

def answer (joint : Primitives) (identity : PublicIdentity) (result : ((Candidate joint identity ⊕ A) × Public) × SourceState) :
    Ed25519Signature ⊕ A := RegistrationNativeIdentityTemplateRecognitionErasure.project joint identity result.1.1

private theorem private_view (message : Pqxdh.Bytes) (before : RegistrationNativeIdentityCensorSource.State)
    (held : before.target = some message) :
    RegistrationNativeIdentityTemplateGhostView.view (before, RegistrationNativeIdentityTemplateFirstOmitted.install before) =
      RegistrationNativeIdentityTemplateProtocol.realize message (RegistrationNativeIdentityTemplateFirstOmitted.install before, before.pool) := by
  rcases before with ⟨pool, hash, target, canonical, framing⟩
  change target = some message at held
  subst target
  rfl

private theorem protocol_output (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes)
    (work : OracleComp Spec A) (hash : State Key) (pool : SourceState) :
    Prod.fst <$> (simulateQ (RegistrationNativeIdentityTemplateErasure.sourceHandler joint selected placeholder) work).run
      (RegistrationNativeIdentityTemplateProtocol.realize message (hash, pool)) =
      (fun result => result.1.1) <$>
        (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
          ((simulateQ RegistrationNativeIdentityTemplateProtocol.handler work).run hash)).run pool := by
  have law := congrArg (Functor.map Prod.fst)
    (RegistrationNativeIdentityTemplateProtocol.program joint selected placeholder message work (hash, pool))
  simpa only [Functor.map_map] using law.symm

private theorem policy_output (joint : Primitives) (selected : Nat) (message : Pqxdh.Bytes)
    (work : OracleComp Spec A) (policy : Policy) (held : policy.target = some message) (hash : State Key) (pool : SourceState) :
    (fun result => result.1.1) <$>
      (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run (policy, hash))).run pool =
    (fun result => result.1.1) <$>
      (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
        ((simulateQ RegistrationNativeIdentityTemplateProtocol.handler work).run hash)).run pool := by
  have compiled := RegistrationNativeIdentityTemplatePolicy.program_after_some selected message work (policy, hash) held
  have interpreted := congrArg (fun code => (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint) code).run pool) compiled
  simp only [simulateQ_map, StateT.run_map] at interpreted
  have observed := congrArg (Functor.map (fun result : (A × State Key) × SourceState => result.1.1)) interpreted
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed

/-- The actual physical continuation after its first omitted signature has precisely the public policy/table execution, with the original genuine source pool and complete audit outside the compiler. -/
theorem continuation (setup : PqxdhServerAuthExperiment.Setup base KemSK) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : IdentitySeed) (before : RegistrationNativeIdentityCensorSource.State)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message)
    (known : ∀ input digest, before.hash.1 ((), input) = some digest → input ∈ before.hash.2)
    (unrecognized : ∀ input ∈ before.hash.2, RegistrationNativeIdentityRecognition.recognize
      setup.joint.verify (setup.joint.publicKeys seed).ed25519 message input = none)
    (work : OracleComp Old A) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (annotated : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected message))
    (policy : Policy) (held : policy.target = some message) :
    Prod.fst <$> (simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateSource.recognize
        setup.joint.verify (setup.joint.publicKeys seed).ed25519 message) work)).run
      (RegistrationNativeIdentityTemplateFirstOmitted.after setup.joint selected message seed before) =
      answer setup.joint (setup.joint.publicKeys seed) <$>
        execute setup.joint (setup.joint.publicKeys seed) selected placeholder work policy
          (RegistrationNativeIdentityTemplateFirstOmitted.install before) before.pool := by
  have physical := RegistrationNativeIdentityTemplateFirstOmitted.continuation setup selected placeholder message seed before
    found target known unrecognized work scope
  rw [RegistrationNativeIdentityTemplateRecognitionErasure.capture_erase setup.joint (setup.joint.publicKeys seed)
    selected message placeholder work annotated scope, private_view message before target] at physical
  simp only [simulateQ_map, StateT.run_map, Functor.map_map] at physical
  have symbolic := protocol_output setup.joint selected placeholder message
    (client setup.joint (setup.joint.publicKeys seed) placeholder work)
    (RegistrationNativeIdentityTemplateFirstOmitted.install before) before.pool
  have policyLaw := policy_output setup.joint selected message
    (client setup.joint (setup.joint.publicKeys seed) placeholder work) policy held
    (RegistrationNativeIdentityTemplateFirstOmitted.install before) before.pool
  have joined := congrArg (Functor.map (RegistrationNativeIdentityTemplateRecognitionErasure.project setup.joint (setup.joint.publicKeys seed)))
    (symbolic.trans policyLaw.symm)
  simp only [Functor.map_map, client] at joined physical
  change _ = (fun result => RegistrationNativeIdentityTemplateRecognitionErasure.project setup.joint (setup.joint.publicKeys seed) result.1.1) <$>
    execute setup.joint (setup.joint.publicKeys seed) selected placeholder work policy
      (RegistrationNativeIdentityTemplateFirstOmitted.install before) before.pool
  simpa only [execute, client, Functor.map_map] using physical.trans joined

def Succeeds {Witness : Type} (event : A → Prop) : Witness ⊕ A → Prop
  | .inl _ => True
  | .inr value => event value

private theorem capture_query {Witness : Type} (recognize : Old.Domain → Option Witness) (request : Old.Domain)
    (next : Old.Range request → OracleComp Old A) :
    RegistrationNativeIdentityRecognitionCapture.capture recognize (Old.query request >>= next) =
      (match recognize request with
      | some witness => pure (.inl witness)
      | none => do let reply ← Old.query request
                   RegistrationNativeIdentityRecognitionCapture.capture recognize (next reply)) := rfl

private theorem capture_cover {Witness S : Type} (handler : QueryImpl Old (StateT S ProbComp))
    (recognize : Old.Domain → Option Witness) (work : OracleComp Old A) (before : S) (event : A → Prop) :
    Pr{let result ← (simulateQ handler work).run before}[event result.1] ≤
      Pr{let result ← (simulateQ handler (RegistrationNativeIdentityRecognitionCapture.capture recognize work)).run before}[
        Succeeds event result.1] := by
  classical
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    change Pr{let result ← (pure (value, before) : ProbComp _)}[event result.1] ≤
      Pr{let result ← (pure (.inr value, before) : ProbComp _)}[Succeeds event result.1]
    simp only [prEvent_pure, Succeeds, le_refl]
  | query_bind request next ih =>
    rw [capture_query]
    cases found : recognize request with
    | some witness =>
      simp only [simulateQ_pure, StateT.run_pure, prEvent_pure, Succeeds, ite_true]
      exact prEvent_le_one _
    | none =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply prEvent_bind_mono_of_forall_le_of_support
      intro result _called
      exact ih result.1 result.2

private theorem project_succeeds (joint : Primitives) (identity : PublicIdentity) (event : A → Prop)
    (result : Candidate joint identity ⊕ A) :
    Succeeds event (RegistrationNativeIdentityTemplateRecognitionErasure.project joint identity result) = Succeeds event result := by
  cases result <;> rfl

/-- Recognition and the continued output are one event of the same public execution, so this source cut introduces no second ordinary-EUF charge. All warm cache, optional failure and source-history conditions are the explicit earlier primitive/source receipts. -/
theorem loss (setup : PqxdhServerAuthExperiment.Setup base KemSK) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (seed : IdentitySeed) (before : RegistrationNativeIdentityCensorSource.State)
    (found : before.pool.seeds[selected]? = some seed) (target : before.target = some message)
    (known : ∀ input digest, before.hash.1 ((), input) = some digest → input ∈ before.hash.2)
    (unrecognized : ∀ input ∈ before.hash.2, RegistrationNativeIdentityRecognition.recognize
      setup.joint.verify (setup.joint.publicKeys seed).ed25519 message input = none)
    (work : OracleComp Old A) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (annotated : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected message))
    (policy : Policy) (held : policy.target = some message) (event : A → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder) work).run
      (RegistrationNativeIdentityTemplateFirstOmitted.after setup.joint selected message seed before))}[event result.1] ≤
      Pr{let result ← (execute setup.joint (setup.joint.publicKeys seed) selected placeholder work policy
        (RegistrationNativeIdentityTemplateFirstOmitted.install before) before.pool)}[Succeeds event result.1.1] := by
  have upper := capture_cover (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
    (RegistrationNativeIdentityTemplateSource.recognize setup.joint.verify (setup.joint.publicKeys seed).ed25519 message)
    work (RegistrationNativeIdentityTemplateFirstOmitted.after setup.joint selected message seed before) event
  have same := congrArg (fun distribution => Pr{let result ← distribution}[Succeeds event result])
    (continuation setup selected placeholder message seed before found target known unrecognized work scope annotated policy held)
  simp only [prEvent_map] at same
  rw [same] at upper
  simpa only [answer, project_succeeds] using upper

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic.continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic.continuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic.loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic.loss
