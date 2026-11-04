-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateOmissionPublic

/-! The literal accepted first-selector stem joins its complete physical-prefix scan to the public template continuation. Recognition and the submitted output remain one event of one executable client. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open RegistrationNativeIdentityTemplateOmissionPublic (client execute Succeeds)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old)
open RegistrationNativeIdentityCensorSource (State)
variable {A : Type}

private theorem client_select (joint : Primitives) (identity : PublicIdentity) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old A) :
    client joint identity placeholder (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued) =
      (do let answer ← Spec.query (.inl (.inl (.inr message)))
          client joint identity placeholder (continued answer)) := rfl

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem public_select (joint : Primitives) (identity : PublicIdentity) (selected : Nat)
    (placeholder : Ed25519Signature) (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old A)
    (policy picked : Policy) (hash : RegistrationNativeIdentityReindexedCtx.State RegistrationNativeIdentityTemplateAddress.Key)
    (pool : PqxdhDynamicIdentityPool.SourceState)
    (chosen : RegistrationNativeIdentityCensorPolicySource.choose message policy = (true, picked)) :
    execute joint identity selected placeholder (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued) policy hash pool =
      execute joint identity selected placeholder (continued true) picked hash pool := by
  simp only [execute, client_select, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, bind_apply, chosen, pure_bind]


private theorem capture_query {X W : Type} (recognize : Spec.Domain → Option W)
    (request : Spec.Domain) (next : Spec.Range request → OracleComp Spec X) :
    RegistrationNativeIdentityRecognitionCapture.capture recognize (Spec.query request >>= next) =
      (match recognize request with
      | some witness => pure (.inl witness)
      | none => do let answer ← Spec.query request
                   RegistrationNativeIdentityRecognitionCapture.capture recognize (next answer)) := rfl

private theorem client_scan (joint : Primitives) (identity : PublicIdentity) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes) (rest : Option Ed25519Signature → OracleComp Old A) :
    client joint identity placeholder (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer) =
    (match RegistrationNativeIdentityTemplateCensorRecognition.certifyScan joint identity message inputs with
    | some witness => pure (.inl witness)
    | none => do
        let _ ← Spec.query (.inl (.inr (message, inputs)))
        client joint identity placeholder (rest (some placeholder))) := by
  simp only [client, simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase, pure_bind]
  rw [capture_query]
  simp only [RegistrationNativeIdentityTemplateCensorRecognition.recognize]
  cases RegistrationNativeIdentityTemplateCensorRecognition.certifyScan joint identity message inputs <;> rfl

private theorem public_scan (joint : Primitives) (identity : PublicIdentity) (selected : Nat)
    (placeholder : Ed25519Signature) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (rest : Option Ed25519Signature → OracleComp Old A)
    (policy : Policy) (hash : RegistrationNativeIdentityReindexedCtx.State RegistrationNativeIdentityTemplateAddress.Key)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    execute joint identity selected placeholder (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer) policy hash pool =
    (match RegistrationNativeIdentityTemplateCensorRecognition.certifyScan joint identity message inputs with
    | some witness => pure ((.inl witness, (policy, hash)), pool)
    | none => execute joint identity selected placeholder (rest (some placeholder)) policy hash pool) := by
  simp only [execute, client_scan]
  cases RegistrationNativeIdentityTemplateCensorRecognition.certifyScan joint identity message inputs with
  | some witness => simp only [simulateQ_pure, StateT.run_pure]
  | none =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplatePolicy.handler,
        StateT.run, bind_apply, pure_apply, pure_bind]

private theorem physical_scan (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes) (rest : Option Ed25519Signature → OracleComp Old A)
    (seed : IdentitySeed) (before : State)
    (found : before.pool.seeds[selected]? = some seed) (held : before.target = some message) :
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer)).run before =
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (rest (some placeholder))).run
      (RegistrationNativeIdentityTemplateFirstOmitted.after joint selected message seed before) := by
  have scanned : (RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      (.inl (.inl (.inr (message, inputs))))).run before = pure ((), before) := rfl
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [scanned, pure_bind, RegistrationNativeIdentityTemplateFirstOmitted.marker joint selected placeholder message seed before found held,
    pure_bind]


def picked (message : Pqxdh.Bytes) (before : State) : State :=
  RegistrationNativeIdentityCensorPolicySource.afterSelection message true before

private theorem physical_select (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old A)
    (before : Policy × State) (aligned : RegistrationNativeIdentityCensorPolicySource.Aligned selected before)
    (chosen : RegistrationNativeIdentityCensorPolicySource.choose message before.1 = (true, {before.1 with target := some message})) :
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued)).run before.2 =
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (continued true)).run (picked message before.2) := by
  have actual := RegistrationNativeIdentityCensorPolicySource.select_source selected message before aligned
  rw [chosen] at actual
  change (RegistrationNativeIdentityCensorSource.censored joint selected placeholder
    (.inl (.inl (.inl (.inr message))))).run before.2 = pure (true, picked message before.2) at actual
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, actual, pure_bind]

/-- The literal actual first-selector stem has one public recognized-or-output probability. Cache admission, genuine-history choice and continued annotation are the exact same-cut source receipts. -/
def Stem (selected : Nat) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old A) : Prop :=
  ∃ rest : Option Ed25519Signature → OracleComp Old A,
    continued true = (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer) ∧ ∀ answer,
        (rest answer).AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed ∧
        (rest answer).AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected message)

theorem stem_loss {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected : Nat) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes) (seed : IdentitySeed)
    (before : Policy × State) (aligned : RegistrationNativeIdentityCensorPolicySource.Aligned selected before)
    (found : before.2.pool.seeds[selected]? = some seed)
    (known : RegistrationNativeIdentityCensorCacheProvenance.Known before.2)
    (chosen : RegistrationNativeIdentityCensorPolicySource.choose message before.1 = (true, {before.1 with target := some message}))
    (continued : Bool → OracleComp Old A)
    (guarded : Stem selected message before.2.hash.2 continued)
    (event : A → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued)).run before.2)}[event result.1] ≤
    Pr{let result ← (execute setup.joint (setup.joint.publicKeys seed) selected placeholder
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued) before.1
      (RegistrationNativeIdentityTemplateFirstOmitted.install before.2) before.2.pool)}[Succeeds event result.1.1] := by
  classical
  obtain ⟨rest, body, safe⟩ := guarded
  have physicalLaw := physical_select setup.joint selected placeholder message continued before aligned chosen
  rw [body, physical_scan setup.joint selected placeholder message before.2.hash.2 rest seed
    (picked message before.2) found rfl] at physicalLaw
  have publicLaw := public_select setup.joint (setup.joint.publicKeys seed) selected placeholder message continued
    before.1 {before.1 with target := some message} (RegistrationNativeIdentityTemplateFirstOmitted.install before.2) before.2.pool chosen
  rw [body, public_scan] at publicLaw
  rw [physicalLaw, publicLaw]
  cases scanned : RegistrationNativeIdentityTemplateCensorRecognition.certifyScan setup.joint (setup.joint.publicKeys seed) message before.2.hash.2 with
  | some witness =>
    simp only [prEvent_pure, Succeeds, ite_true]
    exact prEvent_le_one _
  | none =>
    have negative : RegistrationNativeIdentityRecognitionJournal.scan setup.joint.verify
        (setup.joint.publicKeys seed).ed25519 message before.2.hash.2 = none := by
      unfold RegistrationNativeIdentityTemplateCensorRecognition.certifyScan at scanned
      split at scanned
      · assumption
      · cases scanned
    have unrecognized : ∀ input ∈ (picked message before.2).hash.2,
        RegistrationNativeIdentityRecognition.recognize setup.joint.verify (setup.joint.publicKeys seed).ed25519 message input = none := by
      intro input member
      exact List.findSome?_eq_none_iff.mp negative input member
    exact RegistrationNativeIdentityTemplateOmissionPublic.loss setup selected placeholder message seed
      (picked message before.2) found rfl (fun input _digest present => known input (by
        intro absent
        have impossible := present.symm.trans absent
        cases impossible)) unrecognized (rest (some placeholder))
      (safe (some placeholder)).1 (safe (some placeholder)).2 {before.1 with target := some message} rfl event


theorem first_loss {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected : Nat) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes) (seed : IdentitySeed)
    (before : Policy × State) (aligned : RegistrationNativeIdentityCensorPolicySource.Aligned selected before)
    (found : before.2.pool.seeds[selected]? = some seed)
    (known : RegistrationNativeIdentityCensorCacheProvenance.Known before.2)
    (chosen : RegistrationNativeIdentityCensorPolicySource.choose message before.1 = (true, {before.1 with target := some message}))
    (continued : Bool → OracleComp Old (A × RegistrationNativeIdentityCensorCompiler.Mode))
    (guarded : RegistrationNativeIdentityTemplateSelectionPrefixScope.GuardedStem selected message before.2.hash.2 continued)
    (event : (A × RegistrationNativeIdentityCensorCompiler.Mode) → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued)).run before.2)}[event result.1] ≤
    Pr{let result ← (execute setup.joint (setup.joint.publicKeys seed) selected placeholder
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued) before.1
      (RegistrationNativeIdentityTemplateFirstOmitted.install before.2) before.2.pool)}[Succeeds event result.1.1] := by
  obtain ⟨rest, body, safe⟩ := guarded
  exact stem_loss setup selected placeholder message seed before aligned found known chosen continued
    ⟨rest, body, fun answer => ⟨(safe answer).1, (safe answer).2.1⟩⟩ event

/-- Applying the complete actual first-selector cut discharges the local source conditions of the physical/public probability inequality. All installation and tail conditions come from that same supported run. -/
theorem actual_cut {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected : Nat) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true) (seed : IdentitySeed)
    (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec A)
    (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (control : RegistrationNativeIdentityTemplateSelectionPrefixScope.Ready mode) (arming : mode.armed = true)
    (before : Policy × State) (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected before)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (fresh : message ∉ RegistrationNativeIdentityCensorPolicySource.messages selected before.2.pool)
    (found : before.2.pool.seeds[selected]? = some seed)
    (continued : Bool → OracleComp Old (A × RegistrationNativeIdentityCensorCompiler.Mode)) (after : Policy × State)
    (reached : (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued, after) ∈ support
      ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler setup.joint selected placeholder)
        (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
          ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before))
    (event : (A × RegistrationNativeIdentityCensorCompiler.Mode) → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued)).run after.2)}[event result.1] ≤
    Pr{let result ← (execute setup.joint (setup.joint.publicKeys seed) selected placeholder
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued) after.1
      (RegistrationNativeIdentityTemplateFirstOmitted.install after.2) after.2.pool)}[Succeeds event result.1.1] := by
  obtain ⟨ready, _fresh, row, chosen, guarded⟩ := RegistrationNativeIdentityTemplateSelectionSource.first_cut
    setup.joint selected placeholder message role seed work mode control arming before prior journal fresh found continued after reached
  exact first_loss setup selected placeholder message seed after ready.aligned row ready.known chosen continued guarded event

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss.first_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss.first_loss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss.actual_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss.actual_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss.stem_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss.stem_loss
