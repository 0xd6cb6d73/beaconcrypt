-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPrefixJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorForwardScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetAnnotations

/-! Before its first public selector, actual lowering retains the physical public-input prefix even when the fixed bundle attempt is armed. The cut keeps the entire original continuation for the source/E stopping argument. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPrefix (SourceSpec record)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old Cut stop)
open RegistrationNativeIdentityTemplatePublicPrefix (Allowed)
variable {A B : Type}

def Ready (mode : Mode) : Prop := mode.target = none ∧ mode.active = false

def Safe (work : OracleComp Old (Cut (A × Mode))) : Prop :=
  work.AllQueriesSatisfy Allowed ∧
    ∀ value after, Cut.returned (value, after) ∈ support work → Ready after

private theorem stop_forwarded (work : OracleComp Old A) (allowed : work.AllQueriesSatisfy Allowed) :
    stop work = Cut.returned <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    rw [RegistrationNativeIdentityTemplateSelectionCut.Original.step]
    rcases query with (((protocol | selection) | scanned) | described) | marker
    · simp only [map_bind]
      exact bind_congr (fun reply => ih reply (later reply))
    · exact False.elim first
    · simp only [map_bind]
      exact bind_congr (fun reply => ih reply (later reply))
    · simp only [map_bind]
      exact bind_congr (fun reply => ih reply (later reply))
    · exact False.elim first

private theorem record_scope (request : SourceSpec.Domain) (mode : Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode)).AllQueriesSatisfy Allowed := by
  cases request <;>
    simp only [record, StateT.run, simulateQ_bind, simulateQ_pure,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed] <;>
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨by trivial, fun _ => allQueriesSatisfy_pure _ _⟩

private theorem record_ready (request : SourceSpec.Domain) (mode : Mode) (prior : Ready mode)
    (result : SourceSpec.Range request × Mode)
    (reached : result ∈ support (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))) :
    Ready result.2 := by
  cases request <;>
    simp only [record, StateT.run,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed, bind_pure_comp, simulateQ_map, support_map] at reached
  all_goals obtain ⟨reply, _possible, rfl⟩ := reached
  all_goals exact prior

private theorem record_safe (request : SourceSpec.Domain) (mode : Mode) (prior : Ready mode) :
    Safe (stop (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))) := by
  rw [stop_forwarded _ (record_scope request mode)]
  refine ⟨RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ (record_scope request mode), ?_⟩
  intro value after reached
  rw [support_map] at reached
  obtain ⟨actual, called, same⟩ := reached
  cases Cut.returned.inj same
  exact record_ready request mode prior (value, after) called

def Nonsign (selected : Nat) : SourceSpec.Domain → Prop
  | .inl (.inl (.inr (.service handle (.sign message)))) =>
      ¬ (handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message)
  | _ => True

private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (mode : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run mode =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run mode) := rfl

private theorem plain (selected : Nat) (placeholder : Ed25519Signature) (request : SourceSpec.Domain)
    (mode : Mode) (prior : Ready mode) (nonsign : Nonsign selected request) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode =
      simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode) := by
  rcases mode with ⟨bundles, armed, active, target, inputs⟩
  change target = none ∧ active = false at prior
  rcases prior with ⟨rfl, rfl⟩
  rcases request with ((coin | query) | report) | bytes
  · rfl
  · cases query with
    | create | reveal handle => rfl
    | service handle request => cases request with
      | staticDh peer => rfl
      | sign message =>
        change ¬ (handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) at nonsign
        have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run
            ⟨bundles, armed, false, none, inputs⟩ = pure ((), ⟨bundles, armed, false, none, inputs⟩) := by
          simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, nonsign, ite_false]
        change (RegistrationNativeIdentityCensorOperational.signing selected handle message).run _ = _
        simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, promote_run,
          prepared, simulateQ_pure, pure_bind, StateT.run_get, reduceCtorEq, and_false, ite_false]
        rfl
  · rfl
  · rfl

private theorem selected_safe (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (A × Mode)) :
    Safe (pure (Cut.selected message continued)) := by
  refine ⟨allQueriesSatisfy_pure _ _, ?_⟩
  intro value after reached
  simp only [mem_support_pure_iff, reduceCtorEq] at reached

private theorem armed (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode) (prior : Ready mode)
    (arming : mode.armed = true) (eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) :
    ∃ continued, stop ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode) =
      pure (Cut.selected message continued) := by
  rcases mode with ⟨bundles, armed, active, target, inputs⟩
  change target = none ∧ active = false at prior
  rcases prior with ⟨rfl, rfl⟩
  change armed = true at arming
  subst armed
  obtain ⟨same, role⟩ := eligible
  subst handle
  have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run
      ⟨bundles, true, false, none, inputs⟩ = (do
        let chosen ← RegistrationNativeIdentityCensorCompiler.select message
        if chosen then RegistrationNativeIdentityCensorCompiler.inspect message inputs else pure ()
        pure ((), (⟨bundles, true, (if chosen then some message else none) == some message,
          (if chosen then some message else none), inputs⟩ : Mode))) := by
    simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, role]
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, promote_run,
    prepared, simulateQ_bind, RegistrationNativeIdentityCensorCompiler.select, simulateQ_spec_query,
    RegistrationNativeIdentityCensorOperational.embed, bind_assoc]
  rw [RegistrationNativeIdentityTemplateSelectionCut.Original.step]
  exact ⟨_, rfl⟩

/-- The literal current source query has only public physical prefix requests before its first selector, even on an armed attempt. A returned query retains the unselected/inactive control state. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature) (request : SourceSpec.Domain)
    (mode : Mode) (prior : Ready mode) :
    Safe (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)) := by
  cases arming : mode.armed with
  | false =>
    rw [RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder request mode ⟨arming, prior.1, prior.2⟩]
    exact record_safe request mode prior
  | true =>
    by_cases nonsign : Nonsign selected request
    · rw [plain selected placeholder request mode prior nonsign]
      exact record_safe request mode prior
    · rcases request with ((coin | request) | report) | bytes
      · exact False.elim (nonsign trivial)
      · cases request with
        | create | reveal handle => exact False.elim (nonsign trivial)
        | service handle request => cases request with
          | staticDh peer => exact False.elim (nonsign trivial)
          | sign message =>
            change ¬¬(handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) at nonsign
            obtain ⟨continued, equal⟩ := armed selected handle message mode prior arming (Classical.not_not.mp nonsign)
            change Safe (stop ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode))
            rw [equal]
            exact selected_safe message continued
      · exact False.elim (nonsign trivial)
      · exact False.elim (nonsign trivial)

private theorem bind_safe {X Y : Type} (work : OracleComp Old X) (next : X → OracleComp Old Y)
    (prior : work.AllQueriesSatisfy Allowed)
    (later : ∀ value ∈ support work, (next value).AllQueriesSatisfy Allowed) :
    (work >>= next).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => exact later value (by simp only [mem_support_pure_iff])
  | query_bind request rest ih =>
    obtain ⟨first, continued⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [bind_assoc, allQueriesSatisfy_query_bind_iff]
    refine ⟨first, fun reply => ih reply (continued reply) ?_⟩
    intro value reached
    apply later value
    rw [mem_support_bind_iff]
    exact ⟨reply, by simp only [support_query, Set.mem_univ], reached⟩

/-- Before the first selector, the complete actual lowered program has only public physical requests. If it returns without selecting, its absent target and inactive mode remain exact. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp SourceSpec A)
    (mode : Mode) (prior : Ready mode) :
    Safe (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)) := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value =>
    change Safe (pure (Cut.returned (value, mode)))
    refine ⟨allQueriesSatisfy_pure _ _, ?_⟩
    intro returned after reached
    have same := eq_of_mem_support_pure _ reached
    cases Cut.returned.inj same
    exact prior
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [RegistrationNativeIdentityTemplateSelectionCut.Original.bind]
    have first := query selected placeholder request mode prior
    constructor
    · apply bind_safe _ _ first.1
      intro cut reached
      cases cut with
      | returned result => exact (ih result.1 result.2 (first.2 result.1 result.2 reached)).1
      | selected message continued => exact allQueriesSatisfy_pure _ _
    · intro value after reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨cut, called, continued⟩ := reached
      cases cut with
      | returned result => exact (ih result.1 result.2 (first.2 result.1 result.2 called)).2 value after continued
      | selected message next => simp only [mem_support_pure_iff, reduceCtorEq] at continued

/-- The original physical source has the public policy/table interpretation at its actual first-selector cut. The entire frontend/platform value and original continuation remain at that same cut. -/
theorem physical_prefix (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec A) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State) :
    Prod.map id RegistrationNativeIdentityTemplatePublicPrefix.project <$>
      (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
        (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before =
      (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected)
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
          (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)))).run
        (RegistrationNativeIdentityTemplatePublicPrefix.project before) :=
  RegistrationNativeIdentityTemplatePublicPrefix.program joint selected placeholder _ (program selected placeholder work mode prior).1 before

/-- Executable erasure takes the actual same physical first-selector prefix to the public first-selector prefix, retaining its exact reply-dependent continuation and all represented source state. -/
theorem source_cut (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec A) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State) :
    Prod.map (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder)
      RegistrationNativeIdentityTemplatePublicPrefix.project <$>
      (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
        (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before =
      (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected)
        (RegistrationNativeIdentityTemplateSelectionCut.stop
          (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
            ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)))).run
        (RegistrationNativeIdentityTemplatePublicPrefix.project before) := by
  have coupled := physical_prefix joint selected placeholder work mode prior before
  have observed := congrArg (Functor.map (Prod.map (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder) id)) coupled
  have erased := congrArg (fun code => (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected) code).run
    (RegistrationNativeIdentityTemplatePublicPrefix.project before))
      (RegistrationNativeIdentityTemplateSelectionCut.Original.erase_stop placeholder
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))
  simp only [simulateQ_map, StateT.run_map] at erased
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed.trans erased

def Stem (selected : Nat) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old A) : Prop :=
  ∃ rest : Option Ed25519Signature → OracleComp Old A,
    continued true = (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer)

def SourceShape (selected : Nat)
    (result : Cut (A × Mode) × (RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)) : Prop :=
  match result.1 with
  | .returned (_, mode) => Ready mode ∧ RegistrationNativeIdentityCensorPrefixJournal.Aligned mode result.2.2
  | .selected message continued => Stem selected message result.2.2.hash.2 continued

private theorem record_shape {S : Type} (impl : QueryImpl Old (StateT S ProbComp)) (request : SourceSpec.Domain)
    (mode : Mode) (before : S) :
    (simulateQ impl (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))).run before =
      (fun result => ((result.1, RegistrationNativeIdentityCensorPrefix.next mode request), result.2)) <$>
        (simulateQ impl (simulateQ RegistrationNativeIdentityCensorOperational.embed
          (RegistrationNativeIdentityCensorPrefix.embed request))).run before := by
  simp only [record, StateT.run, bind_pure_comp, simulateQ_map]
  exact StateT.run_map _ _ _

private theorem recorded_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : SourceSpec.Domain) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (result : Cut (SourceSpec.Range request × Mode) × (RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State))
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode)))).run before)) :
    SourceShape selected result := by
  rw [stop_forwarded _ (record_scope request mode)] at reached
  simp only [simulateQ_map, StateT.run_map, support_map] at reached
  obtain ⟨actual, called, rfl⟩ := reached
  have raw : (actual.1, actual.2.2) ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))).run before.2) := by
    rw [← RegistrationNativeIdentityCensorPolicySource.program_erasure joint selected placeholder _ before, support_map]
    exact ⟨actual, called, rfl⟩
  have afterJournal := RegistrationNativeIdentityCensorPrefixJournal.recorded_program joint selected placeholder
    (SourceSpec.query request) mode before.2 journal (actual.1, actual.2.2) (by simpa only [simulateQ_spec_query] using raw)
  change Ready actual.1.2 ∧ RegistrationNativeIdentityCensorPrefixJournal.Aligned actual.1.2 actual.2.2
  refine ⟨?_, afterJournal⟩
  rw [record_shape, support_map] at called
  obtain ⟨returned, _called, same⟩ := called
  cases same
  cases request <;> exact prior

private theorem stem_bind {X Y : Type} (selected : Nat) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old X) (next : X → OracleComp Old Y) (prior : Stem selected message inputs continued) :
    Stem selected message inputs (fun reply => continued reply >>= next) := by
  obtain ⟨rest, body⟩ := prior
  refine ⟨fun answer => rest answer >>= next, ?_⟩
  simpa only [bind_assoc] using congrArg (fun code => code >>= next) body

/-- The actual current query's supported first selector scans exactly the reached physical journal and then emits the canonical marker. Returned queries retain journal alignment for the next source query. -/
theorem query_stem (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : SourceSpec.Domain) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (result : Cut (SourceSpec.Range request × Mode) × (RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State))
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode))).run before)) :
    SourceShape selected result := by
  cases arming : mode.armed with
  | false =>
    rw [RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder request mode ⟨arming, prior.1, prior.2⟩] at reached
    exact recorded_source joint selected placeholder request mode prior before journal result reached
  | true =>
    by_cases nonsign : Nonsign selected request
    · rw [plain selected placeholder request mode prior nonsign] at reached
      exact recorded_source joint selected placeholder request mode prior before journal result reached
    · rcases request with ((coin | request) | report) | bytes
      · exact False.elim (nonsign trivial)
      · cases request with
        | create | reveal handle => exact False.elim (nonsign trivial)
        | service handle request => cases request with
          | staticDh peer => exact False.elim (nonsign trivial)
          | sign message =>
            change ¬¬(handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) at nonsign
            obtain ⟨same, role⟩ := Classical.not_not.mp nonsign
            subst handle
            obtain ⟨continued, equal, rest, body⟩ := RegistrationNativeIdentityTemplateSigningStem.selection selected message mode role arming prior.1 prior.2
            change result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
              (stop ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode))).run before) at reached
            rw [equal, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
            cases reached
            refine ⟨rest, ?_⟩
            change mode.knownInputs = before.2.hash.2 at journal
            rw [← journal]
            exact body
      · exact False.elim (nonsign trivial)
      · exact False.elim (nonsign trivial)

/-- The entire actual supported first-selector cut carries the literal complete-prefix scan and following canonical omission, with its original continuation intact. -/
theorem program_stem (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec A) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (result : Cut (A × Mode) × (RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State))
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    SourceShape selected result := by
  induction work using OracleComp.inductionOn generalizing mode before result with
  | pure value =>
    change result ∈ support (pure (Cut.returned (value, mode), before)) at reached
    obtain rfl := eq_of_mem_support_pure _ reached
    exact ⟨prior, journal⟩
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      RegistrationNativeIdentityTemplateSelectionCut.Original.bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    have shape := query_stem joint selected placeholder request mode prior before journal middle called
    rcases middle with ⟨cut, after⟩
    cases cut with
    | returned current =>
      exact ih current.1 current.2 shape.1 after shape.2 result continued
    | selected message body =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact stem_bind selected message _ body _ shape


private theorem record_forward (selected : Nat) (wanted : Pqxdh.Bytes)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted = true) (request : SourceSpec.Domain)
    (nonsign : Nonsign selected request) (mode : Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode)).AllQueriesSatisfy
      (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted) := by
  have first : ∀ request : PqxdhJointPhase1Reports.ProtocolSpec.Domain,
      Nonsign selected (.inl request) →
      RegistrationNativeIdentityCensorForwardScope.ProtocolAllowed selected wanted request := by
    intro q allowed
    rcases q with (coin | q) | report
    · trivial
    · cases q with
      | create | reveal handle => trivial
      | service handle q => cases q with
        | staticDh peer => trivial
        | sign message =>
          intro same equal
          change ¬ (handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) at allowed
          exact allowed ⟨same, equal.symm ▸ role⟩
    · trivial
  cases request with
  | inl request =>
    simp only [record, StateT.run, simulateQ_bind, simulateQ_pure,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first request nonsign, fun _ => allQueriesSatisfy_pure _ _⟩
  | inr input =>
    simp only [record, StateT.run, simulateQ_bind, simulateQ_pure,
      RegistrationNativeIdentityCensorPrefix.embed, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => allQueriesSatisfy_pure _ _⟩

private theorem record_armed (request : SourceSpec.Domain) (mode : Mode)
    (result : SourceSpec.Range request × Mode)
    (reached : result ∈ support (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))) :
    result.2.armed = mode.armed := by
  cases request <;>
    simp only [record, StateT.run,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed, bind_pure_comp, simulateQ_map, support_map] at reached
  all_goals obtain ⟨reply, _possible, rfl⟩ := reached
  all_goals rfl

/-- Before its first selector, an armed source query cannot forward any selected one-time target to the genuine signing service. Returning without selection keeps the attempt armed. -/
theorem query_fresh_scope (selected : Nat) (placeholder : Ed25519Signature) (wanted : Pqxdh.Bytes)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted = true) (request : SourceSpec.Domain)
    (mode : Mode) (prior : Ready mode) (arming : mode.armed = true) :
    (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)).AllQueriesSatisfy
      (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted) ∧
    ∀ value after, Cut.returned (value, after) ∈ support (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)) →
      Ready after ∧ after.armed = true := by
  by_cases nonsign : Nonsign selected request
  · rw [plain selected placeholder request mode prior nonsign, stop_forwarded _ (record_scope request mode)]
    refine ⟨RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ (record_forward selected wanted role request nonsign mode), ?_⟩
    intro value after reached
    rw [support_map] at reached
    obtain ⟨actual, called, same⟩ := reached
    cases Cut.returned.inj same
    exact ⟨record_ready request mode prior (value, after) called, (record_armed request mode (value, after) called).trans arming⟩
  · rcases request with ((coin | request) | report) | bytes
    · exact False.elim (nonsign trivial)
    · cases request with
      | create | reveal handle => exact False.elim (nonsign trivial)
      | service handle request => cases request with
        | staticDh peer => exact False.elim (nonsign trivial)
        | sign message =>
          change ¬¬(handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) at nonsign
          obtain ⟨continued, equal⟩ := armed selected handle message mode prior arming (Classical.not_not.mp nonsign)
          change (stop ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).AllQueriesSatisfy _ ∧ _
          rw [equal]
          refine ⟨allQueriesSatisfy_pure _ _, ?_⟩
          intro value after reached
          change Cut.returned (value, after) ∈ support (stop ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)) at reached
          rw [equal, mem_support_pure_iff] at reached
          cases reached
    · exact False.elim (nonsign trivial)
    · exact False.elim (nonsign trivial)


private theorem bind_forward {X Y : Type} (selected : Nat) (wanted : Pqxdh.Bytes)
    (work : OracleComp Old X) (next : X → OracleComp Old Y)
    (prior : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted))
    (later : ∀ value ∈ support work, (next value).AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted)) :
    (work >>= next).AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact later value (by simp only [mem_support_pure_iff])
  | query_bind request rest ih =>
    obtain ⟨first, continued⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [bind_assoc, allQueriesSatisfy_query_bind_iff]
    refine ⟨first, fun reply => ih reply (continued reply) ?_⟩
    intro value reached
    apply later value
    rw [mem_support_bind_iff]
    exact ⟨reply, by simp only [support_query, Set.mem_univ], reached⟩

/-- The complete armed first-selector prefix excludes genuine signing of every selected one-time target. This follows from the actual stopped lowering, including arbitrary failure replies. -/
theorem program_fresh_scope (selected : Nat) (placeholder : Ed25519Signature) (wanted : Pqxdh.Bytes)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted = true) (work : OracleComp SourceSpec A)
    (mode : Mode) (prior : Ready mode) (arming : mode.armed = true) :
    (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).AllQueriesSatisfy
      (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted) ∧
    ∀ value after, Cut.returned (value, after) ∈ support (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)) →
      Ready after ∧ after.armed = true := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value =>
    change (pure (Cut.returned (value, mode)) : OracleComp Old _).AllQueriesSatisfy _ ∧ _
    refine ⟨allQueriesSatisfy_pure _ _, ?_⟩
    intro returned after reached
    have same := eq_of_mem_support_pure _ reached
    cases Cut.returned.inj same
    exact ⟨prior, arming⟩
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [RegistrationNativeIdentityTemplateSelectionCut.Original.bind]
    have first := query_fresh_scope selected placeholder wanted role request mode prior arming
    constructor
    · apply bind_forward selected wanted _ _ first.1
      intro cut reached
      cases cut with
      | returned result =>
        have stable := first.2 result.1 result.2 reached
        exact (ih result.1 result.2 stable.1 stable.2).1
      | selected message continued => exact allQueriesSatisfy_pure _ _
    · intro value after reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨cut, called, continued⟩ := reached
      cases cut with
      | returned result =>
        have stable := first.2 result.1 result.2 called
        exact (ih result.1 result.2 stable.1 stable.2).2 value after continued
      | selected message next => simp only [mem_support_pure_iff, reduceCtorEq] at continued


def GuardedTail (selected : Nat) (message : Pqxdh.Bytes) (work : OracleComp Old (A × Mode)) : Prop :=
  work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed ∧
  work.AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected message) ∧
  ∀ result ∈ support work, result.2.target = some message

def GuardedStem (selected : Nat) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old (A × Mode)) : Prop :=
  ∃ rest : Option Ed25519Signature → OracleComp Old (A × Mode),
    continued true = (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer) ∧ ∀ answer, GuardedTail selected message (rest answer)

private theorem record_not_selected (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : SourceSpec.Domain) (mode : Mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (SourceSpec.Range request × Mode))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode)))).run before)) : False := by
  rw [stop_forwarded _ (record_scope request mode)] at reached
  simp only [simulateQ_map, StateT.run_map, support_map] at reached
  obtain ⟨actual, _called, same⟩ := reached
  have impossible := congrArg Prod.fst same
  cases impossible

/-- The current first selector carries an actual post-selection tail with source-derived template width and target annotations. Every optional reply remains represented. -/
theorem query_guarded_stem (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : SourceSpec.Domain) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (SourceSpec.Range request × Mode))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode))).run before)) :
    GuardedStem selected message after.2.hash.2 continued := by
  cases arming : mode.armed with
  | false =>
    rw [RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder request mode ⟨arming, prior.1, prior.2⟩] at reached
    exact False.elim (record_not_selected joint selected placeholder request mode before message continued after reached)
  | true =>
    by_cases nonsign : Nonsign selected request
    · rw [plain selected placeholder request mode prior nonsign] at reached
      exact False.elim (record_not_selected joint selected placeholder request mode before message continued after reached)
    · rcases request with ((coin | request) | report) | bytes
      · exact False.elim (nonsign trivial)
      · cases request with
        | create | reveal handle => exact False.elim (nonsign trivial)
        | service handle request => cases request with
          | staticDh peer => exact False.elim (nonsign trivial)
          | sign current =>
            change ¬¬(handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime current) at nonsign
            obtain ⟨same, role⟩ := Classical.not_not.mp nonsign
            subst handle
            obtain ⟨body, equal, terminal⟩ := RegistrationNativeIdentityTemplateSigningStem.selection_tail selected current mode role arming prior.1 prior.2
            change (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
              (stop ((RegistrationNativeIdentityCensorOperational.signing selected selected current).run mode))).run before) at reached
            rw [equal, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
            cases reached
            refine ⟨fun answer => pure (answer, {mode with active := true, target := some message}), ?_, ?_⟩
            · change mode.knownInputs = before.2.hash.2 at journal
              rw [← journal]
              exact terminal
            · intro answer
              refine ⟨allQueriesSatisfy_pure _ _, allQueriesSatisfy_pure _ _, ?_⟩
              intro result called
              obtain rfl := eq_of_mem_support_pure _ called
              rfl
      · exact False.elim (nonsign trivial)
      · exact False.elim (nonsign trivial)


private theorem bind_scoped {X Y : Type} (scope : Old.Domain → Prop)
    (work : OracleComp Old X) (next : X → OracleComp Old Y)
    (prior : work.AllQueriesSatisfy scope)
    (later : ∀ value ∈ support work, (next value).AllQueriesSatisfy scope) :
    (work >>= next).AllQueriesSatisfy scope := by
  induction work using OracleComp.inductionOn with
  | pure value => exact later value (by simp only [mem_support_pure_iff])
  | query_bind request rest ih =>
    obtain ⟨first, continued⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [bind_assoc, allQueriesSatisfy_query_bind_iff]
    refine ⟨first, fun reply => ih reply (continued reply) ?_⟩
    intro value reached
    apply later value
    rw [mem_support_bind_iff]
    exact ⟨reply, by simp only [support_query, Set.mem_univ], reached⟩

private theorem tail_bind {X Y : Type} (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (work : OracleComp Old (X × Mode)) (next : X → OracleComp SourceSpec Y)
    (prior : GuardedTail selected message work) :
    GuardedTail selected message (work >>= fun current =>
      (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2) := by
  refine ⟨bind_scoped _ _ _ prior.1 ?_, bind_scoped _ _ _ prior.2.1 ?_, ?_⟩
  · intro current _reached
    exact RegistrationNativeIdentityCensorTemplateScope.program selected placeholder (next current.1) current.2
  · intro current reached
    exact (RegistrationNativeIdentityCensorTargetAnnotations.program selected placeholder message (next current.1) current.2 (prior.2.2 current reached)).1
  · intro result reached
    rw [mem_support_bind_iff] at reached
    obtain ⟨current, called, continued⟩ := reached
    exact (RegistrationNativeIdentityCensorTargetAnnotations.program selected placeholder message (next current.1) current.2 (prior.2.2 current called)).2 result continued

private theorem guarded_stem_bind {X Y : Type} (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old (X × Mode)) (next : X → OracleComp SourceSpec Y)
    (prior : GuardedStem selected message inputs continued) :
    GuardedStem selected message inputs (fun answer => continued answer >>= fun current =>
      (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2) := by
  obtain ⟨rest, body, safe⟩ := prior
  refine ⟨fun answer => rest answer >>= fun current =>
    (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2, ?_, ?_⟩
  · simpa only [bind_assoc] using congrArg (fun code => code >>= fun current =>
      (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2) body
  · intro answer
    exact tail_bind selected placeholder message (rest answer) next (safe answer)

/-- At every actual first-selector cut, the unchanged complete continuation has a literal scan/omission stem and a source-derived guarded tail. The latter retains all adaptive subsequent source effects. -/
theorem program_guarded_stem (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec A) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (A × Mode))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    GuardedStem selected message after.2.hash.2 continued := by
  induction work using OracleComp.inductionOn generalizing mode before message continued after with
  | pure value =>
    change (Cut.selected message continued, after) ∈ support (pure (Cut.returned (value, mode), before)) at reached
    obtain impossible := eq_of_mem_support_pure _ reached
    cases impossible
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      RegistrationNativeIdentityTemplateSelectionCut.Original.bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, following⟩ := reached
    have shape := query_stem joint selected placeholder request mode prior before journal middle called
    rcases middle with ⟨cut, state⟩
    cases cut with
    | returned current =>
      exact ih current.1 current.2 shape.1 state shape.2 message continued after following
    | selected current body =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at following
      cases following
      exact guarded_stem_bind selected placeholder message _ body next
        (query_guarded_stem joint selected placeholder request mode prior before journal message body after called)


/-- Public hash descriptors have no selected message before the first selector. The retroactive scan follows selection, so there is no earlier scan or recognition marker in this prefix. -/
def BeforeSelection : Old.Domain → Prop
  | .inl (.inl (.inl (.inl _))) => True
  | .inl (.inr described) => described.message = none ∧ described.input.isSome
  | _ => False

private theorem record_before_selection (request : SourceSpec.Domain) (mode : Mode) :
    (stop (simulateQ RegistrationNativeIdentityCensorOperational.embed ((record request).run mode))).AllQueriesSatisfy BeforeSelection := by
  rw [stop_forwarded _ (record_scope request mode)]
  apply RegistrationNativeIdentityMainNoRevealCore.mapped
  cases request <;>
    simp only [record, StateT.run, simulateQ_bind, simulateQ_pure,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed] <;>
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨by trivial, fun _ => allQueriesSatisfy_pure _ _⟩

private theorem query_before_selection (selected : Nat) (placeholder : Ed25519Signature) (request : SourceSpec.Domain)
    (mode : Mode) (prior : Ready mode) :
    (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)).AllQueriesSatisfy BeforeSelection := by
  cases arming : mode.armed with
  | false =>
    rw [RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder request mode ⟨arming, prior.1, prior.2⟩]
    exact record_before_selection request mode
  | true =>
    by_cases nonsign : Nonsign selected request
    · rw [plain selected placeholder request mode prior nonsign]
      exact record_before_selection request mode
    · rcases request with ((coin | request) | report) | bytes
      · exact False.elim (nonsign trivial)
      · cases request with
        | create | reveal handle => exact False.elim (nonsign trivial)
        | service handle request => cases request with
          | staticDh peer => exact False.elim (nonsign trivial)
          | sign message =>
            change ¬¬(handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message) at nonsign
            obtain ⟨continued, equal⟩ := armed selected handle message mode prior arming (Classical.not_not.mp nonsign)
            change (stop ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).AllQueriesSatisfy _
            rw [equal]
            exact allQueriesSatisfy_pure _ _
      · exact False.elim (nonsign trivial)
      · exact False.elim (nonsign trivial)

/-- Every literal source first-selector prefix has only genuine protocol calls and public hash inputs tagged with no selected message. This includes an armed chosen bundle. -/
theorem before_selection (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp SourceSpec A)
    (mode : Mode) (prior : Ready mode) :
    (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).AllQueriesSatisfy BeforeSelection := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [RegistrationNativeIdentityTemplateSelectionCut.Original.bind]
    have controls := query selected placeholder request mode prior
    apply bind_scoped _ _ _ (query_before_selection selected placeholder request mode prior)
    intro cut reached
    cases cut with
    | returned current => exact ih current.1 current.2 (controls.2 current.1 current.2 reached)
    | selected message continued => exact allQueriesSatisfy_pure _ _

/-- The actual post-selection tail forwards no genuine selected-target signing request. -/
def ForwardTail (selected : Nat) (message : Pqxdh.Bytes) (work : OracleComp Old (A × Mode)) : Prop :=
  work.AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) ∧
    ∀ result ∈ support work, result.2.target = some message

def ForwardStem (selected : Nat) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old (A × Mode)) : Prop :=
  ∃ rest : Option Ed25519Signature → OracleComp Old (A × Mode),
    continued true = (do
      let _ ← Old.query (.inl (.inl (.inr (message, inputs))))
      let answer ← Old.query (.inr (.omitted selected message))
      rest answer) ∧ ∀ answer, ForwardTail selected message (rest answer)

theorem query_forward_stem (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : SourceSpec.Domain) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (SourceSpec.Range request × Mode))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode))).run before)) :
    ForwardStem selected message after.2.hash.2 continued := by
  cases arming : mode.armed with
  | false =>
    rw [RegistrationNativeIdentityCensorOperationalPrefix.query selected placeholder request mode ⟨arming, prior.1, prior.2⟩] at reached
    exact False.elim (record_not_selected joint selected placeholder request mode before message continued after reached)
  | true =>
    by_cases nonsign : Nonsign selected request
    · rw [plain selected placeholder request mode prior nonsign] at reached
      exact False.elim (record_not_selected joint selected placeholder request mode before message continued after reached)
    · rcases request with ((coin | request) | report) | bytes
      · exact False.elim (nonsign trivial)
      · cases request with
        | create | reveal handle => exact False.elim (nonsign trivial)
        | service handle request => cases request with
          | staticDh peer => exact False.elim (nonsign trivial)
          | sign current =>
            change ¬¬(handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime current) at nonsign
            obtain ⟨same, role⟩ := Classical.not_not.mp nonsign
            subst handle
            obtain ⟨body, equal, terminal⟩ := RegistrationNativeIdentityTemplateSigningStem.selection_tail selected current mode role arming prior.1 prior.2
            change (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
              (stop ((RegistrationNativeIdentityCensorOperational.signing selected selected current).run mode))).run before) at reached
            rw [equal, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
            cases reached
            refine ⟨fun answer => pure (answer, {mode with active := true, target := some message}), ?_, ?_⟩
            · change mode.knownInputs = before.2.hash.2 at journal
              rw [← journal]
              exact terminal
            · intro answer
              refine ⟨allQueriesSatisfy_pure _ _, ?_⟩
              intro result called
              obtain rfl := eq_of_mem_support_pure _ called
              rfl
      · exact False.elim (nonsign trivial)
      · exact False.elim (nonsign trivial)


private theorem forward_tail_bind {X Y : Type} (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (work : OracleComp Old (X × Mode)) (next : X → OracleComp SourceSpec Y)
    (prior : ForwardTail selected message work) :
    ForwardTail selected message (work >>= fun current =>
      (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2) := by
  refine ⟨bind_scoped _ _ _ prior.1 ?_, ?_⟩
  · intro current reached
    exact (RegistrationNativeIdentityCensorForwardScope.program selected placeholder message (next current.1) current.2 (prior.2 current reached)).1
  · intro result reached
    rw [mem_support_bind_iff] at reached
    obtain ⟨current,called,continued⟩ := reached
    exact (RegistrationNativeIdentityCensorForwardScope.program selected placeholder message (next current.1) current.2 (prior.2 current called)).2 result continued

private theorem forward_stem_bind {X Y : Type} (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old (X × Mode)) (next : X → OracleComp SourceSpec Y)
    (prior : ForwardStem selected message inputs continued) :
    ForwardStem selected message inputs (fun answer => continued answer >>= fun current =>
      (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2) := by
  obtain ⟨rest,body,safe⟩ := prior
  refine ⟨fun answer => rest answer >>= fun current =>
    (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2, ?_, ?_⟩
  · simpa only [bind_assoc] using congrArg (fun code => code >>= fun current =>
      (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (next current.1)).run current.2) body
  · intro answer
    exact forward_tail_bind selected placeholder message (rest answer) next (safe answer)

theorem program_forward_stem (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp SourceSpec A) (mode : Mode) (prior : Ready mode)
    (before : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (A × Mode))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    ForwardStem selected message after.2.hash.2 continued := by
  induction work using OracleComp.inductionOn generalizing mode before message continued after with
  | pure value =>
    change (Cut.selected message continued, after) ∈ support (pure (Cut.returned (value, mode), before)) at reached
    obtain impossible := eq_of_mem_support_pure _ reached
    cases impossible
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      RegistrationNativeIdentityTemplateSelectionCut.Original.bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, following⟩ := reached
    have shape := query_stem joint selected placeholder request mode prior before journal middle called
    rcases middle with ⟨cut, state⟩
    cases cut with
    | returned current =>
      exact ih current.1 current.2 shape.1 state shape.2 message continued after following
    | selected current body =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at following
      cases following
      exact forward_stem_bind selected placeholder message _ body next
        (query_forward_stem joint selected placeholder request mode prior before journal message body after called)


end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.physical_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.physical_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.source_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.source_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_stem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_stem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_stem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_stem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_fresh_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_fresh_scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_fresh_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_fresh_scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_guarded_stem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_guarded_stem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_guarded_stem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_guarded_stem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.before_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.before_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_forward_stem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.query_forward_stem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_forward_stem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope.program_forward_stem
