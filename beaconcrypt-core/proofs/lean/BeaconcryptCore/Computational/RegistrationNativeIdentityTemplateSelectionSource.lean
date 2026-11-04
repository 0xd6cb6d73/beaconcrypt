-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCacheProvenance
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorForwardScope

/-! Actual supported first-selector prefixes retain the genuine successful-reply history, the absent source target and the provenance of the warm physical cache. These are source invariants, derived before applying the canonical first-omission continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource
open PqxdhJointIdentity (Primitives)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativeIdentityCensorPolicySource (handler)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityTemplatePublicPrefix (Allowed)
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old Cut stop)
variable {A : Type}

structure Ready (selected : Nat) (before : Policy × State) : Prop where
  aligned : RegistrationNativeIdentityCensorPolicySource.Aligned selected before
  missing : before.2.target = none
  known : RegistrationNativeIdentityCensorCacheProvenance.Known before.2

private theorem fixed (request : Old.Domain) (allowed : Allowed request) (reply : Old.Range request)
    (target : Option Pqxdh.Bytes) :
    RegistrationNativeIdentityCensorTargetSync.targetAfter request reply target = target := by
  rcases request with (((protocol | selection) | scanned) | described) | marker
  · rfl
  · exact False.elim allowed
  · rfl
  · rfl
  · exact False.elim allowed

private theorem step (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : Old.Domain) (allowed : Allowed request) (before : Policy × State) (prior : Ready selected before)
    (result : Old.Range request × (Policy × State))
    (reached : result ∈ support ((handler joint selected placeholder request).run before)) :
    Ready selected result.2 := by
  simp only [handler, StateT.run, support_map] at reached
  obtain ⟨actual, called, rfl⟩ := reached
  have marker : RegistrationNativeIdentityCensorPolicySource.MarkerReady before.2 request := by
    cases request with
    | inl request => trivial
    | inr marker => exact False.elim allowed
  refine ⟨RegistrationNativeIdentityCensorPolicySource.step joint selected placeholder request before prior.aligned marker actual called, ?_,
    RegistrationNativeIdentityCensorCacheProvenance.query joint selected placeholder request before.2 prior.known actual called⟩
  exact (RegistrationNativeIdentityCensorTargetSync.censored_step joint selected placeholder request before.2 actual called).trans
    ((fixed request allowed actual.1 before.2.target).trans prior.missing)

/-- Every actual source outcome of a public prefix retains the successful-reply/source-history relation, absent target and complete warm-cache provenance. -/
theorem program (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Old A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : Policy × State) (prior : Ready selected before)
    (result : A × (Policy × State))
    (reached : result ∈ support ((simulateQ (handler joint selected placeholder) work).run before)) :
    Ready selected result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1 (later middle.1) middle.2 (step joint selected placeholder request first before prior middle called) result continued

/-- The actual stopped lowering discharges public-prefix scope internally, including an armed guessed bundle. No successful source signing or selected-row premise is used. -/
theorem cut (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec A) (mode : Mode)
    (control : RegistrationNativeIdentityTemplateSelectionPrefixScope.Ready mode)
    (before : Policy × State) (prior : Ready selected before)
    (result : Cut (A × Mode) × (Policy × State))
    (reached : result ∈ support ((simulateQ (handler joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    Ready selected result.2 :=
  program joint selected placeholder _ (RegistrationNativeIdentityTemplateSelectionPrefixScope.program selected placeholder work mode control).1 before prior result reached

/-- Literal source initialization derives all prefix invariants from its actual warm Server pin cache and original source journal. -/
theorem initialized {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (selected identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (reached : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Ready selected (({} : Policy), (⟨PqxdhDynamicIdentityPool.initialState,
      (RegistrationNativeWorldCache.cache initial.state, [PqxdhRefinement.absBytes initial.credential.publicKey]), none, none, none⟩ : State)) := by
  exact ⟨RegistrationNativeIdentityCensorPolicySource.initialized selected _, rfl,
    RegistrationNativeIdentityCensorCacheProvenance.initialized setup ensureInit identityIndex serverKeyId initial reached⟩


private theorem observe_fresh (selected : Nat) (wanted : Pqxdh.Bytes) (request : Old.Domain)
    (allowed : RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted request)
    (reply : Old.Range request) (before : Policy) (fresh : wanted ∉ before.forwarded) :
    wanted ∉ (RegistrationNativeIdentityCensorPolicySource.observe selected request reply before).forwarded := by
  rcases request with (((protocol | selection) | scanned) | described) | marker
  · rcases protocol with (coin | query) | report
    · simpa [RegistrationNativeIdentityCensorPolicySource.observe,
        RegistrationNativeIdentityCensorPolicySource.update, RegistrationNativeIdentityCensorPolicySource.newMessage] using fresh
    · cases query with
      | create | reveal handle =>
          simpa [RegistrationNativeIdentityCensorPolicySource.observe,
            RegistrationNativeIdentityCensorPolicySource.update, RegistrationNativeIdentityCensorPolicySource.newMessage] using fresh
      | service handle query => cases query with
        | staticDh peer =>
            simpa [RegistrationNativeIdentityCensorPolicySource.observe,
              RegistrationNativeIdentityCensorPolicySource.update, RegistrationNativeIdentityCensorPolicySource.newMessage] using fresh
        | sign message =>
          change handle = selected → message ≠ wanted at allowed
          by_cases same : handle = selected
          · cases reply with
            | none =>
              simpa [RegistrationNativeIdentityCensorPolicySource.observe,
                RegistrationNativeIdentityCensorPolicySource.update,
                RegistrationNativeIdentityCensorPolicySource.newMessage, same] using fresh
            | some signature =>
              simpa [RegistrationNativeIdentityCensorPolicySource.observe,
                RegistrationNativeIdentityCensorPolicySource.update,
                RegistrationNativeIdentityCensorPolicySource.newMessage, same] using
                  (show wanted ∉ before.forwarded ∧ wanted ≠ message from ⟨fresh, (allowed same).symm⟩)
          · simpa [RegistrationNativeIdentityCensorPolicySource.observe,
              RegistrationNativeIdentityCensorPolicySource.update,
              RegistrationNativeIdentityCensorPolicySource.newMessage, same] using fresh
    · simpa [RegistrationNativeIdentityCensorPolicySource.observe,
        RegistrationNativeIdentityCensorPolicySource.update, RegistrationNativeIdentityCensorPolicySource.newMessage] using fresh
  · exact fresh
  · exact fresh
  · exact fresh
  · exact fresh

private theorem forwarded_program (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (work : OracleComp Old A)
    (allowed : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected wanted))
    (before : Policy × State) (fresh : wanted ∉ before.1.forwarded)
    (result : A × (Policy × State))
    (reached : result ∈ support ((simulateQ (handler joint selected placeholder) work).run before)) :
    wanted ∉ result.2.1.forwarded := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact fresh
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    apply ih middle.1 (later middle.1) middle.2 _ result continued
    simp only [handler, StateT.run, support_map] at called
    obtain ⟨actual, _called, rfl⟩ := called
    exact observe_fresh selected wanted request first actual.1 before.1 fresh


/-- Actual armed first-selection prefixes preserve the original fresh one-time message in the genuine source history. The exclusion is derived from the stopped controller, rather than supplied as a signing policy. -/
theorem fresh_cut (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted = true)
    (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec A) (mode : Mode)
    (control : RegistrationNativeIdentityTemplateSelectionPrefixScope.Ready mode) (arming : mode.armed = true)
    (before : Policy × State) (prior : Ready selected before)
    (fresh : wanted ∉ RegistrationNativeIdentityCensorPolicySource.messages selected before.2.pool)
    (result : Cut (A × Mode) × (Policy × State))
    (reached : result ∈ support ((simulateQ (handler joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    wanted ∉ RegistrationNativeIdentityCensorPolicySource.messages selected result.2.2.pool := by
  have initialNone : before.1.target = none := prior.aligned.1.trans prior.missing
  have publicFresh : wanted ∉ before.1.forwarded := by
    simpa only [prior.aligned.2 initialNone] using fresh
  have excluded :=  (RegistrationNativeIdentityTemplateSelectionPrefixScope.program_fresh_scope selected placeholder wanted role work mode control arming).1
  have afterFresh := forwarded_program joint selected placeholder wanted _ excluded before publicFresh result reached
  have afterReady := cut joint selected placeholder work mode control before prior result reached
  have afterNone : result.2.1.target = none := afterReady.aligned.1.trans afterReady.missing
  simpa only [afterReady.aligned.2 afterNone] using afterFresh


/-- The actual supported first selector has every local installation receipt: the original fresh message, the genuine selected row, a positive executable choice, complete cache provenance and a source-derived guarded continuation. -/
theorem first_cut (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted = true)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec A) (mode : Mode)
    (control : RegistrationNativeIdentityTemplateSelectionPrefixScope.Ready mode) (arming : mode.armed = true)
    (before : Policy × State) (prior : Ready selected before)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before.2)
    (fresh : wanted ∉ RegistrationNativeIdentityCensorPolicySource.messages selected before.2.pool)
    (found : before.2.pool.seeds[selected]? = some seed)
    (continued : Bool → OracleComp Old (A × Mode)) (after : Policy × State)
    (reached : (Cut.selected wanted continued, after) ∈ support ((simulateQ (handler joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    Ready selected after ∧
      wanted ∉ RegistrationNativeIdentityCensorPolicySource.messages selected after.2.pool ∧
      after.2.pool.seeds[selected]? = some seed ∧
      RegistrationNativeIdentityCensorPolicySource.choose wanted after.1 = (true, {after.1 with target := some wanted}) ∧
      RegistrationNativeIdentityTemplateSelectionPrefixScope.GuardedStem selected wanted after.2.hash.2 continued := by
  have afterReady := cut joint selected placeholder work mode control before prior _ reached
  have afterFresh := fresh_cut joint selected placeholder wanted role work mode control arming before prior fresh _ reached
  have raw : (Cut.selected wanted continued, after.2) ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (stop ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before.2) := by
    rw [← RegistrationNativeIdentityCensorPolicySource.program_erasure joint selected placeholder _ before, support_map]
    exact ⟨(Cut.selected wanted continued, after), reached, rfl⟩
  have row := RegistrationNativeIdentityCensorSelectedInvariant.row_program joint selected placeholder true seed _ before.2 found _ raw
  have afterNone : after.1.target = none := afterReady.aligned.1.trans afterReady.missing
  have publicFresh : wanted ∉ after.1.forwarded := by
    intro member
    exact afterFresh ((afterReady.aligned.2 afterNone) ▸ member)
  refine ⟨afterReady, afterFresh, row, ?_, ?_⟩
  · simp [RegistrationNativeIdentityCensorPolicySource.choose, afterNone, publicFresh]
  · exact RegistrationNativeIdentityTemplateSelectionPrefixScope.program_guarded_stem joint selected placeholder work mode control before journal wanted continued after reached

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.fresh_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.fresh_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.first_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionSource.first_cut
