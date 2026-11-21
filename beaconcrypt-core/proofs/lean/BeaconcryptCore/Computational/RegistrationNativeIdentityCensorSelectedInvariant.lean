-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource
import BeaconcryptCore.Computational.RegistrationOracleStateSupport
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant
open RegistrationNativeIdentityCensorSource (State implementation censored)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhDynamicIdentityPool (SourceState)
variable {A : Type}

private theorem protocol_row (joint : PqxdhJointIdentity.Primitives)
    (selected : Nat) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (before : SourceState)
    (result : PqxdhJointPhase1Reports.ProtocolSpec.Range query × SourceState)
    (found : before.seeds[selected]? = some seed)
    (supported : result ∈ support ((RegistrationNativeIdentityMainSource.implementation joint query).run before)) :
    result.2.seeds[selected]? = some seed := by
  cases query with
  | inr report =>
    simp only [RegistrationNativeIdentityMainSource.implementation] at supported
    cases supported
    exact found
  | inl query => cases query with
    | inl coin =>
      simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
        PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, _sampled, literal⟩ := supported
      simp only [mem_support_pure_iff] at literal
      cases literal
      exact found
    | inr query => cases query with
      | create =>
        change result ∈ support ((PqxdhDynamicIdentityPool.lazyImpl joint (.inr .create)).run before) at supported
        rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at supported
        obtain ⟨generated, _sampled, rfl⟩ := supported
        change (before.seeds ++ [generated])[selected]? = some seed
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
        exact found
      | service handle request | reveal handle =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        exact found

private theorem row_source_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : RegistrationNativeIdentityCensorOperational.Spec.Domain)
    (before : State) (found : before.pool.seeds[selected]? = some seed)
    (result : RegistrationNativeIdentityCensorOperational.Spec.Range query × State)
    (supported : result ∈ support ((implementation joint selected query).run before)) :
    result.2.pool.seeds[selected]? = some seed := by
  rcases query with (((request | message) | inspected) | input) | marker
  · simp only [implementation, RegistrationNativeIdentityCensorSource.protocol, StateT.run, support_map] at supported
    obtain ⟨returned,called,rfl⟩ := supported
    exact protocol_row joint selected seed request before.pool returned found called
  · simp only [implementation, RegistrationNativeIdentityCensorSource.select, StateT.run] at supported
    split at supported <;> obtain rfl := eq_of_mem_support_pure _ supported <;> exact found
  · simp only [implementation, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact found
  · simp only [implementation, RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
    obtain ⟨returned,_called,rfl⟩ := supported
    exact found
  · cases marker with
    | omitted handle message =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.omitted, StateT.run, support_map] at supported
      obtain ⟨returned,called,rfl⟩ := supported
      exact protocol_row joint selected seed (.inl (.inr (.service handle (.sign message)))) before.pool returned found called
    | template handle message leading trailing =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.template,
        RegistrationNativeIdentityCensorSource.physical, StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨returned,_called,rfl⟩ := supported
      exact found

/-- The genuine reserved row is immutable before and after selection, in both private source interpretations. -/
theorem row_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : RegistrationNativeIdentityCensorOperational.Spec.Domain)
    (before : State) (found : before.pool.seeds[selected]? = some seed)
    (result : RegistrationNativeIdentityCensorOperational.Spec.Range query × State)
    (supported : result ∈ support (((if masked then censored joint selected placeholder else implementation joint selected) query).run before)) :
    result.2.pool.seeds[selected]? = some seed := by
  cases masked with
  | false => exact row_source_query joint selected seed query before found result supported
  | true =>
      cases query with
      | inl query => exact row_source_query joint selected seed (.inl query) before found result supported
      | inr marker => cases marker with
        | template handle message leading trailing =>
          exact row_source_query joint selected seed (.inr (.template handle message leading trailing)) before found result supported
        | omitted handle message =>
          change result ∈ support (do
            let returned ← (RegistrationNativeIdentityCensorSource.omitted joint selected handle message).run before
            pure (some placeholder,returned.2)) at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨returned,called,literal⟩ := supported
          obtain rfl := eq_of_mem_support_pure _ literal
          exact row_source_query joint selected seed (.inr (.omitted handle message)) before found returned called

/-- Arbitrary adaptive private work keeps the same genuine row without requiring that a target has been selected. -/
theorem row_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (seed : PqxdhJointIdentity.IdentitySeed) (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A)
    (before : State) (found : before.pool.seeds[selected]? = some seed) (result : A × State)
    (supported : result ∈ support ((simulateQ (if masked then censored joint selected placeholder else implementation joint selected) work).run before)) :
    result.2.pool.seeds[selected]? = some seed := by
  apply PqxdhRecordLiftFlat.support_keep_oracle _ (fun current => current.pool.seeds[selected]? = some seed) _ work before found result supported
  intro query current present returned called
  exact row_query joint selected placeholder masked seed query current present returned called

def PrivateHeld (selected : Nat) (target : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed) (before : State) : Prop :=
  before.target = some target ∧ before.pool.seeds[selected]? = some seed

/-- Every actual private source leaf retains a preexisting selected message and genuine selected row, including later creations and physical hash/template updates. -/
theorem source_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (target : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : RegistrationNativeIdentityCensorOperational.Spec.Domain)
    (before : State) (prior : PrivateHeld selected target seed before)
    (result : RegistrationNativeIdentityCensorOperational.Spec.Range query × State)
    (supported : result ∈ support ((implementation joint selected query).run before)) :
    PrivateHeld selected target seed result.2 := by
  cases query with
  | inl query => cases query with
    | inl query => cases query with
      | inl query => cases query with
        | inl query =>
          simp only [implementation, RegistrationNativeIdentityCensorSource.protocol, StateT.run, support_map] at supported
          obtain ⟨returned, called, rfl⟩ := supported
          exact ⟨prior.1, protocol_row joint selected seed query before.pool returned prior.2 called⟩
        | inr message =>
          simp only [implementation, RegistrationNativeIdentityCensorSource.select, StateT.run, prior.1,
            reduceCtorEq, false_and, ite_false, mem_support_pure_iff] at supported
          cases supported
          exact prior
      | inr inspected =>
        simp only [implementation, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact prior
    | inr input =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
      obtain ⟨returned, _called, rfl⟩ := supported
      exact prior
  | inr marker => cases marker with
    | omitted handle message =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.omitted, StateT.run, support_map] at supported
      obtain ⟨returned, called, rfl⟩ := supported
      exact ⟨prior.1, protocol_row joint selected seed (.inl (.inr (.service handle (.sign message)))) before.pool returned prior.2 called⟩
    | template handle message leading trailing =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.template,
        RegistrationNativeIdentityCensorSource.physical, StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨returned, _called, rfl⟩ := supported
      exact prior

/-- Replacing only omitted replies by the known placeholder preserves that same selected private target and source row. -/
theorem censored_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (target : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : RegistrationNativeIdentityCensorOperational.Spec.Domain)
    (before : State) (prior : PrivateHeld selected target seed before)
    (result : RegistrationNativeIdentityCensorOperational.Spec.Range query × State)
    (supported : result ∈ support ((censored joint selected placeholder query).run before)) :
    PrivateHeld selected target seed result.2 := by
  cases query with
  | inl query => exact source_query joint selected target seed (.inl query) before prior result supported
  | inr marker => cases marker with
    | template handle message leading trailing =>
      exact source_query joint selected target seed (.inr (.template handle message leading trailing)) before prior result supported
    | omitted handle message =>
      change result ∈ support (do
        let returned ← (RegistrationNativeIdentityCensorSource.omitted joint selected handle message).run before
        pure (some placeholder, returned.2)) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨returned, called, literal⟩ := supported
      obtain rfl := eq_of_mem_support_pure _ literal
      exact source_query joint selected target seed (.inr (.omitted handle message)) before prior returned called

/-- Every complete continued private marker tree retains the preexisting target and selected genuine row in either private interpretation. -/
theorem private_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (target : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A) (before : State)
    (prior : PrivateHeld selected target seed before) (result : A × State)
    (supported : result ∈ support ((simulateQ (if masked then censored joint selected placeholder else implementation joint selected) work).run before)) :
    PrivateHeld selected target seed result.2 := by
  apply PqxdhRecordLiftFlat.support_keep_oracle _ (PrivateHeld selected target seed) _ work before prior result supported
  intro query current held returned called
  cases masked with
  | false => exact source_query joint selected target seed query current held returned called
  | true => exact censored_query joint selected placeholder target seed query current held returned called

private theorem simulated_support {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec A) (value : A)
    (reached : value ∈ support (simulateQ impl work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure returned =>
      rw [simulateQ_pure] at reached
      obtain rfl := eq_of_mem_support_pure _ reached
      simp only [support_pure, Set.mem_singleton_iff]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
    obtain ⟨reply, _queried, continued⟩ := reached
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply continued⟩

private theorem lift_state {B : Type} (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support ((StateT.lift work : StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) B).run mode)) :
    result.2 = mode := by
  change result ∈ support (do let reply ← work; pure (reply, mode)) at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl

private theorem constant_state {I : Type} {spec : OracleSpec I} {B : Type} (work : OracleComp spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support (do let reply ← work; pure (reply, mode))) : result.2 = mode := by
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl


private theorem signing_target (selected handle : Nat) (message target : Pqxdh.Bytes) (mode : Mode)
    (held : mode.target = some target)
    (result : Option PqxdhEd25519EufCma.Ed25519Signature × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)) :
    result.2.target = some target := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨prepared, queried, rest⟩ := reached
  have original := simulated_support _ _ _ queried
  rw [RegistrationNativeIdentityCensorCompiler.prepare_selected selected handle message target mode held] at original
  obtain rfl := eq_of_mem_support_pure _ original
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at rest
  split at rest <;> split at rest
  all_goals rw [lift_state _ _ _ rest]
  all_goals exact held

/-- Actual operational source leaves preserve the previously selected public target through all later hashes and signing calls. -/
theorem mode_query (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (target : Pqxdh.Bytes)
    (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (mode : Mode)
    (held : mode.target = some target)
    (result : RegistrationNativePlatformIdentityCtxCompiler.Spec.Range request × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)) :
    result.2.target = some target := by
  rcases request with ((coin | request) | report) | bytes
  · have original := simulated_support _ _ _ reached
    exact (congrArg Mode.target (constant_state _ _ _ original)).trans held
  · cases request with
    | create | reveal handle =>
      have original := simulated_support _ _ _ reached
      exact (congrArg Mode.target (constant_state _ _ _ original)).trans held
    | service handle request => cases request with
      | staticDh peer =>
        have original := simulated_support _ _ _ reached
        exact (congrArg Mode.target (constant_state _ _ _ original)).trans held
      | sign message => exact signing_target selected handle message target mode held result reached
  · have original := simulated_support _ _ _ reached
    exact (congrArg Mode.target (constant_state _ _ _ original)).trans held
  · change result ∈ support (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => simulateQ RegistrationNativeIdentityCensorOperational.embed
          ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode)
      | none => do
          let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query
            (.inr (.template selected mode.target (RegistrationNativeIdentityCensorOperational.parts bytes).1
              (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp RegistrationNativeIdentityCensorOperational.Spec _)
          pure (reply, mode)) at reached
    split at reached
    · have original := simulated_support _ _ _ reached
      change result ∈ support (do
        let reply ← (RegistrationNativeIdentityCensorCompiler.Spec.query
          (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)) : OracleComp RegistrationNativeIdentityCensorCompiler.Spec _)
        pure (reply, {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
          | none => mode.knownInputs
          | some input => mode.knownInputs ++ [input]})) at original
      have same := constant_state _ _ result original
      have projected := congrArg Mode.target same
      exact projected.trans held
    · exact (congrArg Mode.target (constant_state _ _ _ reached)).trans held


/-- Arbitrary adaptive source work cannot replace the preexisting public target, even while later callbacks change active routing and known inputs. -/
theorem mode_program (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (target : Pqxdh.Bytes) (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A)
    (mode : Mode) (held : mode.target = some target) (result : A × Mode)
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)) :
    result.2.target = some target := by
  induction work using OracleComp.inductionOn generalizing mode result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact held
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1 middle.2 (mode_query selected placeholder target request mode held middle called) result continued

/-- The actual operational proxy lowered through either private source retains the same already selected public/private target and genuine row through the whole continued execution. -/
theorem lower_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (target : Pqxdh.Bytes)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A) (mode : Mode) (before : State)
    (modeHeld : mode.target = some target) (privateHeld : PrivateHeld selected target seed before)
    (result : (A × Mode) × State)
    (reached : result ∈ support ((simulateQ (if masked then censored joint selected placeholder else implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    result.1.2.target = some target ∧ result.2.target = some target ∧ result.2.pool.seeds[selected]? = some seed := by
  have operational : result.1 ∈ support
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode) := by
    apply OracleComp.support_simulateQ_run'_subset
      (if masked then censored joint selected placeholder else implementation joint selected) _ before
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have privateAfter := private_program joint selected placeholder masked target seed
    ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)
    before privateHeld result reached
  exact ⟨mode_program selected placeholder target work mode modeHeld result.1 operational, privateAfter.1, privateAfter.2⟩
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.source_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.censored_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.censored_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.private_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.private_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.mode_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.mode_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.mode_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.mode_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.lower_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.row_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.row_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.row_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant.row_program
