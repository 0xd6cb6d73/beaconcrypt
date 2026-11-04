-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxNoReveal
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistory
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore

/-! Every complete actual CTX source result retains a reveal-free transcript when its free request tree has no indexed reveal. Replaying that literal transcript yields empty family reveals for any family size. All reply, private row, physical cache/journal and client state coordinates are retained in the supported result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
open RegistrationNativePlatformIdentityCtxNoReveal (Allowed)
open RegistrationNativeIdentityMainNoRevealCore (DynamicAllowed)
open PqxdhDynamicIdentityPool (SourceState DynamicSpec Observation)
variable {A : Type}

def TranscriptAllowed (before : SourceState) : Prop := ∀ observation ∈ before.transcript, DynamicAllowed observation.1

private theorem record_allowed (query : DynamicSpec.Domain) (reply : DynamicSpec.Range query) (before : SourceState)
    (prior : TranscriptAllowed before) (allowed : DynamicAllowed query) :
    TranscriptAllowed (PqxdhDynamicIdentityPool.record query reply before) := by
  intro observation member
  simp only [PqxdhDynamicIdentityPool.record, List.mem_append, List.mem_singleton] at member
  rcases member with previous | rfl
  · exact prior observation previous
  · exact allowed

private theorem pool_query (joint : PqxdhJointIdentity.Primitives) (query : DynamicSpec.Domain)
    (before : SourceState) (result : DynamicSpec.Range query × SourceState)
    (prior : TranscriptAllowed before) (allowed : DynamicAllowed query)
    (reached : result ∈ support ((PqxdhDynamicIdentityPool.lazyImpl joint query).run before)) : TranscriptAllowed result.2 := by
  cases query with
  | inl coin =>
    simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_bind_iff] at reached
    obtain ⟨answer, _sampled, literal⟩ := reached
    simp only [mem_support_pure_iff] at literal
    cases literal
    exact record_allowed (.inl coin) answer before prior allowed
  | inr query => cases query with
    | create =>
      rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at reached
      obtain ⟨seed, _sampled, rfl⟩ := reached
      exact record_allowed (.inr .create) _ {before with seeds := before.seeds ++ [seed]} prior allowed
    | reveal handle => cases allowed
    | service handle request =>
      simp only [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_pure_iff] at reached
      cases reached
      exact record_allowed (.inr (.service handle request)) _ before prior allowed

private theorem protocol_allowed (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (allowed : Allowed (.inl query)) :
    RegistrationNativeIdentityMainNoRevealCore.Allowed query := by
  cases query with
  | inr report => trivial
  | inl query => cases query with
    | inl coin => trivial
    | inr query => cases query with
      | create | service handle request => trivial
      | reveal handle => exact allowed trivial

private theorem source_query (joint : PqxdhJointIdentity.Primitives) (query : Spec.Domain)
    (before : State) (result : Spec.Range query × State)
    (prior : TranscriptAllowed before.1) (allowed : Allowed query)
    (reached : result ∈ support ((implementation joint query).run before)) : TranscriptAllowed result.2.1 := by
  cases query with
  | inr bytes =>
    simp only [implementation, StateT.run, support_map] at reached
    obtain ⟨inner, _called, rfl⟩ := reached
    exact prior
  | inl query =>
    have permitted := protocol_allowed query allowed
    simp only [implementation, StateT.run, support_map] at reached
    obtain ⟨inner, called, rfl⟩ := reached
    cases query with
    | inr report =>
      simp only [RegistrationNativeIdentityMainSource.implementation] at called
      cases called
      exact prior
    | inl query =>
      exact pool_query joint query before.1 inner prior permitted called

/-- The literal source interpreter preserves the no-reveal transcript for every adaptive query and every reached reply. -/
theorem program_allowed (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : State) (prior : TranscriptAllowed before.1)
    (result : A × State) (reached : result ∈ support ((simulateQ (implementation joint) work).run before)) :
    TranscriptAllowed result.2.1 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1 (allowed.2 middle.1) middle.2
      (source_query joint query before middle prior allowed.1 called) result continued

private theorem history_update (count : Nat) (query : DynamicSpec.Domain) (reply : DynamicSpec.Range query)
    (before : PqxdhJointIdentityFreshness.GlobalState count) (allowed : DynamicAllowed query) :
    (PqxdhDynamicIdentityRouting.historyUpdate count query reply before).reveals = before.reveals := by
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | create => rfl
    | reveal handle => cases allowed
    | service handle request =>
      simp only [PqxdhDynamicIdentityRouting.historyUpdate]
      split <;> cases reply <;> simp [PqxdhJointIdentityEvents.publicUpdate]

private theorem fold_reveals (count : Nat) (transcript : List Observation)
    (allowed : ∀ observation ∈ transcript, DynamicAllowed observation.1)
    (before : PqxdhJointIdentityFreshness.GlobalState count) :
    (transcript.foldl (fun prior observation => PqxdhDynamicIdentityRouting.historyUpdate count observation.1 observation.2 prior) before).reveals = before.reveals := by
  induction transcript generalizing before with
  | nil => rfl
  | cons observation rest ih =>
    rw [List.foldl_cons, ih (fun current member => allowed current (List.mem_cons_of_mem observation member)),
      history_update count observation.1 observation.2 before (allowed observation (List.mem_cons_self))]

/-- Replaying the actual raw source transcript, rather than a replacement public log, derives empty reveals for every family size. -/
theorem replay_reveals (count : Nat) (before : SourceState) (allowed : TranscriptAllowed before) :
    (RegistrationNativeIdentityHistory.replay count before.transcript).reveals = [] := by
  rw [RegistrationNativeIdentityHistory.replay, fold_reveals count before.transcript allowed]
  rfl

/-- Any actual no-reveal CTX free client initialized with the genuine empty source pool has the required same-run replay receipt beside its arbitrary warm physical cache. -/
theorem initialized_reveals (joint : PqxdhJointIdentity.Primitives) (count : Nat) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy Allowed) (physical : RegistrationNativePlatformCtxBackend.State)
    (result : A × State)
    (reached : result ∈ support ((simulateQ (implementation joint) work).run (PqxdhDynamicIdentityPool.initialState, physical))) :
    (RegistrationNativeIdentityHistory.replay count result.2.1.transcript).reveals = [] := by
  apply replay_reveals count result.2.1
  exact program_allowed joint work allowed (PqxdhDynamicIdentityPool.initialState, physical)
    (fun _ member => False.elim (List.not_mem_nil member)) result reached

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay.program_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay.program_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay.replay_reveals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay.replay_reveals

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay.initialized_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReplay.initialized_reveals
