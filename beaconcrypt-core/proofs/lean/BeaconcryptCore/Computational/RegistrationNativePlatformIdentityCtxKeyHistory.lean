-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame
import BeaconcryptCore.Computational.RegistrationNativeEdKeyPolicy
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
open PqxdhDynamicIdentityPool (SourceState DynamicSpec record)
open RegistrationNativeEdKeyPolicy (Allowed)
open PqxdhEd25519EufCma (X25519PublicKey)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (messages poolMessages)
variable {A : Type}

def Legal (identity : Nat) (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) : Spec.Domain → Prop
  | .inl (.inl (.inr (.service handle (.sign message)))) => handle = identity → Allowed prekey pq message
  | _ => True
private def PoolLegal (identity : Nat) (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) : DynamicSpec.Domain → Prop
  | .inr (.service handle (.sign message)) => handle = identity → Allowed prekey pq message
  | _ => True

def Extends (identity : Nat) (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) (before after : State) : Prop :=
  ∀ message ∈ messages identity after, message ∈ messages identity before ∨ Allowed prekey pq message

private theorem record_messages (identity : Nat) (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)
    (query : DynamicSpec.Domain) (reply : DynamicSpec.Range query) (before : SourceState)
    (allowed : PoolLegal identity prekey pq query) :
    ∀ message ∈ poolMessages identity (record query reply before), message ∈ poolMessages identity before ∨ Allowed prekey pq message := by
  cases query with
  | inl coin =>
    intro message member
    exact Or.inl (by simpa only [poolMessages, record, RegistrationNativeIdentityHistory.history,
      List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
      List.filterMap_nil, List.append_nil] using member)
  | inr query => cases query with
    | create | reveal handle =>
      intro message member
      exact Or.inl (by simpa only [poolMessages, record, RegistrationNativeIdentityHistory.history,
        List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
        List.filterMap_nil, List.append_nil] using member)
    | service handle request =>
      cases request with
      | staticDh peer =>
        intro message member
        cases reply <;> by_cases same : handle = identity <;>
          exact Or.inl (by simpa only [poolMessages, record, RegistrationNativeIdentityHistory.history,
            List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
            same, ite_true, ite_false, List.filterMap_nil, List.append_nil,
            PqxdhJointIdentity.signedMessages, List.filterMap_append, List.filterMap_cons,
            PqxdhJointIdentity.requestEvent] using member)
      | sign request =>
        intro message member
        cases reply <;> by_cases same : handle = identity
        all_goals simp only [poolMessages, record, RegistrationNativeIdentityHistory.history,
          List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
          same, ite_true, ite_false, List.filterMap_nil, List.append_nil,
          PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        all_goals first
          | exact Or.inl member
          | rcases member with old | rfl
            · exact Or.inl old
            · exact Or.inr (allowed same)

/-- The actual joint source can add only an allowed message at this exact generated handle; optional replies and all physical state are retained. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (identity : Nat)
    (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) (request : Spec.Domain)
    (allowed : Legal identity prekey pq request) (before : State) (result : Spec.Range request × State)
    (supported : result ∈ support ((implementation joint request).run before)) : Extends identity prekey pq before result.2 := by
  cases request with
  | inr bytes =>
    simp only [implementation, StateT.run, support_map] at supported
    obtain ⟨returned, _called, rfl⟩ := supported
    exact fun _ member => Or.inl member
  | inl request =>
    simp only [implementation, StateT.run, support_map] at supported
    obtain ⟨returned, called, rfl⟩ := supported
    cases request with
    | inr report =>
      simp only [RegistrationNativeIdentityMainSource.implementation] at called
      cases called
      exact fun _ member => Or.inl member
    | inl request => cases request with
      | inl coin =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, mem_support_bind_iff] at called
        obtain ⟨answer, _sampled, literal⟩ := called
        simp only [mem_support_pure_iff] at literal
        cases literal
        exact record_messages identity prekey pq (.inl coin) answer before.1 trivial
      | inr request => cases request with
        | create =>
          change returned ∈ support ((PqxdhDynamicIdentityPool.lazyImpl joint (.inr .create)).run before.1) at called
          rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at called
          obtain ⟨seed, _sampled, rfl⟩ := called
          exact record_messages identity prekey pq (.inr .create) _ {before.1 with seeds := before.1.seeds ++ [seed]} trivial
        | reveal handle =>
          simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl, mem_support_pure_iff] at called
          cases called
          exact record_messages identity prekey pq (.inr (.reveal handle)) _ before.1 trivial
        | service handle request =>
          simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl, mem_support_pure_iff] at called
          cases called
          cases request <;> exact record_messages identity prekey pq _ _ before.1 allowed

/-- Full adaptive physical execution retains all earlier messages and can add only the actual permitted source key family. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (identity : Nat)
    (prekey : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy (Legal identity prekey pq)) (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ (implementation joint) work).run before)) : Extends identity prekey pq before result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact fun _ member => Or.inl member
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    intro message member
    rcases ih middle.1 (allowed.2 middle.1) middle.2 result continued message member with earlier | legal
    · exact query joint identity prekey pq request allowed.1 before middle called message earlier
    · exact Or.inr legal
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyHistory.program
