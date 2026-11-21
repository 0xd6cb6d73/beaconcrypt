-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleSigningHandle
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistory

/-! Literal source steps without a signing call at a particular handle preserve that handle's successful message history. Combined with the actual bundle's captured-handle scope, a newly signed message identifies its same-run captured owner handle; no owner/admission or desired-origin premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
open PqxdhDynamicIdentityPool (SourceState DynamicSpec record)
variable {A : Type}

def NoSignFor (identity : Nat) : Spec.Domain → Prop
  | .inl (.inl (.inr (.service handle (.sign _)))) => handle ≠ identity
  | _ => True
private def PoolAllowed (identity : Nat) : DynamicSpec.Domain → Prop
  | .inr (.service handle (.sign _)) => handle ≠ identity
  | _ => True

def poolMessages (identity : Nat) (before : SourceState) : List Pqxdh.Bytes :=
  PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history identity before.transcript)
def messages (identity : Nat) (before : State) : List Pqxdh.Bytes := poolMessages identity before.1

private theorem record_messages (identity : Nat) (query : DynamicSpec.Domain) (reply : DynamicSpec.Range query)
    (before : SourceState) (allowed : PoolAllowed identity query) :
    poolMessages identity (record query reply before) = poolMessages identity before := by
  cases query with
  | inl coin =>
      simp only [poolMessages, record, RegistrationNativeIdentityHistory.history,
        List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
        List.filterMap_nil, List.append_nil]
  | inr query => cases query with
    | create | reveal handle =>
      simp only [poolMessages, record, RegistrationNativeIdentityHistory.history,
        List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
        List.filterMap_nil, List.append_nil]
    | service handle request =>
      cases request with
      | sign message =>
        change handle ≠ identity at allowed
        cases reply <;> simp only [poolMessages, record, RegistrationNativeIdentityHistory.history,
          List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
          allowed, ite_false, List.filterMap_nil, List.append_nil]
      | staticDh peer =>
        cases reply <;> by_cases same : handle = identity <;>
          simp only [poolMessages, record, RegistrationNativeIdentityHistory.history,
            List.filterMap_append, List.filterMap_cons, RegistrationNativeIdentityHistory.entry,
            same, ite_true, ite_false, List.filterMap_nil, List.append_nil,
            PqxdhJointIdentity.signedMessages, List.filterMap_append, List.filterMap_cons,
            PqxdhJointIdentity.requestEvent]

/-- Actual primitive/source replies without a signing request for this handle cannot change its successful signing history. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (identity : Nat) (request : Spec.Domain)
    (allowed : NoSignFor identity request) (before : State) (result : Spec.Range request × State)
    (supported : result ∈ support ((implementation joint request).run before)) :
    messages identity result.2 = messages identity before := by
  cases request with
  | inr bytes =>
    simp only [implementation, StateT.run, support_map] at supported
    obtain ⟨returned, _called, rfl⟩ := supported
    rfl
  | inl request =>
    simp only [implementation, StateT.run, support_map] at supported
    obtain ⟨returned, called, rfl⟩ := supported
    cases request with
    | inr report =>
      simp only [RegistrationNativeIdentityMainSource.implementation] at called
      cases called
      rfl
    | inl request => cases request with
      | inl coin =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, mem_support_bind_iff] at called
        obtain ⟨answer, _sampled, literal⟩ := called
        simp only [mem_support_pure_iff] at literal
        cases literal
        exact record_messages identity (.inl coin) answer before.1 trivial
      | inr request => cases request with
        | create =>
          change returned ∈ support ((PqxdhDynamicIdentityPool.lazyImpl joint (.inr .create)).run before.1) at called
          rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at called
          obtain ⟨seed, _sampled, rfl⟩ := called
          exact record_messages identity (.inr .create) _ {before.1 with seeds := before.1.seeds ++ [seed]} trivial
        | reveal handle =>
          simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl, mem_support_pure_iff] at called
          cases called
          exact record_messages identity (.inr (.reveal handle)) _ before.1 trivial
        | service handle request =>
          simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl, mem_support_pure_iff] at called
          cases called
          cases request <;> exact record_messages identity _ _ before.1 allowed

/-- The actual source message history is unchanged throughout every adaptive tree with no signing leaf for that handle. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (identity : Nat) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy (NoSignFor identity)) (before : State) (result : A × State)
    (supported : result ∈ support ((simulateQ (implementation joint) work).run before)) :
    messages identity result.2 = messages identity before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact (ih middle.1 (allowed.2 middle.1) middle.2 result continued).trans
      (query joint identity request allowed.1 before middle called)

private theorem only_other (identity handle : Nat) (different : handle ≠ identity) (request : Spec.Domain)
    (scope : RegistrationNativePlatformIdentityCtxBundleSigningHandle.OnlyHandle handle request) : NoSignFor identity request := by
  rcases request with ((coin | request) | report) | bytes
  · trivial
  · cases request with
    | create | reveal handle => trivial
    | service selected request => cases request with
      | staticDh peer => trivial
      | sign message => exact fun same => different (scope.symm.trans same)
  · trivial
  · trivial

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- If the actual captured body newly signs at a handle, that handle is its actual captured owner. The source scope discharges this association even for failed writers and arbitrary primitive optional replies. -/
theorem owner (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (index : Nat) (captured : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (before : RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (result : RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityCtxMain.interpret setup.joint
      (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
        (RegistrationNativePlatformIdentityBundle.bundled setup index captured scalar writer))).run before))
    (identity : Nat) (message : Pqxdh.Bytes) (fresh : message ∉ messages identity before.2)
    (signed : message ∈ messages identity result.2.2) : captured.identity.handle = identity := by
  by_contra different
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have scope := RegistrationNativePlatformIdentityCtxBundleSigningHandle.bundled setup checks representation created index captured scalar writer before.1
  have allowed := scope.mono (only_other identity captured.identity.handle different)
  have retained := program setup.joint identity _ allowed before.2 inner reached
  exact fresh (retained ▸ signed)

end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningHistoryFrame.owner
