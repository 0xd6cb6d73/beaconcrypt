-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorForwardScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol
/-! A selected message stays fresh in the genuine public source history when the actual lowered tail contains no forwarded selected-target signing request. Canonical omitted ghost receipts are absent from this history. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh
open PqxdhJointIdentity (Primitives)
open PqxdhJointPhase1Reports (ProtocolSpec)
open PqxdhDynamicIdentityPool (SourceState)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec source)
open RegistrationNativeIdentityCensorPolicySource (messages newMessage)
variable {A : Type}

def Allowed (selected : Nat) (target : Pqxdh.Bytes) : PublicSpec.Domain → Prop
  | .inl query => RegistrationNativeIdentityCensorForwardScope.ProtocolAllowed selected target query
  | .inr _ => True

private theorem no_new (selected : Nat) (target : Pqxdh.Bytes) (query : ProtocolSpec.Domain)
    (allowed : RegistrationNativeIdentityCensorForwardScope.ProtocolAllowed selected target query)
    (answer : ProtocolSpec.Range query) : target ∉ (newMessage selected query answer).toList := by
  rcases query with (coin | query) | report
  · simp only [newMessage,Option.toList_none,List.not_mem_nil,not_false_eq_true]
  · cases query with
    | create | reveal handle => simp only [newMessage,Option.toList_none,List.not_mem_nil,not_false_eq_true]
    | service handle request =>
      cases request with
      | staticDh peer => simp only [newMessage,Option.toList_none,List.not_mem_nil,not_false_eq_true]
      | sign message =>
        by_cases same : handle = selected
        · subst handle
          have different : message ≠ target := allowed rfl
          cases answer with
          | none => simp [newMessage]
          | some signature => simpa [newMessage] using Ne.symm different
        · simp only [newMessage,same,ite_false,Option.toList_none,List.not_mem_nil,not_false_eq_true]
  · simp only [newMessage,Option.toList_none,List.not_mem_nil,not_false_eq_true]

/-- One actual genuine query cannot introduce the selected message when its literal request avoids that message. -/
theorem query (joint : Primitives) (selected : Nat) (target : Pqxdh.Bytes) (request : PublicSpec.Domain)
    (allowed : Allowed selected target request) (before : SourceState) (fresh : target ∉ messages selected before)
    (result : PublicSpec.Range request × SourceState)
    (supported : result ∈ support ((source joint request).run before)) : target ∉ messages selected result.2 := by
  cases request with
  | inl protocol =>
    have factual := RegistrationNativeIdentityCensorPolicySource.protocol_messages joint selected protocol before result supported
    rw [factual,List.mem_append]
    exact not_or.mpr ⟨fresh,no_new selected target protocol allowed result.1⟩
  | inr coin =>
    change result ∈ support ((fun answer => (answer,before)) <$> (unifSpec.query coin : ProbComp _)) at supported
    rw [support_map] at supported
    obtain ⟨answer,_sampled,rfl⟩ := supported
    exact fresh

/-- Every actual adaptive genuine source tail retains selected-message freshness, jointly with its literal full transcript and optional output. -/
theorem program (joint : Primitives) (selected : Nat) (target : Pqxdh.Bytes) (work : OracleComp PublicSpec A)
    (allowed : work.AllQueriesSatisfy (Allowed selected target)) (before : SourceState)
    (fresh : target ∉ messages selected before) (result : A × SourceState)
    (supported : result ∈ support ((simulateQ (source joint) work).run before)) : target ∉ messages selected result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact fresh
  | query_bind request next ih =>
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact ih middle.1 (later middle.1) middle.2 (query joint selected target request first before fresh middle called) result continued

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh.program
