-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch

/-! The finite literal-address list used by the known-input tester is extracted from the actual Family observation history. Its coverage is an operational invariant of the actual ideal service, not an input cache-size or hidden-address assumption. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacBlock HmacSha512 HmacOracle)
open RegistrationNativeRelatedFamily (State Observation History Spec input)
variable {Value : Type}

def addresses (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (history : History) : List Pqxdh.Bytes := history.filterMap fun observation =>
  match observation with
  | .derive message _ => input joint dh seed scalar message
  | _ => none

def Covers (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) (state : State) : Prop :=
  ∀ bytes, state.cache bytes ≠ none → bytes ∈ addresses joint dh seed scalar state.history

set_option maxRecDepth 2048 in
/-- Actual protected extraction can only add its one queried literal address to the cache domain. -/
theorem extract_domain (hmac : HmacSha512) (target : Option DhOutput) (bytes : Pqxdh.Bytes)
    (before : HmacOracle.QueryCache) (result : HmacBlock × HmacOracle.QueryCache)
    (supported : result ∈ support ((RegistrationNativeRelatedFamily.protectedExtract hmac target bytes).run before))
    (key : Pqxdh.Bytes) (cached : result.2 key ≠ none) : key = bytes ∨ before key ≠ none := by
  by_cases same : key = bytes
  · exact Or.inl same
  · right
    by_cases inside : RegistrationNativeRelatedFamily.Protected target bytes
    · cases found : before bytes with
      | none =>
          rw [RegistrationNativeRelatedFamily.protected_miss hmac target bytes before inside found] at supported
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨prk, _sampled, returned⟩ := supported
          cases returned
          rwa [OracleSpec.QueryCache.cacheQuery_of_ne _ _ same] at cached
      | some prk =>
          rw [RegistrationNativeRelatedFamily.protected_hit hmac target bytes before prk inside found] at supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact cached
    · simp only [RegistrationNativeRelatedFamily.protectedExtract, ite_eq_right inside,
        RegistrationNativeRelatedFamily.actualExtract, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rwa [OracleSpec.QueryCache.cacheQuery_of_ne _ _ same] at cached

/-- Empty actual startup has no cached literal addresses. -/
theorem empty (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    Covers joint dh seed scalar RegistrationNativeRelatedFamily.empty := by
  intro bytes cached
  exact (cached rfl).elim

/-- The literal address list grows only on an actual realized derive observation. -/
theorem append_derive (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (history : History) (message : RegistrationNativeRelatedFamily.Message) (reply : Option HmacBlock) :
    addresses joint dh seed scalar (history ++ [.derive message reply]) =
      addresses joint dh seed scalar history ++ (input joint dh seed scalar message).toList := by
  simp only [addresses, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases input joint dh seed scalar message <;> rfl

/-- Every actual ideal Family query keeps its cache covered by its own actual observation history. -/
theorem query_covers (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : Spec.Domain) (before : State)
    (result : Spec.Range query × State)
    (valid : Covers joint dh seed scalar before)
    (supported : result ∈ support ((RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar query).run before)) :
    Covers joint dh seed scalar result.2 := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨value, _sampled, returned⟩ := supported
      cases returned
      exact valid
  | inr query => cases query with
    | sign message =>
        simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run,
          support_pure, Set.mem_singleton_iff] at supported
        cases supported
        simpa only [Covers, addresses, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil] using valid
    | publicHmac key message =>
        simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run,
          support_pure, Set.mem_singleton_iff] at supported
        cases supported
        simpa only [Covers, addresses, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil] using valid
    | derive message =>
        simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl, StateT.run] at supported
        cases realized : input joint dh seed scalar message with
        | none =>
            rw [realized] at supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            cases supported
            intro key cached
            rw [append_derive, realized, Option.toList_none, List.append_nil]
            exact valid key cached
        | some bytes =>
            rw [realized] at supported
            simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
            obtain ⟨derived, reached, returned⟩ := supported
            cases returned
            intro key cached
            rw [append_derive, realized, Option.toList_some]
            rcases extract_domain hmac _ bytes before.cache derived reached key cached with same | earlier
            · simp only [same, List.mem_append, List.mem_singleton, or_true]
            · exact List.mem_append_left _ (valid key earlier)

/-- Every adaptive actual Family execution derives finite address coverage from its literal reached history. -/
theorem program_covers (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp Spec Value) (before : State)
    (result : Value × State) (valid : Covers joint dh seed scalar before)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) work).run before)) :
    Covers joint dh seed scalar result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (Covers joint dh seed scalar)
    (fun query state holds next reached => query_covers hmac joint dh seed scalar query state next holds reached)
    work before valid result supported

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.extract_domain' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.extract_domain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.append_derive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.append_derive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.query_covers' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.query_covers
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.program_covers' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCache.program_covers
