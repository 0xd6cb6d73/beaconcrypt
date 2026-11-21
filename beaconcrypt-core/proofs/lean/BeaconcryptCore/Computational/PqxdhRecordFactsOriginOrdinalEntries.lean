-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalTrace
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach

/-! Seal dictionary provenance in the same complete source trace. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsOriginOrdinalTrace (track Result)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsPrivateCacheCompiler (erasedInterpreter)
variable {n : Nat} {X : Type}

/-- Every dictionary entry in this completed erased execution was already present or has a matching literal sealing cut in this same execution's trace. -/
theorem track_entry (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (result : Result n X)
    (supported : result ∈ support (track (erasedInterpreter modes decode crypto base writer replace) work state past))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (present : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    entry ∈ (state.keys label).1.successfulSeals ∨ ∃ cut ∈ result.1, cut.pending.material = label := by
  induction work using OracleComp.inductionOn generalizing state past result with
  | pure value =>
    change result ∈ support (pure ([], (value, state)) : ProbComp (Result n X)) at supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl present
  | query_bind query next ih =>
    by_cases sealed : ∃ pending, query = .sealing pending
    · obtain ⟨pending, rfl⟩ := sealed
      rw [PqxdhRecordFactsOriginOrdinalTrace.track_sealing] at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨reply, answered, inner, finished, rfl⟩ := supported
      rcases ih reply.1 reply.2 (past ++ [pending.material]) inner finished present with before | ⟨cut, member, same⟩
      · by_cases already : entry ∈ (state.keys label).1.successfulSeals
        · exact Or.inl already
        · obtain ⟨actual, queryEq, material⟩ := PqxdhRecordFactsOriginOrdinalServices.insertion_sealing
            modes decode crypto base writer replace (.sealing pending) state reply answered label entry already before
          cases queryEq
          exact Or.inr ⟨⟨pending, next, state, past⟩, List.mem_cons_self, material⟩
      · exact Or.inr ⟨cut, List.mem_cons_of_mem _ member, same⟩
    · rw [PqxdhRecordFactsOriginOrdinalTrace.track_other _ query (fun pending same => sealed ⟨pending, same⟩)] at supported
      simp only [mem_support_bind_iff] at supported
      obtain ⟨reply, answered, finished⟩ := supported
      rcases ih reply.1 reply.2 past result finished present with before | found
      · have same := PqxdhRecordFactsOriginOrdinalServices.service_nonSeal modes decode crypto base writer replace
          query (fun pending same => sealed ⟨pending, same⟩) state reply answered label
        exact Or.inl (same ▸ before)
      · exact Or.inr found

/-- Every member of this exact trace is its indexed supported source-prefix cut, so initialized source freshness facts apply to that same cut. -/
theorem tracked_cut (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (result : Result n X) (supported : result ∈ support (track service work state past))
    (cut : Cut n X) (member : cut ∈ result.1) :
    ∃ index, result.1[index]? = some cut ∧
      PqxdhRecordFactsPrivateCacheSource.Reach service work state past
        ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past ∧
      cut.past.length = past.length + index := by
  obtain ⟨index, chosen⟩ := List.mem_iff_getElem?.mp member
  have exactCut := PqxdhRecordFactsOriginOrdinalTrace.track_selected_support service work index state past result supported cut chosen
  exact ⟨index, chosen, PqxdhRecordFactsOriginOrdinalCut.scan_prefix service work index state past cut exactCut.1⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries.track_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries.track_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries.tracked_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalEntries.tracked_cut
