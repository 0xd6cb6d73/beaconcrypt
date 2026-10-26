import BeaconcryptCore.Computational.PqxdhInitialNativeRetained
import BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix

/-! Replay an actual saved prefix under a retained extension, then resume its exact pending query and complete continuation. This is support provenance, not a probability or resource transfer. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingSupportReplay
open RawCtxPendingMixedPrefix RawCtxCursorLineage

/-- The actual scanned source prefix can precede any supported completion of the same saved frame under a retained extension of its reached cache. Completed frames are retained too. -/
theorem scan_replay {δ T U V : Type} {oracle : OracleSpec δ}
    (selected : δ → T → Bool) (impl : QueryImpl oracle (StateT T ProbComp))
    (other : RawCtxKdfRequestTable.Table → QueryImpl oracle (StateT U ProbComp))
    (cache : T → RawCtxKdfRequestTable.Table) (erase : T → U)
    (extension : ∀ q s, ∀ r ∈ support ((impl q).run s), Extends (cache s) (cache r.2))
    (replay : ∀ q s, ∀ r ∈ support ((impl q).run s), ∀ table, Extends (cache r.2) table →
      (r.1, erase r.2) ∈ support ((other table q).run (erase s)))
    (client : OracleComp oracle V) (state : T) (cut : Prefix oracle V T)
    (supported : cut ∈ support (RawCtxStatefulPendingPrefix.scan selected impl client state))
    (table : RawCtxKdfRequestTable.Table) (larger : Extends (cache cut.2) table) :
    Extends (cache state) (cache cut.2) ∧
      ∀ result, result ∈ support (finish (other table) (cut.1, erase cut.2)) →
        result ∈ support ((simulateQ (other table) client).run (erase state)) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [RawCtxStatefulPendingPrefix.scan_pure, mem_support_pure_iff] at supported
      subst cut
      exact ⟨fun _ _ known => known, fun _ completed => completed⟩
  | query_bind query next ih =>
      cases chosen : selected query state with
      | true =>
          rw [RawCtxStatefulPendingPrefix.scan_cut selected impl query next state chosen,
            mem_support_pure_iff] at supported
          subst cut
          exact ⟨fun _ _ known => known, fun result completed => by
            simpa only [finish, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] using completed⟩
      | false =>
          rw [RawCtxStatefulPendingPrefix.scan_other selected impl query next state chosen,
            mem_support_bind_iff] at supported
          obtain ⟨reply, head, tail⟩ := supported
          have later := ih reply.1 reply.2 tail
          refine ⟨fun address output known => later.1 address output
            (extension query state reply head address output known), ?_⟩
          intro result completed
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
          exact ⟨(reply.1, erase reply.2), replay query state reply head table
            (fun address output known => larger address output (later.1 address output known)),
            later.2 result completed⟩

end BeaconcryptCore.Computational.RawCtxPendingSupportReplay

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingSupportReplay.scan_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingSupportReplay.scan_replay
