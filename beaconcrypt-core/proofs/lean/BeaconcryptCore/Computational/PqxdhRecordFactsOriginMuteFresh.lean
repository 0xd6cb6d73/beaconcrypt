-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices

/-! Derive the muted continuation's selected-query restriction from the actual source attempted-coordinate history. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordLiftProtocolHistory (annotated Fresh)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing interpreter)
variable {n : Nat} {X : Type}

/-- A prior attempted coordinate cannot be the next fresh source sealing request. -/
theorem fresh_excludes (target : Label n) (past : List (Label n)) (present : target ∈ past)
    (query : Service n) (fresh : Fresh (past, query)) : ¬IsTargetSealing target query := by
  cases query with
  | sealing pending => exact fun same => fresh (same ▸ present)
  | _ => exact False.elim

/-- Every remaining adaptive source branch makes zero further seals at any already attempted coordinate. -/
theorem continuation_noSeal (target : Label n) (past : List (Label n)) (present : target ∈ past)
    (client : OracleComp (ServiceSpec n) X)
    (fresh : (annotated client past).AllQueriesSatisfy Fresh) :
    client.IsQueryBoundP (IsTargetSealing target) 0 := by
  induction client using OracleComp.inductionOn generalizing past with
  | pure value => exact OracleComp.isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (fresh_excludes target past present query fresh.1), fun reply => ?_⟩
      simpa only [Nat.zero_sub, ite_self] using
        ih reply _ (List.mem_append_left _ present) (fresh.2 reply)

/-- Every possible continuation of the literal selected seal, including writer failure, excludes another seal at that coordinate. -/
theorem after_seal_noSeal (past : List (Label n)) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (fresh : (annotated ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) past).AllQueriesSatisfy Fresh)
    (reply : (ServiceSpec n).Range (.sealing pending)) :
    (next reply).IsQueryBoundP (IsTargetSealing pending.material) 0 := by
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
  exact continuation_noSeal pending.material _
    (List.mem_append_right _ (List.mem_singleton_self pending.material)) (next reply) (fresh.2 reply)

/-- Source history discharges the muted service continuation's query restriction without an additional secrecy premise. -/
theorem after_seal_project (modes : Label n → KeyMode) (decode : AdaptiveCtxReceive.RawDecoder)
    (crypto : Pqxdh.Crypto) (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (past : List (Label n)) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (fresh : (annotated ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) past).AllQueriesSatisfy Fresh)
    (reply : (ServiceSpec n).Range (.sealing pending)) (state : CtxPrivate n) :
    Prod.map id (PqxdhRecordFactsOriginMuteFamily.project pending.material) <$>
      (simulateQ (interpreter pending.material modes decode crypto base writer replace) (next reply)).run state =
    Prod.map id (PqxdhRecordFactsOriginMuteFamily.project pending.material) <$>
      (simulateQ (interpreter pending.material modes decode crypto base writer replace) (next reply)).run
        (PqxdhRecordFactsOriginMuteFamily.project pending.material state) :=
  PqxdhRecordFactsOriginMuteServices.program_project pending.material modes decode crypto base writer replace
    (next reply) (after_seal_noSeal past pending next fresh reply) state

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.fresh_excludes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.fresh_excludes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.continuation_noSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.continuation_noSeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.after_seal_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh.after_seal_project
