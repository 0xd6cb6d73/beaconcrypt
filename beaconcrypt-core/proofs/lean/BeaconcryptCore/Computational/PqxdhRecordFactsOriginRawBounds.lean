-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-! Source-derived raw-attempt caps for full programs and supported continuations. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds
open PqxdhRecordLiftInterface
open PqxdhRecordLiftCtxProgramBounds (Weighted)
open PqxdhRecordLiftCtxProtocolBounds (categoryCost)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordFactsPrivateCacheSource (Reach)
variable {n : Nat}

/-- The existing weighted raw bill is the all-reply predicate count of hidden opening callbacks. -/
theorem raw_queries {X : Type} (work : OracleComp (ServiceSpec n) X) (cap : Nat)
    (bounded : Weighted (categoryCost .raw) work cap) :
    work.IsQueryBoundP (fun query => categoryCost .raw query = 1) cap := by
  apply OracleComp.IsQueryBound.proj id (h := bounded)
  · intro query current allowed
    cases query <;> simp_all [categoryCost]
    omega
  · intro query current allowed
    cases query <;> simp_all [categoryCost]

/-- The actual source receive budget bounds every literal hidden opening callback, with all typed replies retained. -/
theorem program_raw {E X Reader Response : Type} (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary).IsQueryBoundP
      (fun query => categoryCost .raw query = 1) budget.receives := by
  apply raw_queries
  simpa [PqxdhRecordLiftCtxBills.programBill, PqxdhRecordLiftCtxBills.effectBill,
    PqxdhRecordLiftCtxProgramBounds.operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
    PqxdhRecordLiftCtxProgramBounds.sealingCost, PqxdhRecordLiftCtxProgramBounds.openingCost] using
    PqxdhRecordLiftCtxBills.program_categories .raw env startup allowance framed crypto codec route
      serverKid bounds mode budget adversary respects 0

/-- Every actual supported prefix retains the original all-reply query allowance for its whole remaining source program. -/
theorem reach_queries {X : Type}
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (predicate : Service n → Prop) [DecidablePred predicate] (cap : Nat)
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (PqxdhRecordLiftWorldCompiler.Label n)}
    (bounded : initial.IsQueryBoundP predicate cap)
    (reached : Reach service initial start past0 client state past) :
    client.IsQueryBoundP predicate cap := by
  induction reached with
  | initial => exact bounded
  | @step query next before history reply prior supported ih =>
    rw [isQueryBoundP_query_bind_iff] at ih
    exact (ih.2 reply.1).mono (by split_ifs <;> omega)

/-- At any actual source prefix before a sealing reply, the literal remaining continuation keeps the original receive cap, including a failed writer reply. -/
theorem source_seal_continuation {E X Reader Response : Type} (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (start state : CtxPrivate n) (past0 past : List (PqxdhRecordLiftWorldCompiler.Label n))
    (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n)
      (PqxdhRecordLiftIdeal.Client n E X))
    (reached : Reach service
      (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)
      start past0 ((ServiceSpec n).query (.sealing pending) >>= next) state past)
    (reply : (ServiceSpec n).Range (.sealing pending)) :
    (next reply).IsQueryBoundP (fun query => categoryCost .raw query = 1) budget.receives := by
  have bounded := reach_queries service (fun query => categoryCost .raw query = 1) budget.receives
    (program_raw env startup allowance framed crypto codec route serverKid bounds mode budget adversary respects) reached
  rw [isQueryBoundP_query_bind_iff] at bounded
  exact (bounded.2 reply).mono (by split_ifs <;> omega)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.raw_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.raw_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.program_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.program_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.reach_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.reach_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.source_seal_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawBounds.source_seal_continuation
