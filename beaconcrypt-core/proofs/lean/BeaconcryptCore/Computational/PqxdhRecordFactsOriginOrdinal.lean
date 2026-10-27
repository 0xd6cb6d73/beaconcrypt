-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginServices
import BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills

/-! Select an actual supported callback before a given source execution prefix, without requiring later completion. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordFactsPrivateCacheSource (Reach)
variable {n : Nat} {X : Type}

/-- A property becomes true at this literal supported callback, retaining its full prefix and remaining supported path. -/
def Insertion (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (initial : OracleComp (ServiceSpec n) X) (start : CtxPrivate n) (past0 : List (Label n))
    (client : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (property : CtxPrivate n → Prop) : Prop :=
  ∃ (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
    (before : CtxPrivate n) (history : List (Label n)) (reply : (ServiceSpec n).Range query × CtxPrivate n),
    Reach service initial start past0
      ((liftM ((ServiceSpec n).query query) : OracleComp (ServiceSpec n) _) >>= next) before history ∧
    reply ∈ support ((service query).run before) ∧ ¬property before ∧ property reply.2 ∧
    Reach service (next reply.1) reply.2
      (history ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query) client state past

/-- Every new state fact at a supported prefix arose at an actual supported callback before that prefix. -/
theorem reach_insertion (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (property : CtxPrivate n → Prop) (absent : ¬property start)
    (reached : Reach service initial start past0 client state past) (present : property state) :
    Insertion service initial start past0 client state past property := by
  induction reached with
  | initial => exact False.elim (absent present)
  | @step query next before history reply prior supported ih =>
    by_cases earlier : property before
    · obtain ⟨selected, remaining, selectedState, attempted, answer, selectedReached, answered, notYet, inserted, tail⟩ := ih earlier
      exact ⟨selected, remaining, selectedState, attempted, answer, selectedReached, answered, notYet, inserted,
        Reach.step tail supported⟩
    · exact ⟨query, next, before, history, reply, prior, supported, earlier, present, Reach.initial⟩

/-- Every supported prefix retains the original attempted-coordinate history as a literal prefix. -/
theorem reach_history (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (reached : Reach service initial start past0 client state past) :
    ∃ added, past = past0 ++ added := by
  induction reached with
  | initial => exact ⟨[], (List.append_nil _).symm⟩
  | @step query next before history reply prior supported ih =>
    obtain ⟨added, same⟩ := ih
    exact ⟨added ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query,
      by simp only [same, List.append_assoc]⟩

/-- Attempt history records exactly the existing hidden-seal cost, before the callback outcome. -/
theorem sealingCoordinates_length (query : Service n) :
    (PqxdhRecordLiftWorldProvenance.sealingCoordinates query).length =
      PqxdhRecordFactsHashSealBills.sealCost query := by
  cases query <;> rfl

/-- Every supported prefix has an exact residual syntactic sealing allowance, including all possible later replies. -/
theorem reach_bill (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (bound : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost initial bound)
    (reached : Reach service initial start past0 client state past) :
    ∃ remaining, PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost client remaining ∧
      past.length + remaining = past0.length + bound := by
  induction reached with
  | initial => exact ⟨bound, bounded, rfl⟩
  | @step query next before history reply prior supported ih =>
    obtain ⟨remaining, continued, total⟩ := ih
    rw [PqxdhRecordLiftCtxProgramBounds.Weighted, isQueryBound_query_bind_iff] at continued
    refine ⟨remaining - PqxdhRecordFactsHashSealBills.sealCost query, continued.2 reply.1, ?_⟩
    rw [List.length_append, sealingCoordinates_length]
    omega

/-- A selected sealing request has an ordinal below the full attempted-seal allowance before its reply is known. -/
theorem seal_index_lt (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (bound : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost initial bound)
    (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (reached : Reach service initial start past0
      ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) state past) :
    past.length < past0.length + bound := by
  obtain ⟨remaining, continued, total⟩ := reach_bill service bound bounded reached
  rw [PqxdhRecordLiftCtxProgramBounds.Weighted, isQueryBound_query_bind_iff] at continued
  have positive : 1 ≤ remaining := continued.1
  omega

open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment)
variable {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι}

/-- The actual initialized erased source supplies a strict `budget.sends` cap on every selected seal ordinal, independently of its outcome. -/
theorem source_seal_index (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) state past) :
    past.length < budget.sends := by
  simpa only [List.length_nil, Nat.zero_add] using seal_index_lt _ budget.sends
    (PqxdhRecordFactsHashSealBills.program_seals env setup.source.crypto codec route serverKid bounds mode budget adversary respects)
    pending next reached

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.reach_insertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.reach_insertion

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.reach_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.reach_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.sealingCoordinates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.sealingCoordinates_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.reach_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.reach_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.seal_index_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.seal_index_lt

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.source_seal_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinal.source_seal_index
