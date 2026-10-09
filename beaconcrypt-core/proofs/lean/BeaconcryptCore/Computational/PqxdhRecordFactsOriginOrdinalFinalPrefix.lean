-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries

/-! The final boundary of one literal source path retains exactly its full chronological cut list. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
open PqxdhRecordFactsOriginOrdinalPath (Path Prefix prefix_trans)
variable {n : Nat} {X : Type}

/-- Every literal supported path is a prefix ending at its exact returned value and full state, retaining the identical chronological sealing-cut list. -/
theorem path_prefix (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {work : OracleComp (ServiceSpec n) X} {state : CtxPrivate n} {past : List (Label n)} {result : Result n X}
    (path : Path service work state past result) :
    ∃ finalPast, Prefix service work state past (pure result.2.1) result.2.2 finalPast result.1 := by
  induction path with
  | done value state past => exact ⟨past, Prefix.initial⟩
  | @step query next state past reply result supported tail ih =>
    obtain ⟨finalPast, ending⟩ := ih
    exact ⟨finalPast, prefix_trans service (Prefix.step Prefix.initial supported) ending⟩


/-- Every literal Reach witness admits a chronological cut decoration without changing its original work, complete state, history, or any callback. -/
theorem reach_prefix (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial work : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n} {past0 past : List (Label n)}
    (reached : PqxdhRecordFactsPrivateCacheSource.Reach service initial start past0 work state past) :
    ∃ cuts, Prefix service initial start past0 work state past cuts := by
  induction reached with
  | initial => exact ⟨[], Prefix.initial⟩
  | @step query next state past reply reached supported ih =>
    obtain ⟨cuts, before⟩ := ih
    exact ⟨_, Prefix.step before supported⟩


open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal (KeyMode)
open PqxdhRecordLiftProtocol (Service)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment)
variable {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι}

/-- A final retained entry selects an actual member of this same initialized execution's cut list, with its literal callback reply, fresh before-state and bounded attempted ordinal. -/
theorem source_final_entry (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : Result n (PqxdhRecordLiftIdeal.Client n E X))
    (path : Path (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] result)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    ∃ (cut : Cut n (PqxdhRecordLiftIdeal.Client n E X))
      (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n (PqxdhRecordLiftIdeal.Client n E X))) (finalPast : List (Label n)),
      Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
        ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier ∧
      reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state) ∧
      cut.pending.material = label ∧ cut.past.length = earlier.length ∧ cut.past.length < budget.sends ∧
      (cut.state.keys label).1.successfulSeals = [] ∧
      PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending) ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (cut.next reply.1) reply.2
        (cut.past ++ [cut.pending.material]) (pure result.2.1) result.2.2 finalPast later ∧
      result.1 = earlier ++ cut :: later := by
  obtain ⟨finalPast, reached⟩ := path_prefix _ path
  obtain ⟨cut, reply, earlier, later, rest⟩ :=
    PqxdhRecordFactsOriginOrdinalPathEntries.source_prefix_entry modes replace setup codec route env serverKid
      bounds mode budget adversary respects (pure result.2.1) result.2.2 finalPast result.1 reached label entry present
  exact ⟨cut, reply, earlier, later, finalPast, rest⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix.reach_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix.reach_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix.source_final_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix.source_final_entry
