-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPath

/-! Dictionary insertion in the exact chronological prefix of one tracked source path. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Prefix Path cutAt)
open PqxdhRecordLiftWorldProvenance (sealingCoordinates)
variable {n : Nat} {X : Type}

/-- A predicate acquired along this literal prefix has an actual transition, with its exact earlier and later cut lists and complete callback reply. -/
theorem prefix_insertion (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (predicate : CtxPrivate n → Prop)
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (absent : ¬ predicate start)
    (reached : Prefix service initial start past0 client state past cuts) (present : predicate state) :
    ∃ (query : Service n) (next : (ServiceSpec n).Range query → OracleComp (ServiceSpec n) X)
      (before : CtxPrivate n) (history : List (Label n))
      (reply : (ServiceSpec n).Range query × CtxPrivate n)
      (earlier later : List (Cut n X)),
      Prefix service initial start past0 ((ServiceSpec n).query query >>= next) before history earlier ∧
      reply ∈ support ((service query).run before) ∧ ¬ predicate before ∧ predicate reply.2 ∧
      Prefix service (next reply.1) reply.2 (history ++ sealingCoordinates query) client state past later ∧
      cuts = earlier ++ cutAt query next before history ++ later := by
  induction reached with
  | initial => exact False.elim (absent present)
  | @step query next state past cuts reply before supported ih =>
    by_cases already : predicate state
    · obtain ⟨priorQuery, priorNext, priorState, history, priorReply, earlier, later, prior, answered, notYet, inserted, suffix, same⟩ := ih already
      refine ⟨priorQuery, priorNext, priorState, history, priorReply, earlier, later ++ cutAt query next state past, prior, answered, notYet, inserted, Prefix.step suffix supported, ?_⟩
      simp only [same, List.append_assoc]
    · exact ⟨query, next, state, past, reply, cuts, [], before, supported, already, present, Prefix.initial, (List.append_nil _).symm⟩

open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordFactsPrivateCacheCompiler (erasedInterpreter)

/-- A dictionary entry at this literal prefix selects its actual earlier seal and exact reply, retaining the chronological cut split and the same subsequent prefix. -/
theorem prefix_entry_sealing (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)} (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry ∉ (start.keys label).1.successfulSeals)
    (reached : Prefix (erasedInterpreter modes decode crypto base writer replace)
      initial start past0 client state past cuts)
    (present : entry ∈ (state.keys label).1.successfulSeals) :
    ∃ (cut : Cut n X) (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n X)),
      Prefix (erasedInterpreter modes decode crypto base writer replace) initial start past0
        ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier ∧
      reply ∈ support ((erasedInterpreter modes decode crypto base writer replace (.sealing cut.pending)).run cut.state) ∧
      cut.pending.material = label ∧ entry ∉ (cut.state.keys label).1.successfulSeals ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Prefix (erasedInterpreter modes decode crypto base writer replace) (cut.next reply.1) reply.2
        (cut.past ++ [cut.pending.material]) client state past later ∧
      cuts = earlier ++ cut :: later := by
  obtain ⟨query, next, before, history, reply, earlier, later, prior, answered, notYet, inserted, suffix, same⟩ :=
    prefix_insertion _ (fun current => entry ∈ (current.keys label).1.successfulSeals) absent reached present
  obtain ⟨pending, sameQuery, material⟩ := PqxdhRecordFactsOriginOrdinalServices.insertion_sealing
    modes decode crypto base writer replace query before reply answered label entry notYet inserted
  subst query
  refine ⟨⟨pending, next, before, history⟩, reply, earlier, later, prior, answered, material, notYet, inserted, suffix, ?_⟩
  simpa only [cutAt, List.append_assoc, List.singleton_append] using same

/-- The exact chronological cut-list length counts every source sealing callback in the retained attempted-label history. -/
theorem prefix_length (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (reached : Prefix service initial start past0 client state past cuts) :
    past.length = past0.length + cuts.length := by
  induction reached with
  | initial => exact (Nat.add_zero _).symm
  | @step query next state past cuts reply before supported ih =>
    cases query <;> simp only [cutAt, sealingCoordinates, List.length_append, List.length_cons, List.length_nil, Nat.add_zero, ih, Nat.add_assoc]

open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment)
variable {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι}

/-- Every retained entry at this exact initialized source prefix selects a member of its own earlier cut list, with complete insertion reply, fresh empty before-state and bounded attempted ordinal. -/
theorem source_prefix_entry (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (client : OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (cuts : List (Cut n (PqxdhRecordLiftIdeal.Client n E X)))
    (reached : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] client state past cuts)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (state.keys label).1.successfulSeals) :
    ∃ (cut : Cut n (PqxdhRecordLiftIdeal.Client n E X))
      (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n (PqxdhRecordLiftIdeal.Client n E X))),
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
        (cut.past ++ [cut.pending.material]) client state past later ∧
      cuts = earlier ++ cut :: later := by
  obtain ⟨cut, reply, earlier, later, prior, answered, material, notYet, inserted, suffix, same⟩ :=
    prefix_entry_sealing modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
      label entry (by exact List.not_mem_nil) reached present
  have priorReach := PqxdhRecordFactsOriginOrdinalPath.prefix_reach _ prior
  refine ⟨cut, reply, earlier, later, prior, answered, material, ?_,
    PqxdhRecordFactsOriginOrdinal.source_seal_index modes replace setup codec route env serverKid bounds mode budget adversary respects cut.pending cut.next cut.state cut.past priorReach,
    ?_, PqxdhRecordFactsPrivateCacheSource.source_prefix_fresh modes replace setup codec route env serverKid bounds mode adversary (.sealing cut.pending) cut.next cut.state cut.past priorReach,
    inserted, suffix, same⟩
  · simpa only [List.length_nil, Nat.zero_add] using prefix_length _ prior
  · simpa only [material] using PqxdhRecordFactsOriginOrdinalReach.source_prefix_empty modes replace setup codec route env serverKid bounds mode adversary cut.pending cut.next cut.state cut.past priorReach

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.prefix_insertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.prefix_insertion
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.prefix_entry_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.prefix_entry_sealing
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.prefix_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.prefix_length
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.source_prefix_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPathEntries.source_prefix_entry
