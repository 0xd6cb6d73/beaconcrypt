-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalServices

/-! Actual earlier sealing callbacks for entries present at a supported source prefix. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsPrivateCacheSource (Reach)
open PqxdhRecordFactsPrivateCacheCompiler (erasedInterpreter)
open PqxdhRecordFactsOriginOrdinal PqxdhRecordFactsOriginOrdinalServices
variable {n : Nat} {X : Type}

/-- An entry absent initially but present at the given prefix was inserted by an earlier literal seal at its exact material, with full endpoint states and continuation retained. -/
theorem reach_sealing (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry ∉ (start.keys label).1.successfulSeals)
    (reached : Reach (erasedInterpreter modes decode crypto impl writer replace)
      initial start past0 client state past) (present : entry ∈ (state.keys label).1.successfulSeals) :
    ∃ (pending : PqxdhRecordLiftProtocol.Sealing n)
      (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
      (before : CtxPrivate n) (history : List (Label n))
      (reply : (ServiceSpec n).Range (.sealing pending) × CtxPrivate n),
      Reach (erasedInterpreter modes decode crypto impl writer replace) initial start past0
        ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) before history ∧
      reply ∈ support ((erasedInterpreter modes decode crypto impl writer replace (.sealing pending)).run before) ∧
      pending.material = label ∧ entry ∉ (before.keys label).1.successfulSeals ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Reach (erasedInterpreter modes decode crypto impl writer replace) (next reply.1) reply.2
        (history ++ [pending.material]) client state past := by
  obtain ⟨query, next, before, history, reply, prior, supported, notYet, inserted, continued⟩ :=
    reach_insertion _ (fun current => entry ∈ (current.keys label).1.successfulSeals) absent reached present
  obtain ⟨pending, same, material⟩ := insertion_sealing modes decode crypto impl writer replace
    query before reply supported label entry notYet inserted
  subst query
  exact ⟨pending, next, before, history, reply, prior, supported, material, notYet, inserted, continued⟩

/-- A coordinate absent from the attempted history still has its initially empty seal dictionary at every supported prefix. -/
theorem reach_unattempted_empty (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    {initial client : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} (label : Label n)
    (empty : (start.keys label).1.successfulSeals = [])
    (reached : Reach (erasedInterpreter modes decode crypto impl writer replace)
      initial start past0 client state past) (unattempted : label ∉ past) :
    (state.keys label).1.successfulSeals = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry member
  obtain ⟨pending, next, before, history, reply, prior, supported, material, notYet, inserted, continued⟩ :=
    reach_sealing modes decode crypto impl writer replace label entry (by simp only [empty, List.not_mem_nil, not_false_eq_true]) reached member
  obtain ⟨tail, same⟩ := reach_history _ continued
  apply unattempted
  rw [same]
  simp [material]

open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftInterface (Environment)
variable {ι KemSK Reader Response E : Type} {baseSpec : OracleSpec ι}

/-- Before any actual initialized source sealing callback replies, its selected seal dictionary is empty, derived from source history alone. -/
theorem source_prefix_empty (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) state past) :
    (state.keys pending.material).1.successfulSeals = [] := by
  have fresh := PqxdhRecordFactsPrivateCacheSource.reach_fresh _
    (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary) reached
  rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
  exact reach_unattempted_empty modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
    (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace pending.material rfl reached fresh.1

/-- Every retained entry at an actual source prefix selects an earlier fresh empty-dictionary seal with its exact callback, full state and continuation, and bounded attempted ordinal. -/
theorem source_entry_sealing (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (client : OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
    (state : CtxPrivate n) (past : List (Label n))
    (reached : Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] client state past)
    (label : Label n) (entry : CtxSuccessfulSeal) (present : entry ∈ (state.keys label).1.successfulSeals) :
    ∃ (pending : PqxdhRecordLiftProtocol.Sealing n)
      (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) (PqxdhRecordLiftIdeal.Client n E X))
      (before : CtxPrivate n) (history : List (Label n))
      (reply : (ServiceSpec n).Range (.sealing pending) × CtxPrivate n),
      Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
        ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) before history ∧
      reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run before) ∧
      pending.material = label ∧ history.length < budget.sends ∧
      (before.keys label).1.successfulSeals = [] ∧
      PqxdhRecordFactsPrivateCacheSource.FreshPoint before (.sealing pending) ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Reach (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (next reply.1) reply.2
        (history ++ [pending.material]) client state past := by
  obtain ⟨pending, next, before, history, reply, prior, supported, material, notYet, inserted, continued⟩ :=
    reach_sealing modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace label entry
      (by exact List.not_mem_nil) reached present
  refine ⟨pending, next, before, history, reply, prior, supported, material,
    source_seal_index modes replace setup codec route env serverKid bounds mode budget adversary respects pending next before history prior,
    ?_, PqxdhRecordFactsPrivateCacheSource.source_prefix_fresh modes replace setup codec route env serverKid bounds mode adversary
      (.sealing pending) next before history prior, inserted, continued⟩
  simpa only [material] using source_prefix_empty modes replace setup codec route env serverKid bounds mode adversary
    pending next before history prior

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.reach_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.reach_sealing

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.reach_unattempted_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.reach_unattempted_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.source_prefix_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.source_prefix_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.source_entry_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalReach.source_entry_sealing
