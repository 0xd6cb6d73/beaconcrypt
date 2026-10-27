-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalMarkedPath
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess

/-! A literal source prefix ending in an empty selected dictionary has no earlier selected replay flag. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftProtocol (Service ServiceSpec)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalTrace (Result)
open PqxdhRecordFactsOriginOrdinalPath (Prefix cutAt)
open PqxdhRecordFactsOriginOrdinalMarkedPath (Flagged)
open PqxdhRecordFactsOriginMuteUntilBad (serviceBad)
variable {n : Nat} {X : Type}

/-- Supported forward membership preservation transports an empty after-dictionary backward without changing the actual callback reply. -/
theorem empty_before (target : Label n)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (preserves : ∀ (query : Service n) (state : CtxPrivate n)
      (reply : (ServiceSpec n).Range query × CtxPrivate n),
      reply ∈ support ((service query).run state) → ∀ entry ∈ (state.keys target).1.successfulSeals,
        entry ∈ (reply.2.keys target).1.successfulSeals)
    (query : Service n) (state : CtxPrivate n) (reply : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : reply ∈ support ((service query).run state))
    (empty : (reply.2.keys target).1.successfulSeals = []) :
    (state.keys target).1.successfulSeals = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry member
  have later := preserves query state reply supported entry member
  simp only [empty, List.not_mem_nil] at later

/-- An empty selected dictionary prevents a marker hit whenever the actual marker exposes an existing selected entry. -/
theorem empty_bad_false (target : Label n) (decode : RawDecoder)
    (hit_entry : ∀ (query : Service n) (state : CtxPrivate n),
      serviceBad target decode query state = true → ∃ entry, entry ∈ (state.keys target).1.successfulSeals)
    (query : Service n) (state : CtxPrivate n) (empty : (state.keys target).1.successfulSeals = []) :
    serviceBad target decode query state = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hit
  obtain ⟨entry, member⟩ := hit_entry query state hit
  simp only [empty, List.not_mem_nil] at member

/-- Preserve this literal prefix and every compatible flagged continuation, starting the prefix and continuation with a false marker derived from its empty endpoint dictionary. -/
theorem prefix_false (target : Label n) (decode : RawDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (preserves : ∀ (query : Service n) (state : CtxPrivate n)
      (reply : (ServiceSpec n).Range query × CtxPrivate n),
      reply ∈ support ((service query).run state) → ∀ entry ∈ (state.keys target).1.successfulSeals,
        entry ∈ (reply.2.keys target).1.successfulSeals)
    (hit_entry : ∀ (query : Service n) (state : CtxPrivate n),
      serviceBad target decode query state = true → ∃ entry, entry ∈ (state.keys target).1.successfulSeals)
    {initial work : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (prefixPath : Prefix service initial start past0 work state past cuts)
    (empty : (state.keys target).1.successfulSeals = []) :
    ∀ (result : Result n X) (after : Bool),
      Flagged target decode service work state past result false after →
      Flagged target decode service initial start past0 (cuts ++ result.1, result.2) false after := by
  induction prefixPath with
  | initial => exact fun _ _ tail => tail
  | @step query next state past cuts reply prefixPath supported ih =>
    have beforeEmpty := empty_before target service preserves query state reply supported empty
    have safe := empty_bad_false target decode hit_entry query state beforeEmpty
    intro result after tail
    simpa only [List.append_assoc] using ih beforeEmpty _ after
      (Flagged.step supported (by simpa only [safe, Bool.false_or] using tail))

/-- With the actual complete source decoder, hit-to-entry is derived from the checked literal raw parser; only supported dictionary preservation remains to instantiate. -/
theorem decoder_prefix_false (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (preserves : ∀ (query : Service n) (state : CtxPrivate n)
      (reply : (ServiceSpec n).Range query × CtxPrivate n),
      reply ∈ support ((service query).run state) → ∀ entry ∈ (state.keys target).1.successfulSeals,
        entry ∈ (reply.2.keys target).1.successfulSeals)
    {initial work : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (prefixPath : Prefix service initial start past0 work state past cuts)
    (empty : (state.keys target).1.successfulSeals = []) :
    ∀ (result : Result n X) (after : Bool),
      Flagged target (RawCtxUniversalDecoder.decoder read) service work state past result false after →
      Flagged target (RawCtxUniversalDecoder.decoder read) service initial start past0
        (cuts ++ result.1, result.2) false after := by
  apply prefix_false target (RawCtxUniversalDecoder.decoder read) service preserves _ prefixPath empty
  intro query current hit
  exact (PqxdhRecordFactsOriginRawGuess.service_bad target read query current hit).imp (fun _ evidence => evidence.1)

/-- Reinsert the literal selected sealing reply after its empty-dictionary prefix; every compatible marked suffix reconstructs the same whole-source flagged execution from false. -/
theorem sealing_prefix_false (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (preserves : ∀ (query : Service n) (state : CtxPrivate n)
      (reply : (ServiceSpec n).Range query × CtxPrivate n),
      reply ∈ support ((service query).run state) → ∀ entry ∈ (state.keys target).1.successfulSeals,
        entry ∈ (reply.2.keys target).1.successfulSeals)
    {initial : OracleComp (ServiceSpec n) X} {start state : CtxPrivate n}
    {past0 past : List (Label n)} {cuts : List (Cut n X)}
    (pending : PqxdhRecordLiftProtocol.Sealing n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (prefixPath : Prefix service initial start past0 ((ServiceSpec n).query (.sealing pending) >>= next) state past cuts)
    (empty : (state.keys target).1.successfulSeals = [])
    (reply : (ServiceSpec n).Range (.sealing pending) × CtxPrivate n)
    (supported : reply ∈ support ((service (.sealing pending)).run state))
    (result : Result n X) (after : Bool)
    (tail : Flagged target (RawCtxUniversalDecoder.decoder read) service (next reply.1) reply.2
      (past ++ [pending.material]) result false after) :
    Flagged target (RawCtxUniversalDecoder.decoder read) service initial start past0
      (cuts ++ ⟨pending, next, state, past⟩ :: result.1, result.2) false after := by
  have callback : Flagged target (RawCtxUniversalDecoder.decoder read) service
      ((ServiceSpec n).query (.sealing pending) >>= next) state past
      (cutAt (.sealing pending) next state past ++ result.1, result.2) false after :=
    Flagged.step supported (by simpa only [serviceBad, Bool.false_or, PqxdhRecordLiftWorldProvenance.sealingCoordinates] using tail)
  simpa only [cutAt, List.singleton_append] using decoder_prefix_false target read service preserves prefixPath empty _ after callback

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.empty_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.empty_before
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.empty_bad_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.empty_bad_false
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.prefix_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.prefix_false
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.decoder_prefix_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.decoder_prefix_false
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.sealing_prefix_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag.sealing_prefix_false
