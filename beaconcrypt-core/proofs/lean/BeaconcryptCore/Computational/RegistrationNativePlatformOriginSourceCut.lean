-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginProgram
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix
/-! A final dictionary entry of the actual arbitrary native World tree selects an original same-run attempted seal. The full reached prefix and all source continuations are retained; freshness and query caps are derived from literal schedule syntax. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Prefix Path)
open RegistrationNativeRecordOriginProgram (program)
open RegistrationNativeRecordPackage (Extra)
variable {n : Nat} {I KemSK Reader Response E Value : Type} {base : OracleSpec I}
variable (modes : Label n → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (RegistrationNativeEntropyRun.Outcome E Value))
local notation "Client" => PqxdhRecordLiftIdeal.Client n (Extra E) Value
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "start" => PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))

/-- Any hidden seal retained at this actual source prefix has its own earlier attempted callback, a fresh empty dictionary there, and bounded literal continuations for every optional reply. -/
theorem prefix_entry (sealCap rawCap : Nat)
    (seals : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost (program codec route work) sealCap)
    (raws : (program codec route work).IsQueryBoundP (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (client : OracleComp (ServiceSpec n) Client) (state : CtxPrivate n) (past : List (Label n)) (cuts : List (Cut n Client))
    (reached : Prefix service (program codec route work) start [] client state past cuts)
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (present : entry ∈ (state.keys label).1.successfulSeals) :
    ∃ (cut : Cut n Client) (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n Client)),
      Prefix service (program codec route work) start [] ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier ∧
      reply ∈ support ((service (.sealing cut.pending)).run cut.state) ∧ cut.pending.material=label ∧
      cut.past.length=earlier.length ∧ cut.past.length<sealCap ∧
      (cut.state.keys label).1.successfulSeals=[] ∧
      PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending) ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Prefix service (cut.next reply.1) reply.2 (cut.past++[cut.pending.material]) client state past later ∧
      cuts=earlier++cut::later ∧
      (∀answer,(cut.next answer).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing cut.pending.material) 0) ∧
      (∀answer,(cut.next answer).IsQueryBoundP (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap) := by
  obtain ⟨cut,reply,earlier,later,prior,answered,material,notYet,inserted,suffix,same⟩ :=
    PqxdhRecordFactsOriginOrdinalPathEntries.prefix_entry_sealing modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
      label entry (by exact List.not_mem_nil) reached present
  have actual := PqxdhRecordFactsOriginOrdinalPath.prefix_reach service prior
  have fresh := PqxdhRecordFactsPrivateCacheSource.reach_fresh service (RegistrationNativeRecordOriginProgram.fresh codec route work) actual
  have cap := PqxdhRecordFactsOriginRawBounds.reach_queries service _ rawCap raws actual
  rw [isQueryBoundP_query_bind_iff] at cap
  refine ⟨cut,reply,earlier,later,prior,answered,material,?_,?_,?_,?_,inserted,suffix,same,?_,?_⟩
  · simpa only [List.length_nil,Nat.zero_add] using PqxdhRecordFactsOriginOrdinalPathEntries.prefix_length service prior
  · simpa only [List.length_nil,Nat.zero_add] using PqxdhRecordFactsOriginOrdinal.seal_index_lt service sealCap seals cut.pending cut.next actual
  · simpa only [material] using RegistrationNativeRecordOriginProgram.prefix_empty modes replace setup codec route work cut.pending cut.next cut.state cut.past actual
  · exact RegistrationNativeRecordOriginProgram.prefix_fresh modes replace setup codec route work (.sealing cut.pending) cut.next cut.state cut.past actual
  · intro answer
    exact PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next fresh answer
  · intro answer
    exact (cap.2 answer).mono (by split_ifs <;> omega)

/-- Supported full source execution itself supplies the chronological prefix and chosen callback; no caller journal or path invariant is required. -/
theorem tracked_entry (sealCap rawCap : Nat)
    (seals : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost (program codec route work) sealCap)
    (raws : (program codec route work).IsQueryBoundP (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap)
    (result : PqxdhRecordFactsOriginOrdinalTrace.Result n Client)
    (supported : result ∈ support (PqxdhRecordFactsOriginOrdinalTrace.track service (program codec route work) start []))
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal) (present : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    ∃ (cut : Cut n Client) (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
      (earlier later : List (Cut n Client)) (finalPast : List (Label n)),
      Prefix service (program codec route work) start [] ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier ∧
      reply ∈ support ((service (.sealing cut.pending)).run cut.state) ∧ cut.pending.material=label ∧
      cut.past.length=earlier.length ∧ cut.past.length<sealCap ∧
      (cut.state.keys label).1.successfulSeals=[] ∧
      PqxdhRecordFactsPrivateCacheSource.FreshPoint cut.state (.sealing cut.pending) ∧
      entry ∈ (reply.2.keys label).1.successfulSeals ∧
      Prefix service (cut.next reply.1) reply.2 (cut.past++[cut.pending.material]) (pure result.2.1) result.2.2 finalPast later ∧
      result.1=earlier++cut::later ∧
      (∀answer,(cut.next answer).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing cut.pending.material) 0) ∧
      (∀answer,(cut.next answer).IsQueryBoundP (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) rawCap) := by
  have path := PqxdhRecordFactsOriginOrdinalPath.support_path service (program codec route work) start [] result supported
  obtain ⟨finalPast,ending⟩ := PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix service path
  obtain ⟨cut,reply,earlier,later,receipt⟩ := prefix_entry modes replace setup codec route work sealCap rawCap seals raws _ _ _ _ ending label entry present
  exact ⟨cut,reply,earlier,later,finalPast,receipt⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut.prefix_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut.prefix_entry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut.tracked_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceCut.tracked_entry
