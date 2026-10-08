-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxLink
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds

/-!
# Record-lift CTX availability: every keyed request is at a present, bounded coordinate (items 4 and 5, stage S4)

**Why.** `PqxdhRecordLiftIdeal.materialAt` reads a coordinate's message key and nonce from the chain table with a total all-zero fallback. A CTX world whose keyed requests could reach an absent coordinate would key it with that fallback, and a coordinate of unbounded depth would lie outside every hybrid index of `PqxdhRecordLiftChainOrder`. This module shows that neither happens, for every key function, every mode assignment and every adversary within its budget, so the hybrid argument and the selected-key law need no such premise.

**The program's lookup history.** `ServiceSafe program []` (`program_history`): on every reply path of the compiled protocol program, every private lookup is `Available` against the table of the coordinates looked up before (`historyTable`), and every hidden opening or seal reads the material of a coordinate looked up before. The history is threaded through owner, Server and Beacon requests by the stored-kernel references of `PqxdhRecordLiftChainCompiler` (`ControlReady`). `program_lookups`: the program makes at most `positions budget` lookups (one per send, 51 per raw receive), from `PqxdhRecordLiftBudget.program_record_bound`.

**Transfer.** `certified_map` is the generic consequence for any private interpreter (any state type) whose chain table grows and holds every looked-up coordinate: if its requests touching only present coordinates within `positions` are simulated through a state map by another interpreter, the whole certified program is (`program_map` for the compiled program). For the CTX world with an arbitrary keyed implementation (`ctxInterpreterOf`), keyed implementations agreeing on present coordinates within `positions budget` give the same world (`program_congr`, `ctxRunWith_congr`), and the last hybrid of `PqxdhRecordLiftCtxHybrid` is `PqxdhRecordLiftIdeal.idealAuth` (`hybrid_last`).

**Scope.** No theorem of this module has an assumption or contract hypothesis or uses a contract: no proof uses a field of the primitive record or a security game (fields reached only inside definitions, such as those of the setup's DH interface, are structural). This module leaves the selected-key lazy/eager law to `PqxdhRecordLiftKeyCut`, and the hop bounds and the assembly of `CtxAuthLiftStatement` to `PqxdhRecordLiftCtx` and `PqxdhRecordLiftCtxBills`; see `doc/impl/record-lift-ctx-hybrid.md`. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftCtxHybrid PqxdhRecordLiftCtxLink
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-- A present opening's material is referenced by the effect: a cached material is one of the kernel's stored slots, a future material is the target material. -/
theorem opening_material_present {Context : Type} (table : Table (Slot n))
    (pending : RawCtxInterpretedOpening.Opening (Label n) (Label n) (Label n) Context)
    (refs : EffectPresent table (.openRequested pending)) (label : Label n)
    (selected : RawCtxInterpretedOpening.material pending = .ok (.Some label)) : Present table label := by
  unfold RawCtxInterpretedOpening.material at selected
  cases prepared : pending.prepared with
  | PreparedReceiveCachedCase cached =>
      rw [prepared] at selected
      simp only at selected
      obtain ⟨index, _, selected⟩ := PqxdhFirstRecordReplay.rust_bind_ok selected
      obtain ⟨capacity, _, selected⟩ := PqxdhFirstRecordReplay.rust_bind_ok selected
      split at selected
      · cases selected
      · obtain ⟨entry, found, selected⟩ := PqxdhFirstRecordReplay.rust_bind_ok selected
        obtain ⟨borrowed, borrowedEq, selected⟩ := PqxdhFirstRecordReplay.rust_bind_ok selected
        cases borrowed with
        | none => cases selected
        | some stored =>
            simp only at selected
            split at selected
            · simp only [RustM.ok.injEq] at selected
              cases selected
              have entryEq : entry = some stored := by
                cases entry with
                | none => cases borrowedEq
                | some value =>
                    simp only [core.option.Option.as_ref, RustM.ok.injEq] at borrowedEq
                    rw [borrowedEq]
              have member : some stored ∈ pending.entry.receive_slots.val := by
                unfold Std.Array.index_usize at found
                split at found
                · cases found
                · rename_i value lookup
                  simp only [RustM.ok.injEq] at found
                  rw [← entryEq, ← found]
                  exact List.mem_of_getElem? lookup
              simp only [EffectPresent] at refs
              exact refs.1 stored member
            · cases selected
  | PreparedReceiveFutureCase future =>
      rw [prepared] at selected
      simp only [RustM.ok.injEq] at selected
      cases selected
      simp only [EffectPresent, prepared] at refs
      exact refs.2.2
/-- The native KDF counter of a CTX-world state. -/
def kdfOf (state : CtxPrivate n) : Nat := state.base.primitive.1.native .kdf

/-- A lookup of the CTX world is the chain world's all-ideal persistent lookup on the base state. -/
theorem lookup_factor (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (coordinate : Label n) (state : CtxPrivate n) :
    (ctxInterpreterWith keyOf modes replace setup codec (.lookup coordinate)).run state =
      (fun result => ((), { state with base := { state.base with chain := result.2.1, primitive := result.2.2 } })) <$>
        (PqxdhRecordLiftChainOracle.lookup setup.source (PqxdhRecordLiftProtocol.cachedSeeds state.base) (fun _ => true)
          coordinate).run (state.base.chain, state.base.primitive) := by
  simp only [ctxInterpreterWith, onBase, PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.withRecord,
    PqxdhRecordLiftProtocol.localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
    PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.putRecord,
    idealPolicy, PqxdhRecordLiftMixedWorld.policy, StateT.run, bind_pure_comp, Functor.map_map]
  rw [stateT_map_apply]
  simp only [PqxdhRecordLiftLoggedAdapters.liftLookup, StateT.run, Functor.map_map]

/-- Every all-ideal lookup charges exactly one native KDF call. -/
theorem lookup_kdf (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds (Slot n))
    (coordinate : Label n) (state : Execution (Slot n) PqxdhRecordLiftWorld.Primitive)
    (result : PqxdhFullSecretInputKdf.FullOutput × Execution (Slot n) PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftChainOracle.lookup source seeds (fun _ => true) coordinate).run state)) :
    result.2.2.1.native .kdf = state.2.1.native .kdf + 1 := by
  cases found : state.1 coordinate with
  | some output =>
      rw [PqxdhRecordLiftChainOracle.lookup_hit _ _ _ _ _ rfl output found, support_pure,
        Set.mem_singleton_iff] at supported
      subst result
      simp [PqxdhRecordLiftChainOracle.charge]
  | none =>
      rw [PqxdhRecordLiftChainOracle.lookup_miss _ _ _ _ _ rfl found, support_map] at supported
      obtain ⟨output, _, rfl⟩ := supported
      simp [PqxdhRecordLiftChainOracle.charge]

/-- A lookup of the CTX world at an available coordinate grows the table by that coordinate, keeps it closed and depth-bounded by the native KDF counter, charges one KDF call, and keeps every CTX state and the seeds. -/
theorem lookup_support (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (coordinate : Label n) (state : CtxPrivate n) (closed : Closed state.base.chain)
    (available : Available state.base.chain coordinate)
    (depth : PqxdhRecordLiftChainOrder.DepthBound state.base.chain (kdfOf state))
    (result : Unit × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreterWith keyOf modes replace setup codec (.lookup coordinate)).run state)) :
    state.base.chain ≤ result.2.base.chain ∧ Present result.2.base.chain coordinate ∧ Closed result.2.base.chain ∧
      PqxdhRecordLiftChainOrder.DepthBound result.2.base.chain (kdfOf result.2) ∧ kdfOf result.2 = kdfOf state + 1 ∧
      result.2.keys = state.keys ∧ result.2.base.seeds = state.base.seeds := by
  rw [lookup_factor, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have valid : PqxdhRecordLiftChainOracle.Valid setup.source (PqxdhRecordLiftProtocol.cachedSeeds state.base)
      (fun _ => true) state.base.chain := ⟨closed, fun _ _ real _ => absurd real (by simp)⟩
  have facts := PqxdhRecordLiftChainOracle.lookup_preserves setup.source (PqxdhRecordLiftProtocol.cachedSeeds state.base)
    (fun _ => true) coordinate (state.base.chain, state.base.primitive) valid available inner member
  have bounded := PqxdhRecordLiftChainOrder.lookup_depth setup.source (PqxdhRecordLiftProtocol.cachedSeeds state.base)
    (fun _ => true) coordinate (state.base.chain, state.base.primitive) depth available inner member
  exact ⟨facts.1, ⟨inner.1, facts.2.1⟩, facts.2.2.1, bounded,
    lookup_kdf setup.source _ coordinate _ inner member, rfl, rfl⟩

/-! ### The lookup history of a program, over every reply -/

/-- The table whose present coordinates are exactly a lookup history. Its values are irrelevant. -/
noncomputable def historyTable (past : List (Label n)) : Table (Slot n) := fun label =>
  if label ∈ past then some fallbackOutput else none

theorem historyTable_present (past : List (Label n)) (label : Label n) :
    Present (historyTable past) label ↔ label ∈ past := by
  constructor
  · rintro ⟨output, found⟩
    by_contra absent
    simp [historyTable, absent] at found
  · intro member
    exact ⟨fallbackOutput, by simp [historyTable, member]⟩

theorem historyTable_mono (past later : List (Label n)) (sub : past ⊆ later) :
    historyTable past ≤ historyTable later := by
  intro label output found
  have member : label ∈ past := (historyTable_present past label).mp ⟨output, found⟩
  simp only [historyTable, member, ite_true] at found
  simp only [historyTable, sub member, ite_true, found]

theorem historyTable_append (past : List (Label n)) (label : Label n) :
    historyTable (past ++ [label]) label = some fallbackOutput := by
  simp [historyTable]

/-- The coordinate a local request looks up, if any. -/
def localLookups : (PqxdhRecordLiftProtocol.LocalSpec n).Domain → List (Label n)
  | .inl coordinate => [coordinate]
  | _ => []

/-- Pre-query availability of a local request against the lookup history: a lookup has its predecessor in the history (or is a chain start), an opening's selected material and a seal's material were looked up before. -/
def LocalAvail (past : List (Label n)) : (PqxdhRecordLiftProtocol.LocalSpec n).Domain → Prop
  | .inl coordinate => Available (historyTable past) coordinate
  | .inr (.inl pending) => ∀ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) → label ∈ past
  | .inr (.inr pending) => pending.material ∈ past

/-- Every reached local request, on every reply path, is available against its prior lookup history. -/
def LocalSafe {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result) :
    List (Label n) → Prop :=
  OracleComp.recOn client (fun _ _ => True)
    (fun query _ continued past => LocalAvail past query ∧ ∀ reply, continued reply (past ++ localLookups query))

/-- The local program with its lookup history threaded through every reply. -/
def localTrack : QueryImpl (PqxdhRecordLiftProtocol.LocalSpec n)
    (StateT (List (Label n)) (OracleComp (PqxdhRecordLiftProtocol.LocalSpec n))) := fun query past =>
  (fun reply => (reply, past ++ localLookups query)) <$> (PqxdhRecordLiftProtocol.LocalSpec n).query query

theorem localSafe_query_bind {Result : Type} (query : (PqxdhRecordLiftProtocol.LocalSpec n).Domain)
    (next : (PqxdhRecordLiftProtocol.LocalSpec n).Range query → OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (past : List (Label n)) :
    LocalSafe ((liftM ((PqxdhRecordLiftProtocol.LocalSpec n).query query) :
      OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) _) >>= next) past ↔
      LocalAvail past query ∧ ∀ reply, LocalSafe (next reply) (past ++ localLookups query) := Iff.rfl

theorem localTrack_query_bind {Result : Type} (query : (PqxdhRecordLiftProtocol.LocalSpec n).Domain)
    (next : (PqxdhRecordLiftProtocol.LocalSpec n).Range query → OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (past : List (Label n)) (result : Result × List (Label n))
    (supported : result ∈ support ((simulateQ localTrack ((liftM ((PqxdhRecordLiftProtocol.LocalSpec n).query query) :
      OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) _) >>= next)).run past)) :
    ∃ reply, result ∈ support ((simulateQ localTrack (next reply)).run (past ++ localLookups query)) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, member, continued⟩ := supported
  simp only [localTrack, StateT.run, support_map, Set.mem_image] at member
  obtain ⟨reply, _, rfl⟩ := member
  exact ⟨reply, continued⟩

/-- On every reply path, a hidden receive's local program makes only available lookups and opens only looked-up material, and its resulting kernel references only looked-up coordinates. -/
theorem receive_history (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n) (target : Std.U64)
    (effect : Effect (Slot n) RawCtxWholeOwner.OpenContext)
    (admitted : PqxdhFirstRecordReplay.Admitted entry target effect) (past : List (Label n))
    (refs : References (historyTable past) effect) :
    LocalSafe (PqxdhRecordLiftOpaqueDrivers.receiveProgram (Plaintext := RawCtxWholeOwner.Decrypted)
        (SealContext := RawCtxSourceSend.SealContext) (Output := RawCtxSourceSend.Encrypted) effect) past ∧
      ∀ result ∈ support ((simulateQ localTrack (PqxdhRecordLiftOpaqueDrivers.receiveProgram
          (Plaintext := RawCtxWholeOwner.Decrypted) (SealContext := RawCtxSourceSend.SealContext)
          (Output := RawCtxSourceSend.Encrypted) effect)).run past),
        KernelReferences (historyTable result.2) result.1.1 ∧ past ⊆ result.2 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect past with
  | h depth ih =>
    cases effect with
    | rejected original context =>
        rw [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        refine ⟨trivial, fun result supported => ?_⟩
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨refs, fun _ member => member⟩
    | openRequested pending =>
        rw [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        refine ⟨⟨fun label selected => (historyTable_present past label).mp
          (opening_material_present (historyTable past) pending refs.2 label selected), fun _ => trivial⟩,
          fun result supported => ?_⟩
        obtain ⟨reply, continued⟩ := localTrack_query_bind _ _ past result supported
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, localLookups,
          List.append_nil] at continued
        subst result
        exact ⟨finish_references (historyTable past) pending target
          (by simpa only [admitted.1] using admitted.2) refs reply, fun _ member => member⟩
    | kdfRequested pending =>
        rw [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        have grown : References (historyTable (past ++ [pending.request]))
            (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) :=
          resume_references (historyTable past) (historyTable (past ++ [pending.request]))
            (historyTable_mono past _ (List.subset_append_left _ _)) pending refs fallbackOutput
            (historyTable_append past pending.request)
        have later := ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
          _ (PqxdhFirstRecordReplay.resume_admitted entry target pending (advance pending.request 1, pending.request) admitted)
          (past ++ [pending.request]) grown rfl
        refine ⟨⟨refs.1.2, fun _ => later.1⟩, fun result supported => ?_⟩
        obtain ⟨reply, continued⟩ := localTrack_query_bind _ _ past result supported
        have facts := later.2 result continued
        exact ⟨facts.1, fun label member => facts.2 (List.mem_append_left _ member)⟩

/-- On every reply path, a hidden send's local program looks up an available coordinate and seals exactly that coordinate, and its advanced kernel references only looked-up coordinates. -/
theorem send_history (start : Start (Slot n) RawCtxSourceSend.SealContext) (past : List (Label n))
    (refs : SendReferences (historyTable past) start) :
    LocalSafe (PqxdhRecordLiftOpaqueDrivers.sendProgram (OpenContext := RawCtxWholeOwner.OpenContext)
        (Plaintext := RawCtxWholeOwner.Decrypted) (Output := RawCtxSourceSend.Encrypted) start) past ∧
      ∀ result ∈ support ((simulateQ localTrack (PqxdhRecordLiftOpaqueDrivers.sendProgram
          (OpenContext := RawCtxWholeOwner.OpenContext) (Plaintext := RawCtxWholeOwner.Decrypted)
          (Output := RawCtxSourceSend.Encrypted) start)).run past),
        KernelReferences (historyTable result.2) result.1.1 ∧ past ⊆ result.2 := by
  cases start with
  | exhausted entry context =>
      rw [PqxdhRecordLiftOpaqueDrivers.sendProgram]
      refine ⟨trivial, fun result supported => ?_⟩
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨refs, fun _ member => member⟩
  | requested pending =>
      rw [PqxdhRecordLiftOpaqueDrivers.sendProgram]
      have mono := historyTable_mono past (past ++ [pending.request]) (List.subset_append_left _ _)
      refine ⟨(localSafe_query_bind _ _ _).mpr ⟨refs.1.2, fun _ => (localSafe_query_bind _ _ _).mpr
        ⟨List.mem_append_right _ (List.mem_singleton_self _), fun _ => trivial⟩⟩, fun result supported => ?_⟩
      obtain ⟨_, continued⟩ := localTrack_query_bind _ _ past result supported
      obtain ⟨sealed, continued⟩ := localTrack_query_bind _ _ _ result continued
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, localLookups,
        List.append_nil] at continued
      subst result
      refine ⟨⟨⟨successor_available (historyTable (past ++ [pending.request])) pending.request
          (available_mono _ _ mono _ refs.1.2) fallbackOutput (historyTable_append past pending.request),
        available_mono _ _ mono _ refs.1.1.2⟩, slots_present_mono _ _ mono _ refs.2⟩,
        List.subset_append_left _ _⟩

/-! ### The lookup history of the private service program -/

/-- The coordinate a private service request looks up, if any. -/
def lookupCoordinates : PqxdhRecordLiftProtocol.Service n → List (Label n)
  | .lookup coordinate => [coordinate]
  | _ => []

/-- Pre-query availability of a private service request against the lookup history. -/
def Avail (past : List (Label n)) : PqxdhRecordLiftProtocol.Service n → Prop
  | .lookup coordinate => Available (historyTable past) coordinate
  | .opening pending => ∀ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) → label ∈ past
  | .sealing pending => pending.material ∈ past
  | _ => True

/-- Every reached private request, on every reply path, is available against its prior lookup history. -/
def ServiceSafe {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) :
    List (Label n) → Prop :=
  OracleComp.recOn client (fun _ _ => True)
    (fun query _ continued past => Avail past query ∧ ∀ reply, continued reply (past ++ lookupCoordinates query))

/-- The private service program with its lookup history threaded through every reply. -/
def track : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n)
    (StateT (List (Label n)) (OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n))) := fun query past =>
  (fun reply => (reply, past ++ lookupCoordinates query)) <$> (PqxdhRecordLiftProtocol.ServiceSpec n).query query

/-- The histories reachable by a private service program over every reply. -/
abbrev Trace {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (Label n)) : Set (Result × List (Label n)) :=
  support ((simulateQ track client).run past)

theorem serviceSafe_query_bind {Result : Type} (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (next : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query →
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (past : List (Label n)) :
    ServiceSafe ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) :
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= next) past ↔
      Avail past query ∧ ∀ reply, ServiceSafe (next reply) (past ++ lookupCoordinates query) := Iff.rfl

theorem serviceSafe_pure {Result : Type} (value : Result) (past : List (Label n)) :
    ServiceSafe (pure value : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) past := trivial

theorem trace_pure {Result : Type} (value : Result) (past : List (Label n)) :
    Trace (pure value : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) past = {(value, past)} := by
  simp [Trace]

/-- Every reply of a private request is reachable under the history tracker. -/
theorem track_member (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (reply : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query) (past : List (Label n)) :
    (reply, past ++ lookupCoordinates query) ∈ support ((track query).run past) := by
  change (reply, past ++ lookupCoordinates query) ∈ support ((fun reply => (reply, past ++ lookupCoordinates query)) <$>
    (liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _))
  rw [support_map]
  exact ⟨reply, mem_support_query _ _, rfl⟩

/-- Safety composes through every reached history of the first program. -/
theorem serviceSafe_bind {Result Next : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (next : Result → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Next) (past : List (Label n))
    (safe : ServiceSafe client past)
    (continued : ∀ result ∈ Trace client past, ServiceSafe (next result.1) result.2) :
    ServiceSafe (client >>= next) past := by
  induction client using OracleComp.inductionOn generalizing past with
  | pure value =>
      simpa only [pure_bind] using continued (value, past) (by simp [Trace])
  | query_bind query rest ih =>
      rw [bind_assoc]
      refine (serviceSafe_query_bind _ _ _).mpr ⟨safe.1, fun reply => ih reply _ (safe.2 reply) ?_⟩
      intro result member
      apply continued result
      simp only [Trace, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      exact ⟨(reply, past ++ lookupCoordinates query), track_member query reply past, member⟩

/-- Every history reached by a bound program passes through a history reached by its first part. -/
theorem trace_bind {Result Next : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (next : Result → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Next) (past : List (Label n))
    (final : Next × List (Label n)) (member : final ∈ Trace (client >>= next) past) :
    ∃ middle ∈ Trace client past, final ∈ Trace (next middle.1) middle.2 := by
  simp only [Trace, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  exact member

theorem serviceSafe_map {Result Next : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (f : Result → Next) (past : List (Label n)) (safe : ServiceSafe client past) :
    ServiceSafe (f <$> client) past := by
  rw [map_eq_bind_pure_comp]
  exact serviceSafe_bind _ _ _ safe (fun _ _ => trivial)

theorem trace_map {Result Next : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (f : Result → Next) (past : List (Label n)) (final : Next × List (Label n))
    (member : final ∈ Trace (f <$> client) past) :
    ∃ middle ∈ Trace client past, final = (f middle.1, middle.2) := by
  simp only [Trace, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at member
  obtain ⟨middle, inner, rfl⟩ := member
  exact ⟨middle, inner, rfl⟩

/-- Lifting a local program keeps its lookup history and every pre-query obligation. -/
theorem localLift_safe {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (past : List (Label n)) (safe : LocalSafe client past) :
    ServiceSafe (simulateQ PqxdhRecordLiftProtocol.localLift client) past := by
  induction client using OracleComp.inductionOn generalizing past with
  | pure value => trivial
  | query_bind query next ih =>
      rw [localSafe_query_bind] at safe
      simp only [simulateQ_bind, simulateQ_spec_query]
      rcases query with coordinate | (pending | pending)
      · exact (serviceSafe_query_bind _ _ _).mpr ⟨safe.1, fun reply => ih reply _ (safe.2 reply)⟩
      · exact (serviceSafe_query_bind _ _ _).mpr ⟨safe.1, fun reply => ih reply _ (safe.2 reply)⟩
      · exact (serviceSafe_query_bind _ _ _).mpr ⟨safe.1, fun reply => ih reply _ (safe.2 reply)⟩

/-- Every history reached by a lifted local program is reached by the local program itself. -/
theorem localLift_trace {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (past : List (Label n)) (final : Result × List (Label n))
    (member : final ∈ Trace (simulateQ PqxdhRecordLiftProtocol.localLift client) past) :
    final ∈ support ((simulateQ localTrack client).run past) := by
  induction client using OracleComp.inductionOn generalizing past with
  | pure value => simpa [Trace] using member
  | query_bind query next ih =>
      simp only [Trace, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member ⊢
      obtain ⟨middle, step, continued⟩ := member
      rcases query with coordinate | (pending | pending)
      all_goals
        simp only [PqxdhRecordLiftProtocol.localLift, simulateQ_spec_query, track, StateT.run, support_map,
          Set.mem_image] at step
        obtain ⟨reply, _, rfl⟩ := step
        refine ⟨(reply, _), ?_, ih reply _ continued⟩
        simp only [localTrack, StateT.run, support_map, Set.mem_image]
        exact ⟨reply, mem_support_query _ _, rfl⟩

/-- A history reached by a local program comes with a source result reachable under the original typed replies. -/
theorem localTrack_support {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (past : List (Label n)) (final : Result × List (Label n))
    (member : final ∈ support ((simulateQ localTrack client).run past)) : final.1 ∈ support client := by
  apply support_simulateQ_run'_subset localTrack client past
  rw [StateT.run'_eq, support_map]
  exact ⟨final, member, rfl⟩

open PqxdhRecordLiftWorldCompiler (StoredKernel StoredReady)

/-- A stored kernel's live references and certificate, against the lookup history. -/
abbrev Ready (past : List (Label n)) (stored : StoredKernel n) : Prop := StoredReady (historyTable past) stored

theorem ready_mono (past later : List (Label n)) (sub : past ⊆ later) (stored : StoredKernel n)
    (ready : Ready past stored) : Ready later stored :=
  PqxdhRecordLiftWorldCompiler.storedReady_mono _ _ (historyTable_mono past later sub) stored ready

/-- A hidden or caller-known receive is available on every reply path and returns a ready kernel of the same origin. -/
theorem kernelReceive_history (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (past : List (Label n)) (ready : Ready past stored) :
    ServiceSafe (PqxdhRecordLiftProtocol.kernelReceive stored target context) past ∧
      ∀ result ∈ Trace (PqxdhRecordLiftProtocol.kernelReceive stored target context) past,
        Ready result.2 result.1.1 ∧ past ⊆ result.2 := by
  cases stored with
  | known kernel =>
      refine ⟨(serviceSafe_query_bind _ _ _).mpr ⟨trivial, fun _ => trivial⟩, fun result member => ?_⟩
      obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
      simp only [Trace, simulateQ_spec_query, track, StateT.run, support_map, Set.mem_image] at step
      obtain ⟨reply, _, rfl⟩ := step
      subst result
      exact ⟨trivial, fun _ member => List.mem_append_left _ member⟩
  | hidden slot kernel =>
      have localFacts := receive_history kernel target _ (PqxdhFirstRecordReplay.begin_admitted kernel target context
        ready.2.1.capacity) past ⟨begin_available _ kernel ready.1.1 target context,
          begin_present _ kernel ready.1.2 target context⟩
      refine ⟨serviceSafe_bind _ _ past (localLift_safe _ past localFacts.1) (fun _ _ => trivial),
        fun result member => ?_⟩
      obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
      subst result
      have tracked := localLift_trace _ past middle step
      have refs := localFacts.2 middle tracked
      have facts := PqxdhRecordLiftProtocolHistory.admitted_receive_facts kernel target context ready.2 middle.1
        (localTrack_support _ past middle tracked)
      exact ⟨⟨refs.1, facts.1⟩, refs.2⟩

/-- A hidden or caller-known send is available on every reply path and returns a ready kernel of the same origin. -/
theorem kernelSend_history (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (past : List (Label n)) (ready : Ready past stored) :
    ServiceSafe (PqxdhRecordLiftProtocol.kernelSend stored context) past ∧
      ∀ result ∈ Trace (PqxdhRecordLiftProtocol.kernelSend stored context) past,
        Ready result.2 result.1.1 ∧ past ⊆ result.2 := by
  cases stored with
  | known kernel =>
      refine ⟨(serviceSafe_query_bind _ _ _).mpr ⟨trivial, fun _ => trivial⟩, fun result member => ?_⟩
      obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
      simp only [Trace, simulateQ_spec_query, track, StateT.run, support_map, Set.mem_image] at step
      obtain ⟨reply, _, rfl⟩ := step
      subst result
      exact ⟨trivial, fun _ member => List.mem_append_left _ member⟩
  | hidden slot kernel =>
      have localFacts := send_history _ past (send_begin_references _ kernel ready.1 context)
      refine ⟨serviceSafe_bind _ _ past (localLift_safe _ past localFacts.1) (fun _ _ => trivial),
        fun result member => ?_⟩
      obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
      subst result
      have tracked := localLift_trace _ past middle step
      have refs := localFacts.2 middle tracked
      have facts := PqxdhRecordLiftProtocolHistory.admitted_send_facts kernel context ready.2 middle.1
        (localTrack_support _ past middle tracked)
      exact ⟨⟨refs.1, facts.1⟩, refs.2⟩

open PqxdhRecordLiftWorldCompiler (Owner)

/-- An unchanged owner after a pure step. -/
theorem trace_pure_member {Result : Type} (value : Result) (past : List (Label n)) (result : Result × List (Label n))
    (member : result ∈ Trace (pure value : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) past) :
    result = (value, past) := by
  simpa [Trace] using member

/-- An owner's send or receive is available on every reply path and keeps the owner's kernel ready. -/
theorem ownerStep_history (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (past : List (Label n))
    (ready : Ready past owner.kernel) :
    ServiceSafe (PqxdhRecordLiftProtocol.ownerStep sender decode query owner) past ∧
      ∀ result ∈ Trace (PqxdhRecordLiftProtocol.ownerStep sender decode query owner) past,
        Ready result.2 result.1.2.kernel ∧ past ⊆ result.2 := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend]
      split
      · refine ⟨trivial, fun result member => ?_⟩
        rw [trace_pure_member _ past result member]
        exact ⟨ready, fun _ member => member⟩
      · have kernel := kernelSend_history owner.kernel ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩
          past ready
        refine ⟨serviceSafe_bind _ _ past kernel.1 (fun _ _ => trivial), fun result member => ?_⟩
        obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
        rw [trace_pure_member _ _ result final]
        exact kernel.2 middle step
  | inr raw =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive]
      split
      · refine ⟨trivial, fun result member => ?_⟩
        rw [trace_pure_member _ past result member]
        exact ⟨ready, fun _ member => member⟩
      · split
        · refine ⟨trivial, fun result member => ?_⟩
          rw [trace_pure_member _ past result member]
          exact ⟨ready, fun _ member => member⟩
        · rename_i frame _
          split
          · have kernel := kernelReceive_history owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩ past ready
            refine ⟨serviceSafe_bind _ _ past kernel.1 (fun _ _ => trivial), fun result member => ?_⟩
            obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
            rw [trace_pure_member _ _ result final]
            exact kernel.2 middle step
          · refine ⟨trivial, fun result member => ?_⟩
            rw [trace_pure_member _ past result member]
            exact ⟨ready, fun _ member => member⟩

/-- Publication adds no lookup and keeps the owner step's facts. -/
theorem ownerRun_history (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (past : List (Label n)) (ready : Ready past owner.kernel) :
    ServiceSafe (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner) past ∧
      ∀ result ∈ Trace (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner) past,
        Ready result.2 result.1.2.kernel ∧ past ⊆ result.2 := by
  have step := ownerStep_history sender decode query owner past ready
  refine ⟨serviceSafe_bind _ _ past step.1 (fun _ _ => (serviceSafe_query_bind _ _ _).mpr ⟨trivial, fun _ => trivial⟩),
    fun result member => ?_⟩
  obtain ⟨middle, first, rest⟩ := trace_bind _ _ past result member
  obtain ⟨published, publishStep, final⟩ := trace_bind _ _ _ result rest
  simp only [Trace, simulateQ_spec_query, track, StateT.run, support_map, Set.mem_image] at publishStep
  obtain ⟨reply, _, rfl⟩ := publishStep
  rw [trace_pure_member _ _ result final]
  have facts := step.2 middle first
  simp only [lookupCoordinates, List.append_nil]
  exact facts

/-! ### The client's control under every reply -/

/-- Every stored kernel of the client's control is ready against the lookup history. -/
def ControlReady (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n)) : Prop :=
  (∀ server, control.server = some server → ∀ keyId peer, server.peers keyId = some peer → Ready past peer.kernel) ∧
    (∀ phase ∈ control.owners, match phase with
      | .inactive _ => True
      | .established _ kernel => Ready past kernel)

theorem controlReady_mono (control : PqxdhRecordLiftProtocol.Control n) (past later : List (Label n))
    (sub : past ⊆ later) (ready : ControlReady control past) : ControlReady control later := by
  refine ⟨fun server found keyId peer present => ready_mono past later sub _ (ready.1 server found keyId peer present),
    fun phase member => ?_⟩
  have old := ready.2 phase member
  cases phase with
  | inactive _ => trivial
  | established _ kernel => exact ready_mono past later sub kernel old

theorem controlReady_server (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (ready : ControlReady control past) (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n)
    (added : Ready past peer.kernel) (attempts : Nat) :
    ControlReady { control with server := some { server with
      peers := Function.update server.peers keyId (some peer), rawAttempts := attempts } } past := by
  refine ⟨fun selected found target stored present => ?_, ready.2⟩
  simp only [Option.some.injEq] at found
  subst selected
  change Function.update server.peers keyId (some peer) target = some stored at present
  by_cases same : target = keyId
  · subst target
    rw [Function.update_self] at present
    cases Option.some.inj present
    exact added
  · rw [Function.update_of_ne same] at present
    exact ready.1 server existing target stored present

theorem controlReady_owner (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (ready : ControlReady control past) (owner : Nat) (phase : PqxdhRecordLiftWorldCompiler.Phase n)
    (added : match phase with | .inactive _ => True | .established _ kernel => Ready past kernel)
    (raw : Nat → Nat) :
    ControlReady { control with owners := control.owners.set owner phase, ownerRaw := raw } past := by
  refine ⟨ready.1, fun selected member => ?_⟩
  rcases List.mem_or_eq_of_mem_set member with prior | equal
  · exact ready.2 selected prior
  · subst selected
    exact added

theorem controlReady_attempts (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (ready : ControlReady control past) (attempts : Nat) :
    ControlReady { control with server := some { server with rawAttempts := attempts } } past := by
  refine ⟨fun selected found target stored present => ?_, ready.2⟩
  simp only [Option.some.injEq] at found
  subst selected
  exact ready.1 server existing target stored present

/-- A Server request is available on every reply path and keeps every stored kernel ready. -/
theorem serverStep_history (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (past : List (Label n)) (ready : ControlReady control past) :
    ServiceSafe ((PqxdhRecordLiftProtocol.serverStep decode route query).run control) past ∧
      ∀ result ∈ Trace ((PqxdhRecordLiftProtocol.serverStep decode route query).run control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  change ServiceSafe (PqxdhRecordLiftProtocol.serverStep decode route query control) past ∧
    ∀ result ∈ Trace (PqxdhRecordLiftProtocol.serverStep decode route query control) past,
      ControlReady result.1.2 result.2 ∧ past ⊆ result.2
  unfold PqxdhRecordLiftProtocol.serverStep
  cases existing : control.server with
  | none =>
      cases query <;>
        exact ⟨trivial, fun result member => by
          rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
  | some server =>
      dsimp only
      rcases query with ⟨plaintext, keyId⟩ | raw
      · dsimp only
        cases present : server.peers keyId with
        | none =>
            exact ⟨trivial, fun result member => by
              rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
        | some peer =>
            have owner := ownerRun_history (PqxdhDeploymentNative.serverTag (.inl (plaintext, keyId))) server.sender
              decode (.inl plaintext) (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) past
              (ready.1 server existing keyId peer present)
            refine ⟨serviceSafe_bind _ _ past owner.1 (fun _ _ => trivial), fun result member => ?_⟩
            obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
            rw [trace_pure_member _ _ result final]
            have facts := owner.2 middle step
            exact ⟨controlReady_server control _ server existing
              (controlReady_mono control past _ facts.2 ready) keyId _ facts.1 _, facts.2⟩
      · dsimp only
        cases routed : route raw with
        | none =>
            exact ⟨trivial, fun result member => by
              rw [trace_pure_member _ past result member]
              exact ⟨controlReady_attempts control past server existing ready _, fun _ member => member⟩⟩
        | some keyId =>
            dsimp only
            cases present : server.peers keyId with
            | none =>
                exact ⟨trivial, fun result member => by
                  rw [trace_pure_member _ past result member]
                  exact ⟨controlReady_attempts control past server existing ready _, fun _ member => member⟩⟩
            | some peer =>
                have owner := ownerRun_history (PqxdhDeploymentNative.serverTag (.inr raw)) server.sender
                  decode (.inr raw) (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) past
                  (ready.1 server existing keyId peer present)
                refine ⟨serviceSafe_bind _ _ past owner.1 (fun _ _ => trivial), fun result member => ?_⟩
                obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
                rw [trace_pure_member _ _ result final]
                have facts := owner.2 middle step
                exact ⟨controlReady_server control _ server existing
                  (controlReady_mono control past _ facts.2 ready) keyId _ facts.1 _, facts.2⟩

/-- A Beacon request is available on every reply path and keeps every stored kernel ready. -/
theorem beaconStep_history (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (past : List (Label n)) (ready : ControlReady control past) :
    ServiceSafe ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run control) past ∧
      ∀ result ∈ Trace ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  change ServiceSafe (PqxdhRecordLiftProtocol.beaconStep decode owner query control) past ∧
    ∀ result ∈ Trace (PqxdhRecordLiftProtocol.beaconStep decode owner query control) past,
      ControlReady result.1.2 result.2 ∧ past ⊆ result.2
  unfold PqxdhRecordLiftProtocol.beaconStep
  cases selected : control.owners[owner]? with
  | none =>
      exact ⟨trivial, fun result member => by
        rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            exact ⟨trivial, fun result member => by
              rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
      | established shell kernel =>
          have stored : Ready past kernel := by
            have := ready.2 _ (List.mem_of_getElem? selected)
            exact this
          have run := ownerRun_history (PqxdhDeploymentNative.beaconTag owner) shell.identityKeyId decode query
            (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (control.ownerRaw owner)) past stored
          dsimp only
          refine ⟨serviceSafe_bind _ _ past run.1 (fun _ _ => trivial), fun result member => ?_⟩
          obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
          rw [trace_pure_member _ _ result final]
          have facts := run.2 middle step
          exact ⟨controlReady_owner control _ (controlReady_mono control past _ facts.2 ready) owner
            (.established shell middle.1.2.kernel) facts.1 _, facts.2⟩

theorem controlReady_markUsed (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (role : Role) (ref : PqxdhRecordLiftInterface.KernelRef n) (ready : ControlReady control past) :
    ControlReady (PqxdhRecordLiftProtocol.markUsed control role ref) past := by
  cases ref <;> exact ready

theorem controlReady_congr (control other : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (server : other.server = control.server) (owners : other.owners = control.owners)
    (ready : ControlReady control past) : ControlReady other past := by
  unfold ControlReady
  rw [server, owners]
  exact ready

theorem markUsed_server (control : PqxdhRecordLiftProtocol.Control n) (role : Role)
    (ref : PqxdhRecordLiftInterface.KernelRef n) :
    (PqxdhRecordLiftProtocol.markUsed control role ref).server = control.server := by
  cases ref <;> rfl

theorem controlReady_peers (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (ready : ControlReady control past) (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n)
    (added : Ready past peer.kernel) :
    ControlReady { control with server := some { server with
      peers := Function.update server.peers keyId (some peer) } } past := by
  refine ⟨fun selected found target stored present => ?_, ready.2⟩
  simp only [Option.some.injEq] at found
  subst selected
  change Function.update server.peers keyId (some peer) target = some stored at present
  by_cases same : target = keyId
  · subst target
    rw [Function.update_self] at present
    cases Option.some.inj present
    exact added
  · rw [Function.update_of_ne same] at present
    exact ready.1 server existing target stored present

/-- Resolving a kernel reference allocates at most a seed and returns a ready kernel. -/
theorem resolve_history (role : Role) (ref : PqxdhRecordLiftInterface.KernelRef n) (past : List (Label n)) :
    ServiceSafe (PqxdhRecordLiftProtocol.resolve role ref) past ∧
      ∀ result ∈ Trace (PqxdhRecordLiftProtocol.resolve role ref) past, Ready result.2 result.1 ∧ result.2 = past := by
  cases ref with
  | known kernel =>
      exact ⟨trivial, fun result member => by
        rw [trace_pure_member _ past result member]; exact ⟨trivial, rfl⟩⟩
  | hidden slot =>
      refine ⟨(serviceSafe_query_bind _ _ _).mpr ⟨trivial, fun _ => trivial⟩, fun result member => ?_⟩
      obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_spec_query, track, StateT.run, support_map, Set.mem_image] at step
      obtain ⟨reply, _, rfl⟩ := step
      rw [trace_pure_member _ _ result final]
      exact ⟨PqxdhRecordLiftWorldCompiler.labeledKernel_ready _ role slot, by simp [lookupCoordinates]⟩

/-- Every capability is available on every reply path and keeps every stored kernel ready. -/
theorem capability_history (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (past : List (Label n)) (ready : ControlReady control past) :
    ServiceSafe ((PqxdhRecordLiftProtocol.capability query).run control) past ∧
      ∀ result ∈ Trace ((PqxdhRecordLiftProtocol.capability query).run control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  have unchanged : ∀ {Result : Type} (value : Result),
      ServiceSafe (pure (value, control) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) past ∧
        ∀ result ∈ Trace (pure (value, control) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) past,
          ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := fun value =>
    ⟨trivial, fun result member => by
      rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
  cases query with
  | peerPresent keyId => exact unchanged _
  | ownerPresent owner => exact unchanged _
  | appendOwner sender pin phase =>
      refine ⟨trivial, fun result member => ?_⟩
      rw [trace_pure_member _ past result member]
      refine ⟨⟨ready.1, fun selected found => ?_⟩, fun _ member => member⟩
      rcases List.mem_append.mp found with prior | added
      · exact ready.2 selected prior
      · rw [List.mem_singleton] at added
        subst selected
        trivial
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability, StateT.run]
      split
      · split
        · refine ⟨trivial, fun result member => ?_⟩
          rw [trace_pure_member _ past result member]
          exact ⟨controlReady_owner control past ready owner (.inactive phase) trivial control.ownerRaw,
            fun _ member => member⟩
        · exact unchanged _
      · exact unchanged _
  | installServer keyId identity ref =>
      change ServiceSafe (PqxdhRecordLiftProtocol.installServer keyId identity ref control) past ∧
        ∀ result ∈ Trace (PqxdhRecordLiftProtocol.installServer keyId identity ref control) past,
          ControlReady result.1.2 result.2 ∧ past ⊆ result.2
      unfold PqxdhRecordLiftProtocol.installServer
      cases existing : control.server with
      | none => exact unchanged _
      | some server =>
          dsimp only
          split
          · have resolved := resolve_history .server ref past
            refine ⟨serviceSafe_bind _ _ past resolved.1 (fun _ _ => trivial), fun result member => ?_⟩
            obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
            rw [trace_pure_member _ _ result final]
            obtain ⟨stored, same⟩ := resolved.2 middle step
            rw [same] at stored ⊢
            exact ⟨controlReady_peers (PqxdhRecordLiftProtocol.markUsed control .server ref) past server
              ((markUsed_server control .server ref).trans existing) (controlReady_markUsed control past .server ref ready)
              keyId _ stored, fun _ member => member⟩
          · exact unchanged _
  | installBeacon owner shell ref =>
      change ServiceSafe (PqxdhRecordLiftProtocol.installBeacon owner shell ref control) past ∧
        ∀ result ∈ Trace (PqxdhRecordLiftProtocol.installBeacon owner shell ref control) past,
          ControlReady result.1.2 result.2 ∧ past ⊆ result.2
      unfold PqxdhRecordLiftProtocol.installBeacon
      split
      · have resolved := resolve_history .beacon ref past
        refine ⟨serviceSafe_bind _ _ past resolved.1 (fun _ _ => trivial), fun result member => ?_⟩
        obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
        rw [trace_pure_member _ _ result final]
        obtain ⟨stored, same⟩ := resolved.2 middle step
        rw [same] at stored ⊢
        have updated := controlReady_owner control past ready owner (.established shell middle.1) stored
          control.ownerRaw
        exact ⟨controlReady_congr _ _ past (by exact markUsed_server control .beacon ref) (by rfl) updated,
          fun _ member => member⟩
      · exact unchanged _
  | hash bytes =>
      refine ⟨(serviceSafe_query_bind _ _ _).mpr ⟨trivial, fun _ => trivial⟩, fun result member => ?_⟩
      obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_spec_query, track, StateT.run, support_map, Set.mem_image] at step
      obtain ⟨reply, _, rfl⟩ := step
      rw [trace_pure_member _ _ result final]
      simp only [lookupCoordinates, List.append_nil]
      exact ⟨ready, fun _ member => member⟩

/-- Charging and forwarding an environment effect is available on every reply path and keeps every stored kernel ready. -/
theorem effects_history (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (past : List (Label n)) (ready : ControlReady control past) :
    ServiceSafe ((PqxdhRecordLiftProtocol.effects query).run control) past ∧
      ∀ result ∈ Trace ((PqxdhRecordLiftProtocol.effects query).run control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  have charged : ∀ (query' : PqxdhRecordLiftProtocol.Service n) {Result : Type}
      (rest : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query' → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
      (post : Result × List (Label n) → Prop), lookupCoordinates query' = [] → Avail past query' →
      (∀ reply, ServiceSafe (rest reply) past ∧ ∀ result ∈ Trace (rest reply) past, post result) →
      ServiceSafe ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query') :
        OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= rest) past ∧
        ∀ result ∈ Trace ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query') :
          OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= rest) past, post result := by
    intro query' Result rest post noLookup avail continued
    refine ⟨(serviceSafe_query_bind _ _ _).mpr ⟨avail, fun reply => ?_⟩, fun result member => ?_⟩
    · simpa only [noLookup, List.append_nil] using (continued reply).1
    · obtain ⟨middle, step, final⟩ := trace_bind _ _ past result member
      simp only [Trace, simulateQ_spec_query, track, StateT.run, support_map, Set.mem_image] at step
      obtain ⟨reply, _, rfl⟩ := step
      simp only [noLookup, List.append_nil] at final
      exact (continued reply).2 result final
  refine charged _ _ _ rfl (by exact trivial) ?_
  intro _
  cases query with
  | inl coin =>
      refine charged _ _ _ rfl (by exact trivial) ?_
      intro _
      exact ⟨trivial, fun result member => by
        rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
  | inr request => exact capability_history request control past ready

/-- Server initialization imports only caller-known peers. -/
theorem initializeServer_history (created : PqxdhLiveServerConstruction.Created Unit)
    (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n)) (ready : ControlReady control past) :
    ServiceSafe ((PqxdhRecordLiftProtocol.initializeServer created).run control) past ∧
      ∀ result ∈ Trace ((PqxdhRecordLiftProtocol.initializeServer created).run control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  change ServiceSafe (PqxdhRecordLiftProtocol.initializeServer created control) past ∧
    ∀ result ∈ Trace (PqxdhRecordLiftProtocol.initializeServer created control) past,
      ControlReady result.1.2 result.2 ∧ past ⊆ result.2
  unfold PqxdhRecordLiftProtocol.initializeServer
  cases existing : control.server with
  | some _ =>
      exact ⟨trivial, fun result member => by
        rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
  | none =>
      refine ⟨trivial, fun result member => ?_⟩
      rw [trace_pure_member _ past result member]
      refine ⟨⟨fun server found keyId peer present => ?_, ready.2⟩, fun _ member => member⟩
      simp only [Option.some.injEq] at found
      subst server
      simp only [PqxdhRecordLiftWorldCompiler.Server.fromKnown, Option.map_eq_some_iff] at present
      obtain ⟨known, _, rfl⟩ := present
      trivial

/-- Every World request is available on every reply path and keeps every stored kernel ready. -/
theorem handler_history (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n))
    (ready : ControlReady control past) :
    ServiceSafe ((PqxdhRecordLiftProtocol.handler decode route query).run control) past ∧
      ∀ result ∈ Trace ((PqxdhRecordLiftProtocol.handler decode route query).run control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  rcases query with created | (effect | ((send | raw) | ⟨owner, plaintext | raw⟩))
  · exact initializeServer_history created control past ready
  · exact effects_history effect control past ready
  · exact serverStep_history decode route (.inl send) control past ready
  · exact serverStep_history decode route (.inr raw) control past ready
  · exact beaconStep_history decode owner (.inl plaintext) control past ready
  · exact beaconStep_history decode owner (.inr raw) control past ready

/-- Every adaptive schedule is available on every reply path, from every ready control. -/
theorem schedule_history {Result : Type} (decode : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (control : PqxdhRecordLiftProtocol.Control n) (past : List (Label n)) (ready : ControlReady control past) :
    ServiceSafe (PqxdhRecordLiftProtocol.schedule decode route client control) past ∧
      ∀ result ∈ Trace (PqxdhRecordLiftProtocol.schedule decode route client control) past,
        ControlReady result.1.2 result.2 ∧ past ⊆ result.2 := by
  unfold PqxdhRecordLiftProtocol.schedule
  induction client using OracleComp.inductionOn generalizing control past with
  | pure value =>
      exact ⟨trivial, fun result member => by
        simp only [simulateQ_pure, StateT.run_pure] at member
        rw [trace_pure_member _ past result member]; exact ⟨ready, fun _ member => member⟩⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have step := handler_history decode route query control past ready
      refine ⟨serviceSafe_bind _ _ past step.1 (fun middle member => (ih middle.1.1 middle.1.2 middle.2
        (step.2 middle member).1).1), fun result member => ?_⟩
      obtain ⟨middle, first, rest⟩ := trace_bind _ _ past result member
      have facts := step.2 middle first
      have later := (ih middle.1.1 middle.1.2 middle.2 facts.1).2 result rest
      exact ⟨later.1, fun label member => later.2 (facts.2 member)⟩

/-- The initial control is ready against the empty lookup history. -/
theorem initial_ready : ControlReady (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n) [] := by
  refine ⟨fun server found => ?_, fun phase member => ?_⟩
  · cases found
  · cases member

/-- On every reply path of the frozen program, every lookup has its predecessor in the lookup history and every hidden opening and seal is at a coordinate looked up before. -/
theorem program_history {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ServiceSafe (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary) [] :=
  (schedule_history codec.frameRead route _ PqxdhRecordLiftProtocol.initialControl [] initial_ready).1

/-! ### The lookup bill of the program -/

open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_mono weighted_indicator weighted_simulate
  weighted_run weighted_add)

/-- One unit per private lookup request. -/
def lookupCost : PqxdhRecordLiftProtocol.Service n → Nat
  | .lookup _ => 1
  | _ => 0

/-- A lifted local program is billed exactly for its local lookups. -/
theorem localLift_lookups {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (bound : Nat) [DecidablePred (fun query : (PqxdhRecordLiftProtocol.LocalSpec n).Domain =>
      PqxdhRecordLiftOpaqueBounds.IsLookup query)]
    (bounded : client.IsQueryBoundP (fun query => PqxdhRecordLiftOpaqueBounds.IsLookup query) bound) :
    Weighted lookupCost (simulateQ PqxdhRecordLiftProtocol.localLift client) bound := by
  have indicated := weighted_indicator (spec := PqxdhRecordLiftProtocol.LocalSpec n)
    (fun query => PqxdhRecordLiftOpaqueBounds.IsLookup query) 1 client bound bounded
  rw [Nat.one_mul] at indicated
  apply weighted_simulate _ _ _ _ _ indicated
  intro query
  rcases query with coordinate | (pending | pending) <;>
    simp [Weighted, PqxdhRecordLiftProtocol.localLift, lookupCost, PqxdhRecordLiftOpaqueBounds.IsLookup]

/-- A single service request is billed for its own lookup only. -/
theorem query_lookups (query : PqxdhRecordLiftProtocol.Service n) :
    Weighted lookupCost ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) :
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _)) (lookupCost query) := by
  simp [Weighted]

theorem kernelReceive_lookups (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Weighted lookupCost (PqxdhRecordLiftProtocol.kernelReceive stored target context) 51 := by
  cases stored with
  | known kernel =>
      exact weighted_mono _ _ _ _ (weighted_bind _ _ _ 0 0 (query_lookups _) (fun _ => trivial)) (by omega)
  | hidden slot kernel =>
      classical
      exact weighted_mono _ _ _ _ (weighted_bind _ _ _ 51 0 (localLift_lookups _ 51
        (PqxdhRecordLiftOpaqueBounds.admitted_receive_lookup kernel target context)) (fun _ => trivial)) (by omega)

theorem kernelSend_lookups (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext) :
    Weighted lookupCost (PqxdhRecordLiftProtocol.kernelSend stored context) 1 := by
  cases stored with
  | known kernel =>
      exact weighted_mono _ _ _ _ (weighted_bind _ _ _ 0 0 (query_lookups _) (fun _ => trivial)) (by omega)
  | hidden slot kernel =>
      classical
      exact weighted_mono _ _ _ _ (weighted_bind _ _ _ 1 0 (localLift_lookups _ 1
        (PqxdhRecordLiftOpaqueBounds.admitted_send_lookup kernel context)) (fun _ => trivial)) (by omega)

/-- The lookup bill of one owner request: one for a send, 51 for a receive. -/
def ownerLookups (query : RawCtxMixedOwner.SourceSpec.Domain) : Nat := if query.isLeft then 1 else 51

theorem ownerRun_lookups (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    Weighted lookupCost (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner) (ownerLookups query) := by
  have step : Weighted lookupCost (PqxdhRecordLiftProtocol.ownerStep sender decode query owner) (ownerLookups query) := by
    cases query with
    | inl plaintext =>
        simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend, ownerLookups]
        split
        · trivial
        · exact weighted_mono _ _ _ _ (weighted_bind _ _ _ 1 0 (kernelSend_lookups _ _) (fun _ => trivial)) (by simp)
    | inr raw =>
        simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive, ownerLookups]
        split
        · trivial
        · split
          · trivial
          · split
            · exact weighted_mono _ _ _ _ (weighted_bind _ _ _ 51 0 (kernelReceive_lookups _ _ _) (fun _ => trivial))
                (by simp)
            · trivial
  exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0 step (fun _ =>
    weighted_mono _ _ _ _ (weighted_bind _ _ _ 0 0 (query_lookups _) (fun _ => trivial)) (by omega))) (by omega)

/-- The lookup bill of one World request: one per record send, 51 per raw receive, none otherwise. -/
def worldLookups (query : (WorldSpec n).Domain) : Nat :=
  if PqxdhRecordLiftBudget.WorldRecord .send query then 1
  else if PqxdhRecordLiftBudget.WorldRecord .raw query then 51 else 0


theorem resolve_lookups (role : Role) (ref : PqxdhRecordLiftInterface.KernelRef n) :
    Weighted lookupCost (PqxdhRecordLiftProtocol.resolve role ref) 0 := by
  cases ref <;> simp [PqxdhRecordLiftProtocol.resolve, Weighted, lookupCost]

theorem capability_lookups (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted lookupCost ((PqxdhRecordLiftProtocol.capability query).run control) 0 := by
  cases query with
  | installServer keyId identity ref =>
      change Weighted lookupCost (PqxdhRecordLiftProtocol.installServer keyId identity ref control) 0
      unfold PqxdhRecordLiftProtocol.installServer
      split
      · trivial
      · split
        · exact weighted_bind _ _ _ 0 0 (resolve_lookups _ _) (fun _ => trivial)
        · trivial
  | installBeacon owner shell ref =>
      change Weighted lookupCost (PqxdhRecordLiftProtocol.installBeacon owner shell ref control) 0
      unfold PqxdhRecordLiftProtocol.installBeacon
      split
      · exact weighted_bind _ _ _ 0 0 (resolve_lookups _ _) (fun _ => trivial)
      · trivial
  | advanceOwner owner phase =>
      change Weighted lookupCost (PqxdhRecordLiftProtocol.capability (.advanceOwner owner phase) control) 0
      simp only [PqxdhRecordLiftProtocol.capability]
      split
      · split <;> trivial
      · trivial
  | hash bytes => simp [PqxdhRecordLiftProtocol.capability, Weighted, lookupCost, StateT.run_lift]
  | _ => trivial

theorem effects_lookups (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted lookupCost ((PqxdhRecordLiftProtocol.effects query).run control) 0 := by
  rcases query with coin | request
  · simp [PqxdhRecordLiftProtocol.effects, Weighted, lookupCost, StateT.run_bind, StateT.run_lift]
  · simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    exact weighted_bind _ _ _ 0 0 (by simp [Weighted, lookupCost]) (fun _ => capability_lookups _ _)

theorem serverStep_lookups (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted lookupCost ((PqxdhRecordLiftProtocol.serverStep decode route query).run control)
      (if query.isLeft then 1 else 51) := by
  change Weighted lookupCost (PqxdhRecordLiftProtocol.serverStep decode route query control) _
  unfold PqxdhRecordLiftProtocol.serverStep
  cases existing : control.server with
  | none => cases query <;> trivial
  | some server =>
      dsimp only
      rcases query with ⟨plaintext, keyId⟩ | raw
      · dsimp only
        cases present : server.peers keyId with
        | none => trivial
        | some peer =>
            exact weighted_bind _ _ _ 1 0 (ownerRun_lookups _ _ _ (.inl plaintext) _) (fun _ => trivial)
      · dsimp only
        cases routed : route raw with
        | none => trivial
        | some keyId =>
            dsimp only
            cases present : server.peers keyId with
            | none => trivial
            | some peer =>
                exact weighted_bind _ _ _ 51 0 (ownerRun_lookups _ _ _ (.inr raw) _) (fun _ => trivial)

theorem beaconStep_lookups (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted lookupCost ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run control) (ownerLookups query) := by
  change Weighted lookupCost (PqxdhRecordLiftProtocol.beaconStep decode owner query control) _
  unfold PqxdhRecordLiftProtocol.beaconStep
  cases selected : control.owners[owner]? with
  | none => trivial
  | some phase =>
      cases phase with
      | inactive phase => cases query <;> trivial
      | established shell kernel =>
          exact weighted_mono _ _ _ _ (weighted_bind _ _ _ _ 0 (ownerRun_lookups _ _ _ query _) (fun _ => trivial))
            (by omega)

/-- One World request performs at most its `worldLookups` private lookups. -/
theorem handler_lookups (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Weighted lookupCost ((PqxdhRecordLiftProtocol.handler decode route query).run control) (worldLookups query) := by
  rcases query with created | query
  · change Weighted lookupCost (PqxdhRecordLiftProtocol.initializeServer created control) _
    unfold PqxdhRecordLiftProtocol.initializeServer
    split <;> trivial
  · rcases query with effect | record
    · exact weighted_mono _ _ _ _ (effects_lookups effect control) (Nat.zero_le _)
    · rcases record with (send | raw) | ⟨owner, plaintext | raw⟩
      · rw [show worldLookups (n := n) (.inr (.inr (.inl (.inl send)))) = 1 by
          simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord, PqxdhRecordLiftBudget.recordKind]]
        exact serverStep_lookups decode route (.inl send) control
      · rw [show worldLookups (n := n) (.inr (.inr (.inl (.inr raw)))) = 51 by
          simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord, PqxdhRecordLiftBudget.recordKind]]
        exact serverStep_lookups decode route (.inr raw) control
      · rw [show worldLookups (n := n) (.inr (.inr (.inr (owner, .inl plaintext)))) = 1 by
          simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord, PqxdhRecordLiftBudget.recordKind]]
        exact beaconStep_lookups decode owner (.inl plaintext) control
      · rw [show worldLookups (n := n) (.inr (.inr (.inr (owner, .inr raw)))) = 51 by
          simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord, PqxdhRecordLiftBudget.recordKind]]
        exact beaconStep_lookups decode owner (.inr raw) control

/-- The World program's lookup weight is at most one per send and 51 per raw receive. -/
theorem world_lookups {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (budget : PqxdhDeploymentInterface.Budget)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (respects : budget.Respects adversary) :
    Weighted worldLookups (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary)
      (PqxdhRecordLiftIdeal.positions budget) := by
  have sends := weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .send) 1 _ _
    (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget adversary respects .send)
  have raws := weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .raw) 51 _ _
    (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget adversary respects .raw)
  have joint := weighted_add _ _ _ _ _ sends raws
  have cost : (fun query => (if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0) +
      (if PqxdhRecordLiftBudget.WorldRecord .raw query then 51 else 0)) = (worldLookups : (WorldSpec n).Domain → Nat) := by
    funext query
    rcases query with _ | _ | record
    · simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord]
    · simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord]
    · cases kind : PqxdhRecordLiftBudget.recordKind record <;>
        simp [worldLookups, PqxdhRecordLiftBudget.WorldRecord, kind]
  rw [cost] at joint
  simpa [PqxdhRecordLiftIdeal.positions, PqxdhRecordLiftBudget.recordBudget] using joint

/-- The compiled protocol program performs at most `positions budget` private lookups. -/
theorem program_lookups {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (budget : PqxdhDeploymentInterface.Budget)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (respects : budget.Respects adversary) :
    Weighted lookupCost (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordLiftIdeal.positions budget) :=
  weighted_run worldLookups lookupCost _ _ _ _
    (world_lookups env crypto codec serverKid bounds mode budget adversary respects)
    (fun query control => handler_lookups codec.frameRead route query control)

/-! ### Transfer to every CTX world -/

/-- A lookup request is billed exactly for the coordinates it records. -/
theorem lookupCoordinates_length (query : PqxdhRecordLiftProtocol.Service n) :
    (lookupCoordinates query).length = lookupCost query := by
  cases query <;> rfl

/-- Appending an available lookup keeps the history table's depth within the history's length. -/
theorem history_depth (past : List (Label n)) (depth : PqxdhRecordLiftChainOrder.DepthBound (historyTable past) past.length)
    (query : PqxdhRecordLiftProtocol.Service n) (avail : Avail past query) :
    PqxdhRecordLiftChainOrder.DepthBound (historyTable (past ++ lookupCoordinates query))
      (past ++ lookupCoordinates query).length := by
  cases query with
  | lookup coordinate =>
      intro entry output found
      have member : entry ∈ past ++ [coordinate] := (historyTable_present _ entry).mp ⟨output, found⟩
      simp only [List.length_append]
      rcases List.mem_append.mp member with old | new
      · exact PqxdhRecordLiftChainOrder.bounded_mono entry
          (depth entry fallbackOutput (by simp [historyTable, old])) (Nat.le_succ _)
      · rw [List.mem_singleton.mp new]
        exact PqxdhRecordLiftChainOrder.available_bounded _ _ depth coordinate avail
  | _ => simpa [lookupCoordinates] using depth

/-- Every coordinate of a depth-bounded history is bounded by any larger budget. -/
theorem history_bounded (past : List (Label n)) (positions : Nat)
    (depth : PqxdhRecordLiftChainOrder.DepthBound (historyTable past) past.length) (fits : past.length ≤ positions)
    (label : Label n) (member : label ∈ past) : PqxdhRecordLiftChainOrder.Bounded positions label :=
  PqxdhRecordLiftChainOrder.bounded_mono label (depth label fallbackOutput (by simp [historyTable, member])) fits

/-- The CTX-world interpreter with an arbitrary keyed implementation. -/
noncomputable def ctxInterpreterOf (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .opening pending => fun state =>
      (simulateQ keyed (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run
        state
  | .sealing pending => fun state => do
      let result ← (simulateQ keyed ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
        state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })
  | query => onBase (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec query)

/-- The explicit-key CTX world is the generic interpreter at the explicit-key keyed implementation. -/
theorem ctxInterpreterWith_of (keyOf : KeyOf n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    ctxInterpreterWith keyOf modes replace setup codec =
      ctxInterpreterOf (keyedWith keyOf modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        replace setup codec := by
  funext query
  cases query <;> rfl

/-- The explicit-key keyed implementation never changes the chain table. -/
theorem keyedWith_chain (keyOf : KeyOf n) (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n) (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyedWith keyOf modes decode crypto query).run state)) :
    result.2.base.chain = state.base.chain := by
  simp only [keyedWith, StateT.run, PqxdhRecordLiftProtocol.sampled, bind_pure_comp, support_map,
    Set.mem_image] at supported
  obtain ⟨inner, ⟨_, _, _, rfl⟩, rfl⟩ := supported
  rfl

/-- Keyed implementations that agree on a request agree on the explicit-key requests they serve. -/
theorem keyedWith_congr (keyOf other : KeyOf n) (modes otherModes : Label n → KeyMode) (decode : RawDecoder)
    (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain) (state : CtxPrivate n)
    (sameKey : keyOf state.base.chain query.1 = other state.base.chain query.1)
    (sameMode : modes query.1 = otherModes query.1) :
    (keyedWith keyOf modes decode crypto query).run state = (keyedWith other otherModes decode crypto query).run state := by
  simp only [keyedWith, StateT.run, sameKey, sameMode]

/-- The material of an opening is unchanged by interpreting its chains. -/
theorem material_chains {Send Receive SendValue ReceiveValue Material Context : Type}
    (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (opening : RawCtxInterpretedOpening.Opening Send Receive Material Context) :
    RawCtxInterpretedOpening.material (RawCtxChainInterpretation.mapOpeningChains send receive opening) =
      RawCtxInterpretedOpening.material opening := by
  cases prepared : opening.prepared <;>
    simp only [RawCtxInterpretedOpening.material, RawCtxChainInterpretation.mapOpeningChains,
      RawCtxChainInterpretation.mapPreparedChain, prepared] <;> rfl

/-- Selected opening arguments are at the opening's material. -/
theorem openArguments_material {Material Context : Type}
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Material Context)
    (input : RawCtxInterpretedArguments.Input Material Context)
    (present : RawCtxInterpretedArguments.openArguments pending = some input) :
    RawCtxInterpretedOpening.material pending = .ok (.Some input.material) := by
  have spec := (RawCtxInterpretedArguments.material_total pending).choose_spec
  unfold RawCtxInterpretedArguments.openArguments at present
  split at present
  · cases present
  · rename_i selected chosen
    cases Option.some.inj present
    rw [spec, chosen]

/-- An opening served by two keyed implementations agreeing on its material coordinate has the same law. -/
theorem opening_congr (keyed other : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Opening n)
    (state : CtxPrivate n)
    (agree : ∀ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) →
      ∀ request, (keyed (label, request)).run state = (other (label, request)).run state) :
    (ctxInterpreterOf keyed replace setup codec (.opening pending)).run state =
      (ctxInterpreterOf other replace setup codec (.opening pending)).run state := by
  change (simulateQ keyed (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain
      pending)).run state =
    (simulateQ other (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state
  unfold hiddenOpening
  split
  · rfl
  · split
    · rfl
    · rename_i input arguments
      split
      · have selected := openArguments_material _ input arguments
        rw [material_chains] at selected
        simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
        rw [agree _ selected]
      · rfl

/-- A single keyed request followed by a pure reply has the same law under two keyed implementations agreeing on it. -/
theorem query_bind_congr {Result : Type} (keyed other : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (query : (KeyedSpec n).Domain) (next : (KeyedSpec n).Range query → OracleComp (KeyedSpec n) Result)
    (state : CtxPrivate n) (agree : (keyed query).run state = (other query).run state)
    (pureNext : ∀ reply, ∃ value, next reply = pure value) :
    (simulateQ keyed ((liftM ((KeyedSpec n).query query) : OracleComp (KeyedSpec n) _) >>= next)).run state =
      (simulateQ other ((liftM ((KeyedSpec n).query query) : OracleComp (KeyedSpec n) _) >>= next)).run state := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, agree]
  apply bind_congr
  intro reply
  obtain ⟨value, isPure⟩ := pureNext reply.1
  rw [isPure]
  simp

/-- A sealing served by two keyed implementations agreeing on its material coordinate has the same law. -/
theorem sealing_congr (keyed other : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (state : CtxPrivate n)
    (agree : ∀ request, (keyed (pending.material, request)).run state = (other (pending.material, request)).run state) :
    (ctxInterpreterOf keyed replace setup codec (.sealing pending)).run state =
      (ctxInterpreterOf other replace setup codec (.sealing pending)).run state := by
  change (do
      let result ← (simulateQ keyed ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
        state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) = (do
      let result ← (simulateQ other ((hiddenSealing codec.frameWrite state.base.chain replace pending).run
        state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } }))
  congr 1
  unfold hiddenSealing
  split
  · exact query_bind_congr keyed other _ _ state (agree _) (fun reply => by cases reply <;> exact ⟨_, rfl⟩)
  · rfl

/-- A keyed program never changes the chain table when its keyed implementation does not. -/
theorem simulate_chain (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (keep : ∀ query state, ∀ result ∈ support ((keyed query).run state), result.2.base.chain = state.base.chain)
    {Result : Type} (client : OracleComp (KeyedSpec n) Result) (state : CtxPrivate n) (result : Result × CtxPrivate n)
    (supported : result ∈ support ((simulateQ keyed client).run state)) : result.2.base.chain = state.base.chain := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, step, continued⟩ := supported
      exact (ih middle.1 middle.2 continued).trans (keep query state middle step)

/-- Every CTX-world service grows the chain table, and a lookup makes its coordinate present. -/
theorem chain_step (keyed : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (keep : ∀ query state, ∀ result ∈ support ((keyed query).run state), result.2.base.chain = state.base.chain)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreterOf keyed replace setup codec query).run state)) :
    state.base.chain ≤ result.2.base.chain ∧ ∀ label ∈ lookupCoordinates query, Present result.2.base.chain label := by
  cases query with
  | lookup coordinate =>
      rw [show ctxInterpreterOf keyed replace setup codec (.lookup coordinate) =
        ctxInterpreterWith tableKey (fun _ => .real) replace setup codec (.lookup coordinate) from rfl,
        lookup_factor, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      cases found : state.base.chain coordinate with
      | some output =>
          rw [PqxdhRecordLiftChainOracle.lookup_hit _ _ _ _ _ rfl output found, support_pure,
            Set.mem_singleton_iff] at member
          subst inner
          refine ⟨fun _ _ present => present, fun label member => ?_⟩
          simp only [lookupCoordinates, List.mem_singleton] at member
          subst label
          exact ⟨output, found⟩
      | none =>
          rw [PqxdhRecordLiftChainOracle.lookup_miss _ _ _ _ _ rfl found, support_map] at member
          obtain ⟨value, _, rfl⟩ := member
          refine ⟨fun label output present => ?_, fun label member => ?_⟩
          · have different : label ≠ coordinate := by
              rintro rfl
              rw [found] at present
              cases present
            exact (QueryCache.cacheQuery_of_ne _ _ different).trans present
          · have same : label = coordinate := by simpa only [lookupCoordinates, List.mem_singleton] using member
            rw [same]
            exact ⟨value, QueryCache.cacheQuery_self (state.base.chain : Table (Slot n)) coordinate value⟩
  | opening pending =>
      have same := simulate_chain keyed keep _ state result supported
      refine ⟨fun label output present => ?_, fun _ member => by simp [lookupCoordinates] at member⟩
      rw [same]
      exact present
  | sealing pending =>
      simp only [ctxInterpreterOf, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have same := simulate_chain keyed keep _ state inner member
      refine ⟨fun label output present => ?_, fun _ member => by simp [lookupCoordinates] at member⟩
      change inner.2.base.chain label = some output
      rw [same]
      exact present
  | _ =>
    simp only [ctxInterpreterOf, onBase, PqxdhRecordLiftProtocol.interpreter, PqxdhRecordLiftProtocol.sampled,
      PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork, PqxdhRecordLiftProtocol.putRecord,
      PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.publish, StateT.run, bind_pure_comp, support_map,
      Set.mem_image, Functor.map_map, support_pure, Set.mem_singleton_iff] at supported
    first
      | obtain ⟨_, rfl, rfl⟩ := supported
      | obtain ⟨_, _, rfl⟩ := supported
    exact ⟨fun _ _ found => found, fun _ member => by simp [lookupCoordinates] at member⟩

/-- The coordinates whose material a private service request reads: an opening's selected material and a seal's material. Each must be present in the chain table and within `positions`. -/
def Touches (positions : Nat) (table : Table (Slot n)) : PqxdhRecordLiftProtocol.Service n → Prop
  | .opening pending => ∀ label, RawCtxInterpretedOpening.material pending = .ok (.Some label) →
      Present table label ∧ PqxdhRecordLiftChainOrder.Bounded positions label
  | .sealing pending => Present table pending.material ∧ PqxdhRecordLiftChainOrder.Bounded positions pending.material
  | _ => True

/-- A request available against a present, depth-bounded history touches only present, bounded coordinates. -/
theorem touches_of_avail (positions : Nat) (table : Table (Slot n)) (past : List (Label n))
    (depth : PqxdhRecordLiftChainOrder.DepthBound (historyTable past) past.length) (fits : past.length ≤ positions)
    (present : ∀ label ∈ past, Present table label) (query : PqxdhRecordLiftProtocol.Service n)
    (avail : Avail past query) : Touches positions table query := by
  cases query with
  | opening pending =>
      exact fun label selected => ⟨present label (avail label selected),
        history_bounded past positions depth fits label (avail label selected)⟩
  | sealing pending => exact ⟨present _ avail, history_bounded past positions depth fits _ avail⟩
  | _ => trivial

/-- **Availability.** Along a certified service program, a private interpreter whose every request touching only present, bounded coordinates is simulated through a state map by another interpreter is simulated through that map on the whole program. The certificate is the program's lookup history: every reached request available against it, at most `remaining` further lookups, and a depth bound by its length; the first interpreter grows its chain table, makes looked-up coordinates present and keeps a state invariant. -/
theorem certified_map {σ τ : Type} (positions : Nat)
    (impl : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT σ ProbComp))
    (other : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT τ ProbComp))
    (map : σ → τ) (chainOf : σ → Table (Slot n)) (Inv : σ → Prop)
    (step : ∀ query state, Inv state → Touches positions (chainOf state) query →
      Prod.map id map <$> (impl query).run state = (other query).run (map state))
    (preserve : ∀ query state, Inv state → ∀ result ∈ support ((impl query).run state),
      Inv result.2 ∧ chainOf state ≤ chainOf result.2 ∧
        ∀ label ∈ lookupCoordinates query, Present (chainOf result.2) label)
    {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (past : List (Label n))
    (remaining : Nat) (state : σ) (safe : ServiceSafe client past) (weighted : Weighted lookupCost client remaining)
    (depth : PqxdhRecordLiftChainOrder.DepthBound (historyTable past) past.length)
    (fits : past.length + remaining ≤ positions) (present : ∀ label ∈ past, Present (chainOf state) label)
    (invariant : Inv state) :
    Prod.map id map <$> (simulateQ impl client).run state = (simulateQ other client).run (map state) := by
  induction client using OracleComp.inductionOn generalizing past remaining state with
  | pure value => simp
  | query_bind query next ih =>
      rw [serviceSafe_query_bind] at safe
      rw [Weighted, isQueryBound_query_bind_iff] at weighted
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← step query state invariant
        (touches_of_avail positions _ past depth (by omega) present query safe.1), bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result supported
      have grown := preserve query state invariant result supported
      have length := lookupCoordinates_length query
      exact ih result.1 (past ++ lookupCoordinates query) (remaining - lookupCost query) result.2 (safe.2 result.1)
        (weighted.2 result.1) (history_depth past depth query safe.1)
        (by simp only [List.length_append]; omega)
        (fun label member => by
          rcases List.mem_append.mp member with old | new
          · obtain ⟨output, found⟩ := present label old
            exact ⟨output, grown.2.1 found⟩
          · exact grown.2.2 label new)
        grown.1

/-- The empty history is depth-bounded by zero. -/
theorem history_empty : PqxdhRecordLiftChainOrder.DepthBound (historyTable ([] : List (Label n))) 0 := by
  intro entry output found
  simp [historyTable] at found

/-- **Availability of the whole program.** For every adversary within its budget, a private interpreter simulated through a state map on every request touching only present coordinates within `positions budget` is simulated through it on the whole compiled program. -/
theorem program_map {σ τ : Type} (budget : PqxdhDeploymentInterface.Budget)
    (impl : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT σ ProbComp))
    (other : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT τ ProbComp))
    (map : σ → τ) (chainOf : σ → Table (Slot n)) (Inv : σ → Prop)
    (step : ∀ query state, Inv state → Touches (PqxdhRecordLiftIdeal.positions budget) (chainOf state) query →
      Prod.map id map <$> (impl query).run state = (other query).run (map state))
    (preserve : ∀ query state, Inv state → ∀ result ∈ support ((impl query).run state),
      Inv result.2 ∧ chainOf state ≤ chainOf result.2 ∧
        ∀ label ∈ lookupCoordinates query, Present (chainOf result.2) label)
    (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : budget.Respects adversary) (state : σ) (invariant : Inv state) :
    Prod.map id map <$> (simulateQ impl
      (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)).run state =
    (simulateQ other (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary)).run
      (map state) :=
  certified_map (PqxdhRecordLiftIdeal.positions budget) impl other map chainOf Inv step preserve _ [] _ state
    (program_history env crypto codec route serverKid bounds mode adversary)
    (program_lookups env crypto codec route serverKid bounds mode budget adversary respects)
    history_empty (by simp) (fun _ member => by simp at member) invariant

/-- Two keyed implementations agreeing on every request at a present coordinate within `positions` give CTX-world services agreeing on every request touching only such coordinates. -/
theorem ctxInterpreterOf_congr (positions : Nat) (keyed other : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (agree : ∀ query state, Present state.base.chain query.1 → PqxdhRecordLiftChainOrder.Bounded positions query.1 →
      (keyed query).run state = (other query).run state)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) (touches : Touches positions state.base.chain query) :
    (ctxInterpreterOf keyed replace setup codec query).run state =
      (ctxInterpreterOf other replace setup codec query).run state := by
  cases query with
  | opening pending =>
      exact opening_congr keyed other replace setup codec pending state
        (fun label selected request => agree _ state (touches label selected).1 (touches label selected).2)
  | sealing pending =>
      exact sealing_congr keyed other replace setup codec pending state
        (fun request => agree _ state touches.1 touches.2)
  | _ => rfl

/-- **Availability of the whole program.** For every adversary within its budget, two keyed implementations that agree on every request at a present coordinate within `positions budget` give the same CTX world, from every initial state. -/
theorem program_congr (keyed other : QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp))
    (budget : PqxdhDeploymentInterface.Budget)
    (keep : ∀ query state, ∀ result ∈ support ((keyed query).run state), result.2.base.chain = state.base.chain)
    (agree : ∀ query state, Present state.base.chain query.1 →
      PqxdhRecordLiftChainOrder.Bounded (PqxdhRecordLiftIdeal.positions budget) query.1 →
      (keyed query).run state = (other query).run state)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : budget.Respects adversary) (state : CtxPrivate n) :
    (simulateQ (ctxInterpreterOf keyed replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run state =
    (simulateQ (ctxInterpreterOf other replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run state := by
  have mapped := program_map budget (ctxInterpreterOf keyed replace setup codec) (ctxInterpreterOf other replace setup codec)
    id (fun state => state.base.chain) (fun _ => True)
    (fun query state _ touches => by
      rw [Prod.map_id, id_map]
      exact ctxInterpreterOf_congr _ keyed other agree replace setup codec query state touches)
    (fun query state _ result supported => ⟨trivial, chain_step keyed keep replace setup codec query state result supported⟩)
    env setup.source.crypto codec route serverKid bounds mode adversary respects state trivial
  rwa [Prod.map_id, id_map] at mapped

/-- Explicit-key CTX worlds whose keys and modes agree at every present coordinate within `positions budget` are equal. -/
theorem ctxRunWith_congr (keyOf other : KeyOf n) (modes otherModes : Label n → KeyMode)
    (budget : PqxdhDeploymentInterface.Budget)
    (sameKey : ∀ table label, Present table label → PqxdhRecordLiftChainOrder.Bounded (PqxdhRecordLiftIdeal.positions budget) label →
      keyOf table label = other table label)
    (sameMode : ∀ label, PqxdhRecordLiftChainOrder.Bounded (PqxdhRecordLiftIdeal.positions budget) label →
      modes label = otherModes label)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    ctxRunWith keyOf modes replace setup codec route env serverKid bounds mode adversary =
      ctxRunWith other otherModes replace setup codec route env serverKid bounds mode adversary := by
  unfold ctxRunWith
  rw [ctxInterpreterWith_of, ctxInterpreterWith_of]
  exact program_congr _ _ budget (keyedWith_chain keyOf modes _ _)
    (fun query state present bounded => keyedWith_congr keyOf other modes otherModes _ _ query state
      (sameKey _ _ present bounded) (sameMode _ bounded))
    replace setup codec route env serverKid bounds mode adversary respects _

/-- **The last hybrid is `idealAuth`.** After all `hops n budget` steps every coordinate the program can reach is in replay mode. -/
theorem hybrid_last (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) :
    hybrid (PqxdhRecordLiftIdeal.positions budget) (hops n budget) setup codec route env serverKid bounds mode adversary =
      idealAuth setup codec route env serverKid bounds mode adversary := by
  unfold hybrid idealAuth
  rw [← ctxRunWith_tableKey, ← ctxRunWith_tableKey]
  exact ctxRunWith_congr tableKey tableKey _ _ budget (fun _ _ _ _ => rfl)
    (fun label bounded => (hybridModes_last _ label).mpr bounded) id setup codec route env serverKid bounds mode
    adversary respects

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.opening_material_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.opening_material_present

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookup_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookup_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookup_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookup_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookup_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookup_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.historyTable_present' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.historyTable_present

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.historyTable_mono' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.historyTable_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.historyTable_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.historyTable_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localSafe_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localSafe_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localTrack_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localTrack_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.receive_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.receive_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.send_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.send_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.track_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.track_member

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serviceSafe_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localLift_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localLift_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localLift_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localLift_trace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localTrack_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localTrack_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ready_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ready_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelReceive_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelReceive_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelSend_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelSend_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_pure_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.trace_pure_member

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ownerStep_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ownerStep_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ownerRun_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ownerRun_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_server

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_attempts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serverStep_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serverStep_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.beaconStep_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.beaconStep_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_markUsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_markUsed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.markUsed_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.markUsed_server

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_peers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.controlReady_peers

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.resolve_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.resolve_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.capability_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.capability_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.effects_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.effects_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.initializeServer_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.initializeServer_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.handler_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.handler_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.schedule_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.schedule_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.initial_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.initial_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localLift_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.localLift_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.query_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.query_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelReceive_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelReceive_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelSend_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.kernelSend_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ownerRun_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ownerRun_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.resolve_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.resolve_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.capability_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.capability_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.effects_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.effects_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serverStep_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.serverStep_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.beaconStep_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.beaconStep_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.handler_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.handler_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.world_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.world_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_lookups

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookupCoordinates_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.lookupCoordinates_length

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.history_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.history_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.history_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.history_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ctxInterpreterWith_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ctxInterpreterWith_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.keyedWith_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.keyedWith_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.keyedWith_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.keyedWith_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.material_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.material_chains

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.openArguments_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.openArguments_material

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.opening_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.opening_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.query_bind_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.query_bind_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.sealing_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.sealing_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.simulate_chain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.simulate_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.chain_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.chain_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.touches_of_avail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.touches_of_avail

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.certified_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.certified_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.history_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.history_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ctxInterpreterOf_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ctxInterpreterOf_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.program_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ctxRunWith_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.ctxRunWith_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.hybrid_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxAvailability.hybrid_last
