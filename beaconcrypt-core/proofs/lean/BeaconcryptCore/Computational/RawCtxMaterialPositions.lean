import BeaconcryptCore.Computational.RawCtxSourceHkdf
import BeaconcryptCore.Refinement.RatchetFutureTrace
import BeaconcryptCore.Refinement.RatchetReceiveIdeal

/-!
Actual extracted send and receive programs expose their material positions through a private log of the exact KDF request and actual response. The same fixed functional interpreter handles every derivation. Future admission records the chronological origin positions, including skipped material and the selected target; cached admission reads the stored material without another KDF call. Sending advances from its current origin position before the actual optional sealing result. No independent material table, injectivity, freshness or output-distribution premise is introduced.

The complete opening and sealing callbacks retain arbitrary probabilistic effects and their entire primitive state. A failed future opening restores only the source kernel. A subsequent retry therefore recomputes the same positions and appends the repeated requests while passing the first opening's actual primitive poststate into the next opening. Successful cached/future publication and all send outcomes preserve the ordinary kernel/material relation without assuming that the callback implements an ideal decryption predicate. Source zero, replay, capacity and exhaustion branches remain included.

Erasing only the private KDF log gives the exact original interpreted program through every adaptive continuation and preserves every selective underlying-oracle cap. Concrete source handlers use the existing shared HKDF/CTX state and actual native capability adapters; byte projections identify complete 76-byte evaluations and key/nonce material at every original position. Actual initial source responses establish both role orientations and the starting relation for any supplied root. Initial roots need not be independent or uniform for these operational statements.

The log retains earlier chain inputs and is analysis-only private state, excluded from adversary replies, reveals, snapshots and persistence. This fixed-functional KDF interpretation is not an arbitrary fresh-output hybrid: a later hybrid must prove its own reachable-table/position correspondence. Whole raw/mixed owner scheduling, global role allocation/registration/reveals, restored-state validity, source-key collision probabilities and single-use security remain separate composition steps. Native primitive, decoder, compiler, storage and runtime contracts are unchanged. Query equality does not make HKDF/HMAC, local AEAD, byte conversion, copying, logging or list work free. The inherited noncomputable source normalizers and the local elaboration-transparency option imply no compiled-runtime claim.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxMaterialPositions

abbrev KdfLog := List (SymmetricRatchetKdfRequest × RatchetKdfResponse)

inductive Prefix {Context : Type} (execute : KdfInterpreter) :
    ReceiveEffect Context → ReceiveEffect Context → List SymmetricRatchetKdfRequest → Prop where
  | refl (effect : ReceiveEffect Context) : Prefix execute effect effect []
  | step (pending : ReceiveKdf Context) (next final : ReceiveEffect Context)
      (requests : List SymmetricRatchetKdfRequest)
      (resumed : pending.resume (execute pending.request) = ok next)
      (tail : Prefix execute next final requests) :
      Prefix execute (.ReceiveKdfRequested pending) final (pending.request :: requests)

def receiveImpl {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext)) :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext)
      (StateT (PrimitiveState × KdfLog) (OracleComp base))
  | .inl request => fun state =>
      pure (execute request, (state.1, state.2 ++ [(request, execute request)]))
  | .inr pending => fun state => do
      let result ← (opening pending).run state.1
      pure (result.1, (result.2, state.2))

/-- An exact source KDF prefix appends every actual request/response before the unchanged remaining computation. -/
theorem prefix_complete {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    {effect terminal : ReceiveEffect Context} {requests : List SymmetricRatchetKdfRequest}
    (trace : Prefix execute effect terminal requests) (state : PrimitiveState) (history : KdfLog) :
    ((simulateQ (receiveImpl execute opening) (RawCtxOwnerOracle.program effect)).run (state, history)) =
      ((simulateQ (receiveImpl execute opening) (RawCtxOwnerOracle.program terminal)).run
        (state, history ++ requests.map (fun request => (request, execute request)))) := by
  induction trace generalizing history with
  | refl => simp
  | step pending next final requests resumed tail ih =>
    have next_exact : RawCtxOwnerOracle.resume pending (execute pending.request) = next :=
      RustM.ok.inj ((RawCtxOwnerOracle.resume_exact pending (execute pending.request)).symm.trans resumed)
    rw [RawCtxOwnerOracle.program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [receiveImpl, StateT.run, pure_bind, next_exact]
    simpa only [StateT.run, List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (history ++ [(pending.request, execute pending.request)])

/-- The actual optional opening and complete primitive poststate reach source publication unchanged. -/
theorem opened_complete {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (pending : ReceiveOpen Context) (state : PrimitiveState) (history : KdfLog) :
    ((simulateQ (receiveImpl execute opening)
      (RawCtxOwnerOracle.program (.ReceiveOpenRequested pending))).run (state, history)) = (do
        let result ← (opening pending).run state
        pure (RawCtxOwnerOracle.finish pending result.1, (result.2, history))) := by
  rw [RawCtxOwnerOracle.program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure]
  simp only [receiveImpl, StateT.run, bind_assoc, pure_bind]

def positionedRequests {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (chain : RatchetChain) (start count : Nat) : List SymmetricRatchetKdfRequest :=
  (List.range count).map (fun offset =>
    ⟨(Ratchet.chainAt cr chain (start + offset)).bytes, SYM_RATCHET_INFO⟩)

/-- Chronological position lists expose the current source chain input before the remaining positions. -/
theorem positionedRequests_succ {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (chain : RatchetChain) (start count : Nat) :
    positionedRequests cr chain start (count + 1) =
      ⟨(Ratchet.chainAt cr chain start).bytes, SYM_RATCHET_INFO⟩ ::
        positionedRequests cr chain (start + 1) count := by
  simp [positionedRequests, List.range_succ_eq_map, List.map_map, Function.comp_def,
    Nat.add_comm, Nat.add_left_comm]

/-- A current chain prefix identifies the same original positions, without assuming distinct chain values. -/
theorem positionedRequests_chainAt {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (base start count : Nat) :
    positionedRequests cr (Ratchet.chainAt cr origin base) start count =
      positionedRequests cr origin (base + start) count := by
  simp only [positionedRequests, Ratchet.chainAt_chainAt, Nat.add_assoc]

/-- The source position list contains exactly the requested number of derivations. -/
theorem positionedRequests_length {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (start count : Nat) :
    (positionedRequests cr origin start count).length = count := by
  simp [positionedRequests]

/-- Actual future KDF resumes execute exactly the origin-position prefix for the supplied functional interpreter. -/
theorem future_positioned_prefix {AD PT CT Context : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (remaining : Nat) :
    ∀ (count : Nat) (pending : ReceiveKdf Context), pending.remaining.val = remaining →
      FutureKdfRefines (withInterpreter cr execute) origin send receive entry context target count pending →
      ∃ opened,
        Prefix execute (.ReceiveKdfRequested pending) (.ReceiveOpenRequested opened)
          (positionedRequests (withInterpreter cr execute) receive.ck count remaining) ∧
        FutureOpenRefines (withInterpreter cr execute) origin send receive entry context target opened := by
  induction remaining with
  | zero =>
    intro count pending left refines
    have position := refines.position
    have remaining := refines.remaining
    omega
  | succ remaining ih =>
    intro count pending left refines
    have exactRequest : pending.request =
        ⟨(Ratchet.chainAt (withInterpreter cr execute) receive.ck count).bytes, SYM_RATCHET_INFO⟩ := by
      cases hrequest : pending.request
      simpa only [SymmetricRatchetKdfRequest.mk.injEq, hrequest] using
        And.intro refines.requestInput refines.requestInfo
    have response := interpreter_request_refines cr execute
      (Ratchet.chainAt (withInterpreter cr execute) receive.ck count) pending.request
      refines.requestInput refines.requestInfo
    by_cases last : remaining = 0
    · obtain ⟨opened, resumed, ready⟩ := refines.resume_last (withInterpreter cr execute)
        origin send receive entry context target count pending (by omega) (execute pending.request) response
      refine ⟨opened, ?_, ready⟩
      rw [last, positionedRequests_succ, ← exactRequest]
      exact .step pending _ _ [] resumed (.refl _)
    · obtain ⟨later, resumed, refined⟩ := refines.resume_more (withInterpreter cr execute)
        origin send receive entry context target count pending (by omega) (execute pending.request) response
      obtain ⟨opened, trace, ready⟩ := ih (count + 1) later
        (by have original := refines.remaining; have next := refined.remaining; omega) refined
      refine ⟨opened, ?_, ready⟩
      rw [positionedRequests_succ, ← exactRequest]
      exact .step pending _ _ _ resumed trace

/-- Future admission selects the actual target material and retains every skipped derivation, callback result and state. -/
theorem future_positioned_run {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (future : receive.n < target.val)
    (capacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext)) :
    ∃ opened,
      FutureOpenRefines (withInterpreter cr execute) origin send receive entry context target opened ∧
      opened.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1))) ∧
      ∀ state history,
        ((simulateQ (receiveImpl execute opening)
          (RawCtxOwnerOracle.receive entry target context)).run (state, history)) = (do
            let result ← (opening opened).run state
            pure (RawCtxOwnerOracle.finish opened result.1,
              (result.2, history ++
                (positionedRequests (withInterpreter cr execute) origin receive.n (target.val - receive.n)).map
                  (fun request => (request, execute request))))) := by
  obtain ⟨pending, started, refined⟩ := refines.begin_receive_future
    (withInterpreter cr execute) origin send receive entry context target future capacity
  obtain ⟨opened, trace, ready⟩ := future_positioned_prefix cr execute origin send receive entry context target
    (target.val - receive.n) 0 pending (by simpa only [Nat.sub_zero] using refined.remaining) refined
  have selected := ready.material_exact (withInterpreter cr execute) origin send receive entry context target opened
  rw [refines.receiveControl.chain, Ratchet.msgKeyAt_chainAt,
    show receive.n + (target.val - receive.n - 1) = target.val - 1 by omega] at selected
  refine ⟨opened, ready, selected, ?_⟩
  intro state history
  have began : RawCtxOwnerOracle.begin entry target context = .ReceiveKdfRequested pending :=
    RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans started)
  rw [RawCtxOwnerOracle.receive, began, prefix_complete execute opening trace, opened_complete,
    refines.receiveControl.chain, positionedRequests_chainAt, Nat.add_zero]

/-- Cached admission selects the original stored position and performs no new KDF request. -/
theorem cached_positioned_run {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (index : Nat) (material : RatchetMaterial)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (sequence : target.val = index + 1) (stored : List.lookup index receive.skipped = some material)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext)) :
    ∃ opened,
      CachedOpenRefines (withInterpreter cr execute) origin send receive index material opened ∧
      opened.entry = entry ∧
      opened.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin index)) ∧
      ∀ state history,
        ((simulateQ (receiveImpl execute opening)
          (RawCtxOwnerOracle.receive entry target context)).run (state, history)) = (do
            let result ← (opening opened).run state
            pure (RawCtxOwnerOracle.finish opened result.1, (result.2, history))) := by
  obtain ⟨opened, started, ready⟩ := begin_receive_cached_refines (withInterpreter cr execute)
    origin send receive entry context target index material refines sequence stored
  have selected := ready.material_exact (withInterpreter cr execute) origin send receive index material opened
  have materialAt : material = Ratchet.msgKeyAt (withInterpreter cr execute) origin index :=
    refines.receiveControl.keys _ (control.mem_of_lookup_eq_some stored)
  rw [materialAt] at selected
  have began : RawCtxOwnerOracle.begin entry target context = .ReceiveOpenRequested opened :=
    RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans started)
  have saved : opened.entry = entry := by
    simpa only [began, effectEntry] using RawCtxOwnerOracle.begin_entry entry target context
  refine ⟨opened, ready, saved, selected, ?_⟩
  intro state history
  rw [RawCtxOwnerOracle.receive, began, opened_complete]

def sendImpl {Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output)) :
    QueryImpl (RawCtxSourceSend.SendSpec Context Output)
      (StateT (PrimitiveState × KdfLog) (OracleComp base))
  | .inl request => fun state =>
      pure (execute request, (state.1, state.2 ++ [(request, execute request)]))
  | .inr pending => fun state => do
      let result ← (sealing pending).run state.1
      pure (result.1, (result.2, state.2))

/- The source send computes its real KDF response and publishes the advanced kernel even after sealing returns None. -/
set_option backward.isDefEq.respectTransparency false in
theorem send_requested_complete {Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output))
    (pending : SendKdf Context) (state : PrimitiveState) (history : KdfLog) :
    ((simulateQ (sendImpl execute sealing)
      (RawCtxSourceSend.program (.SendKdfRequested pending))).run (state, history)) = (do
        let result ← (sealing (RawCtxSourceSend.resumeSend pending (execute pending.request))).run state
        pure (((RawCtxSourceSend.resumeSend pending (execute pending.request)).advanced, result.1),
          (result.2, history ++ [(pending.request, execute pending.request)]))) := by
  rw [RawCtxSourceSend.program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [show (sendImpl execute sealing (.inl pending.request)).run (state, history) =
      pure (execute pending.request, (state, history ++ [(pending.request, execute pending.request)])) from rfl]
  simp only [pure_bind]
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure]
  simp only [sendImpl, StateT.run, bind_assoc, pure_bind]

/-- An aligned source send uses its old origin position and advances once before the optional result is published. -/
theorem send_positioned_run {AD PT CT Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (entry : ConcreteRatchetKernel) (context : Context)
    (aligned : entry.refined.send_chain = Ratchet.chainAt (withInterpreter cr execute)
      origin entry.refined.control.send_sequence.val)
    (active : entry.refined.control.send_sequence ≠ core.num.U64.MAX)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output)) :
    ∃ (pending : SendKdf Context) (ready : SendSeal Context),
      pending.request = ⟨entry.refined.send_chain.bytes, SYM_RATCHET_INFO⟩ ∧
      ready.material = Ratchet.msgKeyAt (withInterpreter cr execute)
        origin entry.refined.control.send_sequence.val ∧
      ready.advanced.refined.send_chain = Ratchet.chainAt (withInterpreter cr execute)
        origin (entry.refined.control.send_sequence.val + 1) ∧
      ready.advanced.refined.control.send_sequence.val = entry.refined.control.send_sequence.val + 1 ∧
      ready.sequence.val = entry.refined.control.send_sequence.val + 1 ∧ ready.context = context ∧
      ∀ state history,
        ((simulateQ (sendImpl execute sealing)
          (RawCtxSourceSend.send entry context)).run (state, history)) = (do
            let result ← (sealing ready).run state
            pure ((ready.advanced, result.1),
              (result.2, history ++ [(pending.request, execute pending.request)]))) := by
  obtain ⟨pending, started, entryEq, contextEq, inputEq, infoEq, sequenceEq, next, _, _⟩ :=
    RawCtxSourceSend.beginSend_fields entry context active
  have requestEq : pending.request = ⟨entry.refined.send_chain.bytes, SYM_RATCHET_INFO⟩ := by
    cases hrequest : pending.request
    simpa only [SymmetricRatchetKdfRequest.mk.injEq, hrequest] using And.intro inputEq infoEq
  obtain ⟨stepped, decoded, readyEq⟩ :=
    RawCtxSourceSend.resumeSend_fields pending (execute pending.request)
  have responseEq : ratchet_step_from_response (execute pending.request) =
      ok (interpretedStep execute entry.refined.send_chain) := by
    rw [requestEq]
    exact interpretedStep_spec execute entry.refined.send_chain
  have stepEq : stepped = interpretedStep execute entry.refined.send_chain :=
    RustM.ok.inj (decoded.symm.trans responseEq)
  rw [stepEq] at readyEq
  refine ⟨pending, RawCtxSourceSend.resumeSend pending (execute pending.request), requestEq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [readyEq, Ratchet.msgKeyAt, withInterpreter] using
      congrArg (fun chain => (interpretedStep execute chain).material) aligned
  · simp only [readyEq]
    change (withInterpreter cr execute).kdfChain entry.refined.send_chain = _
    rw [aligned]
    simp only [Ratchet.chainAt, Function.iterate_succ_apply']
  · simp only [readyEq, ← sequenceEq, next]
  · simp only [readyEq, next]
  · simp only [readyEq, contextEq]
  · intro state history
    rw [RawCtxSourceSend.send, started, send_requested_complete]

def bareReceiveImpl {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext)) :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) (StateT PrimitiveState (OracleComp base))
  | .inl request => pure (execute request)
  | .inr pending => opening pending

/-- Erasing the private receive log preserves the exact reply and complete primitive state. -/
theorem receive_query_erase {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (query : (RawCtxOwnerOracle.ReceiveSpec Context Plaintext).Domain) (state : PrimitiveState × KdfLog) :
    Prod.map id Prod.fst <$> (receiveImpl execute opening query).run state =
      (bareReceiveImpl execute opening query).run state.1 := by
  cases query with
  | inl request =>
    change Prod.map id Prod.fst <$> (pure (execute request,
      (state.1, state.2 ++ [(request, execute request)])) : OracleComp base _) =
        pure (execute request, state.1)
    simp
  | inr pending => simp [receiveImpl, bareReceiveImpl, StateT.run]

/-- Every receive-side adaptive continuation retains the original full computation after log erasure. -/
theorem receive_complete_erase {Context Plaintext PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (client : OracleComp (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) Result)
    (state : PrimitiveState × KdfLog) :
    Prod.map id Prod.fst <$> (simulateQ (receiveImpl execute opening) client).run state =
      (simulateQ (bareReceiveImpl execute opening) client).run state.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (receiveImpl execute opening) (bareReceiveImpl execute opening) Prod.fst
    (receive_query_erase execute opening) client state


def bareSendImpl {Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output)) :
    QueryImpl (RawCtxSourceSend.SendSpec Context Output) (StateT PrimitiveState (OracleComp base))
  | .inl request => pure (execute request)
  | .inr pending => sealing pending

/-- Erasing the private send log preserves the exact reply and complete primitive state. -/
theorem send_query_erase {Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output))
    (query : (RawCtxSourceSend.SendSpec Context Output).Domain) (state : PrimitiveState × KdfLog) :
    Prod.map id Prod.fst <$> (sendImpl execute sealing query).run state =
      (bareSendImpl execute sealing query).run state.1 := by
  cases query with
  | inl request =>
    change Prod.map id Prod.fst <$> (pure (execute request,
      (state.1, state.2 ++ [(request, execute request)])) : OracleComp base _) =
        pure (execute request, state.1)
    simp
  | inr pending => simp [sendImpl, bareSendImpl, StateT.run]

/-- Every send-side adaptive continuation retains the original full computation after log erasure. -/
theorem send_complete_erase {Context Output PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output))
    (client : OracleComp (RawCtxSourceSend.SendSpec Context Output) Result)
    (state : PrimitiveState × KdfLog) :
    Prod.map id Prod.fst <$> (simulateQ (sendImpl execute sealing) client).run state =
      (simulateQ (bareSendImpl execute sealing) client).run state.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (sendImpl execute sealing) (bareSendImpl execute sealing) Prod.fst
    (send_query_erase execute sealing) client state

open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge

/-- Concrete functional source chains and key/nonce material identify the same complete byte-model positions. -/
theorem source_position_bytes (c : Pqxdh.Crypto) (origin : RatchetChain) (position : Nat) :
    absChain (Ratchet.chainAt (concreteCrypto c (RawCtxSourceHkdf.response c)) origin position) =
      Ratchet.chainAt (Pqxdh.ratchetCrypto c) (absChain origin) position ∧
    absMaterial (Ratchet.msgKeyAt (concreteCrypto c (RawCtxSourceHkdf.response c)) origin position) =
      Ratchet.msgKeyAt (Pqxdh.ratchetCrypto c) (absChain origin) position := by
  exact ⟨chainAt_commutes c _ (RawCtxSourceHkdf.response_law c) origin position,
    msgKeyAt_commutes c _ (RawCtxSourceHkdf.response_law c) origin position⟩

noncomputable def retryOnFailure {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (state : PrimitiveState × KdfLog) :
    OracleComp base ((ConcreteRatchetKernel × core.option.Option Plaintext) × (PrimitiveState × KdfLog)) := do
  let first ← (simulateQ (receiveImpl execute opening)
    (RawCtxOwnerOracle.receive entry target context)).run state
  match first.1.2 with
  | .None => (simulateQ (receiveImpl execute opening)
      (RawCtxOwnerOracle.receive first.1.1 target context)).run first.2
  | .Some _ => pure first

/-- A retry after actual rejection reuses the saved kernel and actual primitive poststate, retaining both KDF prefixes. -/
theorem retry_complete {Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (opened : ReceiveOpen Context) (saved : opened.entry = entry) (requests : KdfLog)
    (run_exact : ∀ state history,
      (simulateQ (receiveImpl execute opening)
        (RawCtxOwnerOracle.receive entry target context)).run (state, history) = (do
          let result ← (opening opened).run state
          pure (RawCtxOwnerOracle.finish opened result.1, (result.2, history ++ requests))))
    (state : PrimitiveState) (history : KdfLog) :
    retryOnFailure execute opening entry target context (state, history) = (do
      let first ← (opening opened).run state
      match first.1 with
      | .None => do
          let second ← (opening opened).run first.2
          pure (RawCtxOwnerOracle.finish opened second.1,
            (second.2, (history ++ requests) ++ requests))
      | .Some plaintext => pure (RawCtxOwnerOracle.finish opened (.Some plaintext),
          (first.2, history ++ requests))) := by
  rw [retryOnFailure, run_exact]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext first
  rcases first with ⟨reply, nextState⟩
  cases reply with
  | none => simp only [RawCtxOwnerOracle.finish_none, saved, run_exact]
  | some plaintext => rfl


/-- Actual future rejection and retry recompute identical origin positions without resetting the primitive state. -/
theorem future_retry {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (future : receive.n < target.val)
    (capacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext)) :
    ∃ opened,
      opened.material = ok (.Some (Ratchet.msgKeyAt (withInterpreter cr execute) origin (target.val - 1))) ∧
      ∀ state history,
        let requests := (positionedRequests (withInterpreter cr execute)
          origin receive.n (target.val - receive.n)).map (fun request => (request, execute request))
        retryOnFailure execute opening entry target context (state, history) = (do
          let first ← (opening opened).run state
          match first.1 with
          | .None => do
              let second ← (opening opened).run first.2
              pure (RawCtxOwnerOracle.finish opened second.1,
                (second.2, (history ++ requests) ++ requests))
          | .Some plaintext => pure (RawCtxOwnerOracle.finish opened (.Some plaintext),
              (first.2, history ++ requests))) := by
  obtain ⟨opened, hscoped, material, exactRun⟩ := future_positioned_run cr execute origin send receive
    entry context target refines future capacity opening
  have saved : opened.entry = entry := hscoped.choose_spec.1
  exact ⟨opened, material, fun state history => retry_complete execute opening entry target context
    opened saved _ exactRun state history⟩

/-- Any successful callback consumes the selected cached position and preserves all remaining source material invariants. -/
theorem cached_finish_positioned {AD PT CT Context Plaintext : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (index : Nat) (material : RatchetMaterial) (opened : ReceiveOpen Context)
    (refines : CachedOpenRefines cr origin send receive index material opened)
    (plaintext : Plaintext) :
    KernelRefines cr origin send
      { receive with skipped := receive.skipped.filter (fun p => !(p.1 == index)) }
      (RawCtxOwnerOracle.finish opened (.Some plaintext)).1 := by
  obtain ⟨prepared, cached, phase, _, last, finish, kernel, _, sequence,
    slot, _, controlSequence, cachedSequence, _⟩ := refines
  obtain ⟨published, publication, invariant⟩ :=
    KernelRefines.cached_publication cr origin send receive opened.entry kernel prepared index
      sequence slot (controlSequence.symm.trans cachedSequence) last finish
  have actual : opened.finish (.Some plaintext) = ok ({ refined := published }, .Some plaintext) := by
    simp only [ReceiveOpen.finish, phase, publication, bind_tc_ok]
  have equal := RustM.ok.inj ((RawCtxOwnerOracle.finish_exact opened (.Some plaintext)).symm.trans actual)
  rw [equal]
  exact invariant

/-- Any successful callback publishes the actual future state and every retained skipped material position. -/
theorem future_finish_positioned {AD PT CT Context Plaintext : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (opened : ReceiveOpen Context)
    (refines : FutureOpenRefines cr origin send receive entry context target opened)
    (plaintext : Plaintext) :
    KernelRefines cr origin send (futureReceiveState cr receive target)
      (RawCtxOwnerOracle.finish opened (.Some plaintext)).1 := by
  obtain ⟨published, actual, invariant⟩ :=
    refines.finish_some cr origin send receive entry context target opened plaintext
  have equal := RustM.ok.inj ((RawCtxOwnerOracle.finish_exact opened (.Some plaintext)).symm.trans actual)
  rw [equal]
  exact invariant


/-- Every supported actual receive preserves the full source material relation, including all rejection branches. -/
theorem receive_preserves_positions {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64)
    (refines : KernelRefines (withInterpreter cr execute) origin send receive entry)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (state : PrimitiveState × KdfLog)
    (result : (ConcreteRatchetKernel × core.option.Option Plaintext) × (PrimitiveState × KdfLog))
    (present : result ∈ support ((simulateQ (receiveImpl execute opening)
      (RawCtxOwnerOracle.receive entry target context)).run state)) :
    ∃ nextReceive, KernelRefines (withInterpreter cr execute) origin send nextReceive result.1.1 := by
  by_cases failure : result.1.2 = .None
  · have same := RawCtxOwnerOracle.receive_failure_entry (receiveImpl execute opening)
      state entry target context result present failure
    exact ⟨receive, same ▸ refines⟩
  have rejected (actual : begin_receive entry target context = ok (.ReceiveRejected entry context)) : False := by
    have began : RawCtxOwnerOracle.begin entry target context = .ReceiveRejected entry context :=
      RustM.ok.inj ((RawCtxOwnerOracle.begin_exact entry target context).symm.trans actual)
    simp only [RawCtxOwnerOracle.receive, began, RawCtxOwnerOracle.program, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at present
    subst result
    exact failure rfl
  by_cases zero : target = 0#u64
  · exact False.elim (rejected (zero ▸ refines.begin_receive_zero
      (withInterpreter cr execute) origin send receive entry context))
  have positive : 0 < target.val := by scalar_tac
  cases stored : List.lookup (target.val - 1) receive.skipped with
  | some material =>
    obtain ⟨opened, hscoped, saved, _, exactRun⟩ := cached_positioned_run cr execute origin send receive
      entry context target (target.val - 1) material refines (by omega) stored opening
    rw [show state = (state.1, state.2) from rfl, exactRun, mem_support_bind_iff] at present
    obtain ⟨reply, _, returned⟩ := present
    simp only [mem_support_pure_iff] at returned
    subst result
    rcases reply with ⟨value, finalState⟩
    cases value with
    | none => exact False.elim (failure rfl)
    | some plaintext =>
      exact ⟨_, cached_finish_positioned (withInterpreter cr execute) origin send receive
        (target.val - 1) material opened hscoped plaintext⟩
  | none =>
    by_cases past : target.val ≤ receive.n
    · exact False.elim (rejected (refines.begin_receive_replay (withInterpreter cr execute)
        origin send receive entry target context past positive stored))
    by_cases capacity : entry.refined.control.receive_cache.len.val + (target.val - receive.n - 1) ≤ 50
    · obtain ⟨opened, hscoped, _, exactRun⟩ := future_positioned_run cr execute origin send receive
        entry context target refines (by omega) capacity opening
      rw [show state = (state.1, state.2) from rfl, exactRun, mem_support_bind_iff] at present
      obtain ⟨reply, _, returned⟩ := present
      simp only [mem_support_pure_iff] at returned
      subst result
      rcases reply with ⟨value, finalState⟩
      cases value with
      | none => exact False.elim (failure rfl)
      | some plaintext =>
        exact ⟨_, future_finish_positioned (withInterpreter cr execute) origin send receive
          entry context target opened hscoped plaintext⟩
    · exact False.elim (rejected (refines.begin_receive_capacity_rejected (withInterpreter cr execute)
        origin send receive entry target context (by omega) (by omega)))


/-- Every supported source send preserves both directional material relations, including exhausted and failed seals. -/
theorem send_preserves_positions {AD PT CT Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (receiveOrigin sendOrigin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (context : Context)
    (refines : KernelRefines (withInterpreter cr execute) receiveOrigin send receive entry)
    (aligned : send.ck = Ratchet.chainAt (withInterpreter cr execute) sendOrigin send.n)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output))
    (state : PrimitiveState × KdfLog)
    (result : (ConcreteRatchetKernel × Option Output) × (PrimitiveState × KdfLog))
    (present : result ∈ support ((simulateQ (sendImpl execute sealing)
      (RawCtxSourceSend.send entry context)).run state)) :
    ∃ nextSend, KernelRefines (withInterpreter cr execute) receiveOrigin nextSend receive result.1.1 ∧
      nextSend.ck = Ratchet.chainAt (withInterpreter cr execute) sendOrigin nextSend.n := by
  by_cases exhausted : entry.refined.control.send_sequence = core.num.U64.MAX
  · rw [RawCtxSourceSend.send_exhausted entry context exhausted] at present
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at present
    subst result
    exact ⟨send, refines, aligned⟩
  obtain ⟨pending, started, hphase⟩ := begin_send_refines (withInterpreter cr execute)
    receiveOrigin send receive entry context refines exhausted
  have began : RawCtxSourceSend.beginSend entry context = .SendKdfRequested pending :=
    RustM.ok.inj ((RawCtxSourceSend.beginSend_exact entry context).symm.trans started)
  have response := interpreter_request_refines cr execute send.ck pending.request hphase.requestInput hphase.requestInfo
  obtain ⟨ready, resumed, hready⟩ := SendKdf.resume_refines (withInterpreter cr execute)
    receiveOrigin send receive entry context pending hphase (execute pending.request) response
  have normalized : RawCtxSourceSend.resumeSend pending (execute pending.request) = ready :=
    RustM.ok.inj ((RawCtxSourceSend.resumeSend_exact pending (execute pending.request)).symm.trans resumed)
  rw [RawCtxSourceSend.send, began, show state = (state.1, state.2) from rfl,
    send_requested_complete, normalized, mem_support_bind_iff] at present
  obtain ⟨reply, _, returned⟩ := present
  simp only [mem_support_pure_iff] at returned
  subst result
  refine ⟨_, hready.advanced, ?_⟩
  change (withInterpreter cr execute).kdfChain send.ck =
    Ratchet.chainAt (withInterpreter cr execute) sendOrigin (send.n + 1)
  rw [aligned]
  simp only [Ratchet.chainAt, Function.iterate_succ_apply']


noncomputable def sourceOpening {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp
      (core.option.Option RawCtxWholeOwner.Decrypted) :=
  (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxSourceOpen.ownerAdapter) (.inr pending)

/-- The bare receive handler is exactly the existing concrete shared primitive and native capability composition. -/
theorem source_receive_handler {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    bareReceiveImpl (RawCtxSourceHkdf.response source.crypto) (sourceOpening (Auxiliary := Auxiliary) source) =
      RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
        RawCtxSourceOpen.ownerAdapter := by
  funext query
  cases query with
  | inr pending => rfl
  | inl request =>
    simp [bareReceiveImpl, RawCtxSourceOpen.ownerAdapter, QueryImpl.compose,
      RawCtxWholeOwner.adapter, RawCtxSourceOpen.nativeAdapter, OracleSpec.query]
    rfl

/-- Actual native receiving and full shared state agree with the position-log interpretation after only log erasure. -/
theorem source_receive_complete {Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (client : OracleComp (RawCtxOwnerOracle.ReceiveSpec RawCtxWholeOwner.OpenContext
      RawCtxWholeOwner.Decrypted) Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) (history : KdfLog) :
    Prod.map id Prod.fst <$> (simulateQ (receiveImpl (RawCtxSourceHkdf.response source.crypto)
      (sourceOpening source)) client).run (state, history) =
      (simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
        (simulateQ RawCtxSourceOpen.ownerAdapter client)).run state := by
  rw [receive_complete_erase, source_receive_handler, QueryImpl.simulateQ_compose]

noncomputable def sourceSealing {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : SendSeal RawCtxSourceSend.SealContext) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Option RawCtxSourceSend.Encrypted) :=
  ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) (.inr pending)

/-- The bare send handler is exactly the existing common shared primitive and native capability composition. -/
theorem source_send_handler {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    bareSendImpl (RawCtxSourceHkdf.response source.crypto) (sourceSealing (Auxiliary := Auxiliary) source writer) =
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
        RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter := by
  funext query
  cases query with
  | inr pending => rfl
  | inl request =>
    simp [bareSendImpl, RawCtxSourceSend.adapter, RawCtxMixedOwner.sendAdapter,
      RawCtxSourceSeal.nativeAdapter, RawCtxMixedOwner.sendLift, QueryImpl.compose,
      RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, OracleSpec.query]
    rfl

/-- Actual native sending and full shared state agree with the position-log interpretation after only log erasure. -/
theorem source_send_complete {Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (client : OracleComp (RawCtxSourceSend.SendSpec RawCtxSourceSend.SealContext
      RawCtxSourceSend.Encrypted) Result)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) (history : KdfLog) :
    Prod.map id Prod.fst <$> (simulateQ (sendImpl (RawCtxSourceHkdf.response source.crypto)
      (sourceSealing source writer)) client).run (state, history) =
      (simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
        (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter client))).run state := by
  rw [send_complete_erase, source_send_handler, QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose]


open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

/-- The actual initial response establishes Beacon directional origins and the complete source kernel relation. -/
theorem beacon_initial_positions (c : Pqxdh.Crypto) (root : Std.Array Std.U8 32#usize) :
    ∃ kernel,
      initializeBeacon root (RawCtxSourceHkdf.initialResponse c) = ok kernel ∧
      ChainBytesRefines kernel.refined.send_chain (Pqxdh.rootChains c (absBytes root)).2 ∧
      ChainBytesRefines kernel.refined.receive_chain (Pqxdh.rootChains c (absBytes root)).1 ∧
      KernelRefines (concreteCrypto c (RawCtxSourceHkdf.response c)) kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  exact BeaconcryptCore.Refinement.ProtocolComposition.initializeBeacon_refines c
    (concreteCrypto c (RawCtxSourceHkdf.response c)) root (RawCtxSourceHkdf.initialResponse c)
    (RawCtxSourceHkdf.initialResponse_law c)

/-- The actual initial response establishes Server directional origins and the complete source kernel relation. -/
theorem server_initial_positions (c : Pqxdh.Crypto) (root : Std.Array Std.U8 32#usize) :
    ∃ kernel,
      initializeServer root (RawCtxSourceHkdf.initialResponse c) = ok kernel ∧
      ChainBytesRefines kernel.refined.send_chain (Pqxdh.rootChains c (absBytes root)).1 ∧
      ChainBytesRefines kernel.refined.receive_chain (Pqxdh.rootChains c (absBytes root)).2 ∧
      KernelRefines (concreteCrypto c (RawCtxSourceHkdf.response c)) kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  exact BeaconcryptCore.Refinement.ProtocolComposition.initializeServer_refines c
    (concreteCrypto c (RawCtxSourceHkdf.response c)) root (RawCtxSourceHkdf.initialResponse c)
    (RawCtxSourceHkdf.initialResponse_law c)

/-- Log erasure preserves every selective underlying receive query bound exactly. -/
theorem receive_query_bounds {Context Plaintext PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : ReceiveOpen Context → StateT PrimitiveState (OracleComp base) (core.option.Option Plaintext))
    (client : OracleComp (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) Result)
    (state : PrimitiveState × KdfLog) (predicate : base.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (receiveImpl execute opening) client).run state).IsQueryBoundP predicate bound ↔
      ((simulateQ (bareReceiveImpl execute opening) client).run state.1).IsQueryBoundP predicate bound := by
  rw [← receive_complete_erase execute opening client state]
  exact (OracleComp.isQueryBoundP_map_iff _ _ _).symm

/-- Log erasure preserves every selective underlying send query bound exactly. -/
theorem send_query_bounds {Context Output PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : SendSeal Context → StateT PrimitiveState (OracleComp base) (Option Output))
    (client : OracleComp (RawCtxSourceSend.SendSpec Context Output) Result)
    (state : PrimitiveState × KdfLog) (predicate : base.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (sendImpl execute sealing) client).run state).IsQueryBoundP predicate bound ↔
      ((simulateQ (bareSendImpl execute sealing) client).run state.1).IsQueryBoundP predicate bound := by
  rw [← send_complete_erase execute sealing client state]
  exact (OracleComp.isQueryBoundP_map_iff _ _ _).symm


/-- Each actual response at an origin position is the same full 76-byte source evaluation, without position injectivity. -/
theorem source_response_at_position (c : Pqxdh.Crypto) (origin : RatchetChain) (position : Nat) :
    absBytes (RawCtxSourceHkdf.response c
      ⟨(Ratchet.chainAt (concreteCrypto c (RawCtxSourceHkdf.response c)) origin position).bytes,
        SYM_RATCHET_INFO⟩).bytes =
      c.hkdf (Ratchet.chainAt (Pqxdh.ratchetCrypto c) (absChain origin) position) Pqxdh.INFO_R 76 := by
  rw [RawCtxSourceHkdf.response_law c]
  rw [(source_position_bytes c origin position).1]

end BeaconcryptCore.Computational.RawCtxMaterialPositions

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.prefix_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.prefix_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.opened_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.opened_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.positionedRequests_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.positionedRequests_succ

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.positionedRequests_chainAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.positionedRequests_chainAt

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.positionedRequests_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.positionedRequests_length

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.future_positioned_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.future_positioned_prefix

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.future_positioned_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.future_positioned_run

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.cached_positioned_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.cached_positioned_run

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.send_requested_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.send_requested_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.send_positioned_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.send_positioned_run

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_query_erase

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_complete_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_complete_erase

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.send_query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.send_query_erase

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.send_complete_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.send_complete_erase

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.source_position_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.source_position_bytes

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.retry_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.retry_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.future_retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.future_retry

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.cached_finish_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.cached_finish_positioned

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.future_finish_positioned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.future_finish_positioned

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_preserves_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_preserves_positions

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.send_preserves_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.send_preserves_positions

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.source_receive_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.source_receive_handler

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.source_receive_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.source_receive_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.source_send_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.source_send_handler

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.source_send_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.source_send_complete

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.beacon_initial_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.beacon_initial_positions

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.server_initial_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.server_initial_positions

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.receive_query_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.send_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.send_query_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxMaterialPositions.source_response_at_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialPositions.source_response_at_position
