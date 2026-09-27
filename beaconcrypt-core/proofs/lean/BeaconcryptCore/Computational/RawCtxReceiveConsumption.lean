import BeaconcryptCore.Computational.RawCtxMaterialPositions

/-!
Actual source receiving has an exact operational cached/future/rejection relation under every actual optional opening reply. The future relation deliberately omits window and cache-room constraints as a stronger admission interface; its source refinement still follows every real guard and retains the complete primitive and private KDF-log poststate. No ideal decryption predicate, authentic plaintext, key uniqueness or independent material table is assumed.

For one uninterrupted initialized owner, successful source receiving consumes its actual decoded position. Cached success removes that position, future success advances to the real source future state, and rejection restores only the source kernel while retaining all primitive effects. Source sending preserves receive history even when failed sealing advances the send chain. These statements use the existing fixed functional source KDF and its original directional origins; equal material bytes may occur at different positions.

A private history monitor executes each original mixed send/raw operation before recording the sequence from an actual successful API reply. It never gates execution or changes any reply. Exact erasure preserves the complete adaptive OracleComp program, whole owner and shared primitive state. Actual initialization derives the empty history invariant; every supported original execution has a matching private history with no repeated successful position and length at most the raw-call cap. All selective underlying-oracle query bounds are exactly unchanged. Actual optional plaintext remains the original API result, whose network disclosure requires a separate policy.

The history is proof instrumentation, excluded from adversary/reveal/snapshot/persistence interfaces. This is operational source consumption, not cryptographic freshness, key or nonce uniqueness, a persistent ProVerif process simulation, or a multi-key authenticity reduction. Copies, restoration, crashes, concurrent ownership and rollback-resistant storage need their explicit outer contracts; restoring an earlier source kernel does not satisfy this uninterrupted-history theorem automatically. Native decoder/primitive/compiler/representation contracts remain unchanged. Fixed-source positions must still be related to any evolving-output hybrid. Hash/KDF, parsing, copying, private monitoring and list work remain real local computation despite unchanged oracle caps.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
open BeaconcryptCore.Refinement.RepresentationBridge
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxReceiveConsumption
open RawCtxMaterialPositions

inductive Transition {AD PT CT Plaintext : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial) (target : Std.U64) :
    core.option.Option Plaintext → Ratchet.RecvState RatchetChain RatchetMaterial → Prop where
  | rejected : Transition cr receive target .None receive
  | cached (plaintext : Plaintext) (material : RatchetMaterial)
      (positive : 0 < target.val)
      (stored : List.lookup (target.val - 1) receive.skipped = some material) :
      Transition cr receive target (.Some plaintext)
        { receive with skipped := receive.skipped.filter (fun p => !(p.1 == target.val - 1)) }
  | future (plaintext : Plaintext) (later : receive.n < target.val) :
      Transition cr receive target (.Some plaintext) (futureReceiveState cr receive target)

theorem receive_transition {AD PT CT Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
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
    ∃ nextReceive, KernelRefines (withInterpreter cr execute) origin send nextReceive result.1.1 ∧
      Transition (withInterpreter cr execute) receive target result.1.2 nextReceive := by
  by_cases failure : result.1.2 = .None
  · have same := RawCtxOwnerOracle.receive_failure_entry (receiveImpl execute opening)
      state entry target context result present failure
    exact ⟨receive, same ▸ refines, failure ▸ Transition.rejected⟩
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
      refine ⟨_, cached_finish_positioned (withInterpreter cr execute) origin send receive
        (target.val - 1) material opened hscoped plaintext, ?_⟩
      exact Transition.cached plaintext material positive stored
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
        refine ⟨_, future_finish_positioned (withInterpreter cr execute) origin send receive
          entry context target opened hscoped plaintext, ?_⟩
        exact Transition.future plaintext (by omega)
    · exact False.elim (rejected (refines.begin_receive_capacity_rejected (withInterpreter cr execute)
        origin send receive entry target context (by omega) (by omega)))

def Spent (receive : Ratchet.RecvState RatchetChain RatchetMaterial) (spent : List Nat) : Prop :=
  ∀ index ∈ spent, index < receive.n ∧ List.lookup index receive.skipped = none

theorem Transition.success_fresh {AD PT CT Plaintext : Type}
    {cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT}
    {receive next : Ratchet.RecvState RatchetChain RatchetMaterial}
    {target : Std.U64} {plaintext : Plaintext} {spent : List Nat}
    (step : Transition cr receive target (.Some plaintext) next)
    (invariant : Spent receive spent) : target.val - 1 ∉ spent := by
  cases step with
  | cached plaintext material positive stored =>
    intro consumed
    have absent := (invariant _ consumed).2
    rw [stored] at absent
    contradiction
  | future plaintext later =>
    intro consumed
    have earlier := (invariant _ consumed).1
    omega

def Past (receive : Ratchet.RecvState RatchetChain RatchetMaterial) : Prop :=
  ∀ pair ∈ receive.skipped, pair.1 < receive.n

theorem Transition.preserves_past {AD PT CT Plaintext : Type}
    {cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT}
    {receive next : Ratchet.RecvState RatchetChain RatchetMaterial}
    {target : Std.U64} {reply : core.option.Option Plaintext}
    (step : Transition cr receive target reply next) (past : Past receive) : Past next := by
  cases step with
  | rejected => exact past
  | cached plaintext material positive stored =>
    intro pair member
    exact past pair (List.mem_filter.mp member).1
  | future plaintext later =>
    intro pair member
    rcases List.mem_append.mp member with old | added
    · have before := past pair old
      dsimp only [futureReceiveState]
      omega
    · have range := Ratchet.mem_skipKeys_index cr receive.ck receive.n
        (target.val - receive.n - 1) added
      dsimp only [futureReceiveState]
      omega

def recordSpent {Plaintext : Type} (target : Std.U64)
    (reply : core.option.Option Plaintext) (spent : List Nat) : List Nat :=
  match reply with
  | .None => spent
  | .Some _ => (target.val - 1) :: spent

theorem Transition.preserves_spent {AD PT CT Plaintext : Type}
    {cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT}
    {receive next : Ratchet.RecvState RatchetChain RatchetMaterial}
    {target : Std.U64} {reply : core.option.Option Plaintext} {spent : List Nat}
    (step : Transition cr receive target reply next)
    (past : Past receive) (invariant : Spent receive spent) :
    Spent next (recordSpent target reply spent) := by
  cases step with
  | rejected => exact invariant
  | cached plaintext material positive stored =>
    intro index consumed
    rcases List.mem_cons.mp consumed with rfl | old
    · refine ⟨past _ (ratchet.control.mem_of_lookup_eq_some stored), ?_⟩
      simp [List.lookup_eq_none_iff, List.mem_filter, ne_comm]
    · refine ⟨(invariant index old).1, ?_⟩
      rw [List.lookup_eq_none_iff]
      intro pair member
      exact (List.lookup_eq_none_iff.mp (invariant index old).2) pair (List.mem_filter.mp member).1
  | future plaintext later =>
    intro index consumed
    rcases List.mem_cons.mp consumed with rfl | old
    · refine ⟨by dsimp only [futureReceiveState]; omega,
        Ratchet.lookup_eq_none_of_keys_lt (base := target.val - 1) ?_ (Nat.le_refl _)⟩
      intro pair member
      rcases List.mem_append.mp member with old | added
      · have before := past pair old
        omega
      · have range := Ratchet.mem_skipKeys_index cr receive.ck receive.n
          (target.val - receive.n - 1) added
        omega
    · refine ⟨by have earlier := (invariant index old).1; dsimp only [futureReceiveState]; omega, ?_⟩
      rw [List.lookup_eq_none_iff]
      intro pair member
      rcases List.mem_append.mp member with retained | added
      · exact (List.lookup_eq_none_iff.mp (invariant index old).2) pair retained
      · have range := Ratchet.mem_skipKeys_index cr receive.ck receive.n
          (target.val - receive.n - 1) added
        have earlier := (invariant index old).1
        simpa only [bne_iff_ne] using (show index ≠ pair.1 from by omega)

theorem Transition.spent_nodup {AD PT CT Plaintext : Type}
    {cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT}
    {receive next : Ratchet.RecvState RatchetChain RatchetMaterial}
    {target : Std.U64} {reply : core.option.Option Plaintext} {spent : List Nat}
    (step : Transition cr receive target reply next)
    (invariant : Spent receive spent) (unique : spent.Nodup) :
    (recordSpent target reply spent).Nodup := by
  cases reply with
  | none => exact unique
  | some plaintext => exact List.nodup_cons.mpr ⟨step.success_fresh invariant, unique⟩

noncomputable def crypto (c : Pqxdh.Crypto) := concreteCrypto c (RawCtxSourceHkdf.response c)

theorem native_receive_transition {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (origin : RatchetChain) (send : Ratchet.SendState RatchetChain)
    (receive : Ratchet.RecvState RatchetChain RatchetMaterial)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (refines : KernelRefines (crypto source.crypto) origin send receive entry)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support ((simulateQ
      (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
      (simulateQ RawCtxSourceOpen.ownerAdapter (RawCtxOwnerOracle.receive entry target context))).run primitive)) :
    ∃ nextReceive, KernelRefines (crypto source.crypto) origin send nextReceive result.1.1 ∧
      Transition (crypto source.crypto) receive target result.1.2 nextReceive := by
  rw [← source_receive_complete source (RawCtxOwnerOracle.receive entry target context) primitive [],
    support_map, Set.mem_image] at present
  obtain ⟨logged, hlogged, rfl⟩ := present
  exact receive_transition (crypto source.crypto) (RawCtxSourceHkdf.response source.crypto)
    origin send receive entry context target refines (sourceOpening source) (primitive, []) logged hlogged

def ConsumedRefines (c : Pqxdh.Crypto) (sendOrigin receiveOrigin : RatchetChain)
    (kernel : ConcreteRatchetKernel) (spent : List Nat) : Prop :=
  ∃ send receive, KernelRefines (crypto c) receiveOrigin send receive kernel ∧
    send.ck = Ratchet.chainAt (crypto c) sendOrigin send.n ∧
    Spent receive spent ∧ spent.Nodup

theorem native_receive_spent {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat)
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin entry spent)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support ((simulateQ
      (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
      (simulateQ RawCtxSourceOpen.ownerAdapter (RawCtxOwnerOracle.receive entry target context))).run primitive)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.1.1
      (recordSpent target result.1.2 spent) := by
  obtain ⟨send, receive, refines, aligned, consumed, unique⟩ := invariant
  obtain ⟨nextReceive, nextRefines, step⟩ := native_receive_transition source receiveOrigin send receive
    entry target context refines primitive result present
  exact ⟨send, nextReceive, nextRefines, aligned,
    step.preserves_spent refines.receiveControl.keys_lt consumed, step.spent_nodup consumed unique⟩

noncomputable def receiveNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :=
  RawCtxSharedPrimitive.nativeImpl (Auxiliary := Auxiliary) source.crypto (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxSourceOpen.nativeAdapter

def recordReply (reply : core.option.Option RawCtxWholeOwner.Decrypted) (spent : List Nat) : List Nat :=
  match reply with
  | .None => spent
  | .Some message => (message.sequence.val - 1) :: spent

theorem recordReply_eq (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (target : Std.U64) (spent : List Nat)
    (metadata : ∀ message, reply = .Some message → message.sequence = target) :
    recordReply reply spent = recordSpent target reply spent := by
  cases reply with
  | none => rfl
  | some message => simp only [recordReply, recordSpent, metadata message rfl]

theorem raw_spent {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.owner.kernel spent)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxWholeOwner.rawGame (receiveNative source) decode raw state primitive)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.1.2.owner.kernel
      (recordReply result.1.1 spent) := by
  have metadata := RawCtxOwnerProvenance.raw_success_metadata (receiveNative source)
    decode raw state primitive result present
  unfold RawCtxWholeOwner.rawGame RawCtxWholeOwner.rawReceive StateT.run at present
  split at present
  · change result ∈ support ((simulateQ (receiveNative source)
        (pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None)))).run primitive) at present
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
    subst result
    exact invariant
  · split at present
    · change result ∈ support ((simulateQ (receiveNative source)
          (pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None)))).run primitive) at present
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
      subst result
      exact invariant
    · unfold StateT.run at present
      split at present
      · rw [simulateQ_bind] at present
        change result ∈ support (StateT.run _ primitive) at present
        simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at present
        obtain ⟨opened, hopen, rfl⟩ := present
        rename_i nonempty parsed frame decoded valid
        have mapped : recordReply opened.1.2 spent = recordSpent frame.sequence opened.1.2 spent :=
          recordReply_eq opened.1.2 frame.sequence spent (by
            intro message success
            obtain ⟨actual, hactual, _, _, sequence⟩ := metadata message success
            have same : actual = frame := Option.some.inj (hactual.symm.trans decoded)
            simpa only [same] using sequence)
        change ConsumedRefines source.crypto sendOrigin receiveOrigin opened.1.1 (recordReply opened.1.2 spent)
        rw [mapped]
        apply native_receive_spent source sendOrigin receiveOrigin spent state.owner.kernel
          frame.sequence ⟨raw, frame, state.owner.associatedData⟩ invariant primitive opened
        simpa only [receiveNative, RawCtxSourceOpen.ownerAdapter, QueryImpl.simulateQ_compose] using hopen
      · change result ∈ support ((simulateQ (receiveNative source)
            (pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None)))).run primitive) at present
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
        subst result
        exact invariant

noncomputable def sendNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :=
  RawCtxMixedShared.sharedImpl (Auxiliary := Auxiliary) source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxMixedOwner.sendAdapter

theorem native_send_spent {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat)
    (entry : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin entry spent)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support ((simulateQ
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      (simulateQ RawCtxMixedOwner.sendAdapter
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send entry context)))).run primitive)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.1.1 spent := by
  rw [← source_send_complete source writer (RawCtxSourceSend.send entry context) primitive [],
    support_map, Set.mem_image] at present
  obtain ⟨logged, hlogged, rfl⟩ := present
  obtain ⟨send, receive, refines, aligned, consumed, unique⟩ := invariant
  obtain ⟨nextSend, preserved, nextAligned⟩ := send_preserves_positions (crypto source.crypto)
    (RawCtxSourceHkdf.response source.crypto) receiveOrigin sendOrigin send receive entry context refines aligned
    (sourceSealing source writer) (primitive, []) logged hlogged
  exact ⟨nextSend, receive, preserved, nextAligned, consumed, unique⟩

theorem send_spent {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (spent : List Nat) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.owner.kernel spent)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) ×
      RawCtxSharedPrimitive.SharedState Auxiliary)
    (present : result ∈ support (RawCtxSourceSend.sendGame (sendNative source writer)
      sender plaintext state primitive)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.1.2.owner.kernel spent := by
  unfold RawCtxSourceSend.sendGame RawCtxSourceSend.sendOwner StateT.run at present
  split at present
  all_goals change result ∈ support ((simulateQ (sendNative source writer) _).run primitive) at present
  · change result ∈ support ((simulateQ (sendNative source writer)
        (pure (none, state))).run primitive) at present
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
    subst result
    exact invariant
  · change result ∈ support ((simulateQ (sendNative source writer) (do
        let sealed ← simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send state.owner.kernel {
          plaintext := plaintext, targetId := state.owner.expectedSender,
          senderId := sender, associatedData := state.owner.associatedData })
        pure (sealed.2, { state with owner := { state.owner with kernel := sealed.1 } }))).run
          primitive) at present
    rw [simulateQ_bind] at present
    change result ∈ support (StateT.run _ primitive) at present
    simp only [StateT.run_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at present
    obtain ⟨sealed, hseal, rfl⟩ := present
    apply native_send_spent source writer sendOrigin receiveOrigin spent state.owner.kernel _ invariant primitive sealed
    simpa only [sendNative, QueryImpl.simulateQ_compose] using hseal

theorem shared_receiveNative {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    (RawCtxMixedShared.sharedImpl (Auxiliary := Auxiliary) source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
      RawCtxMixedOwner.receiveAdapter) = receiveNative source := by
  funext query
  change simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
    (simulateQ RawCtxMixedOwner.receiveLift (RawCtxSourceOpen.nativeAdapter query)) =
      simulateQ (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source))
        (RawCtxSourceOpen.nativeAdapter query)
  rw [← QueryImpl.simulateQ_compose, RawCtxMixedShared.shared_receive]

def recordSource (query : RawCtxMixedOwner.SourceSpec.Domain)
    (reply : RawCtxMixedOwner.SourceSpec.Range query) (spent : List Nat) : List Nat :=
  match query with
  | .inl _ => spent
  | .inr _ => recordReply reply spent

noncomputable def trackedImpl {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec
      (StateT ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat) ProbComp) :=
  fun query state => do
    let result ← (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode query).run state.1
    pure (result.1, (result.2, recordSource query result.1 state.2))

theorem tracked_step_spent {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2)
    (result : RawCtxMixedOwner.SourceSpec.Range query ×
      ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat))
    (present : result ∈ support ((trackedImpl source writer sender decode query).run state)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.1.owner.kernel result.2.2 := by
  unfold trackedImpl StateT.run at present
  obtain ⟨actual, hactual, returned⟩ := mem_support_bind_peel _ _ present
  have equal := eq_of_mem_support_pure _ returned
  subst result
  cases query with
  | inl plaintext =>
    change actual ∈ support ((do
      let sent ← RawCtxSourceSend.sendGame (sendNative source writer) sender plaintext state.1.1 state.1.2
      pure (sent.1.1, (sent.1.2, sent.2))) : ProbComp _) at hactual
    obtain ⟨sent, hsent, returned⟩ := mem_support_bind_peel _ _ hactual
    have equal := eq_of_mem_support_pure _ returned
    subst actual
    exact send_spent source writer sendOrigin receiveOrigin state.2 sender plaintext state.1.1 invariant state.1.2 sent hsent
  | inr raw =>
    simp only [RawCtxMixedOwner.sourceImpl, shared_receiveNative] at hactual
    change actual ∈ support ((do
      let received ← RawCtxWholeOwner.rawGame (receiveNative source) decode raw state.1.1 state.1.2
      pure (received.1.1, (received.1.2, received.2))) : ProbComp _) at hactual
    obtain ⟨received, hreceived, returned⟩ := mem_support_bind_peel _ _ hactual
    have equal := eq_of_mem_support_pure _ returned
    subst actual
    exact raw_spent source sendOrigin receiveOrigin state.2 decode raw state.1.1 invariant state.1.2 received hreceived

theorem tracked_schedule_spent {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2)
    (result : Result × ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat))
    (present : result ∈ support ((simulateQ (trackedImpl source writer sender decode) client).run state)) :
    ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.1.owner.kernel result.2.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value => simpa using present ▸ invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
    obtain ⟨reply, hreply, htail⟩ := present
    exact ih reply.1 reply.2
      (tracked_step_spent source writer sendOrigin receiveOrigin sender decode query state invariant reply hreply)
      result htail

theorem tracked_erasure {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat) :
    (fun result => (result.1, result.2.1)) <$> ((simulateQ (trackedImpl source writer sender decode) client).run (state, spent)) =
      (simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state spent with
  | pure value => simp [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    simp only [StateT.run, trackedImpl, bind_assoc, pure_bind]
    congr 1
    funext actual
    exact ih actual.1 actual.2 (recordSource query actual.1 spent)

theorem tracked_step_length {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (result : RawCtxMixedOwner.SourceSpec.Range query ×
      ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat))
    (present : result ∈ support ((trackedImpl source writer sender decode query).run state)) :
    result.2.2.length ≤ state.2.length + (if query.isRight then 1 else 0) := by
  unfold trackedImpl StateT.run at present
  obtain ⟨actual, _, returned⟩ := mem_support_bind_peel _ _ present
  have equal := eq_of_mem_support_pure _ returned
  subst result
  cases query with
  | inl plaintext => simp [recordSource]
  | inr raw =>
    cases reply : actual.1 with
    | none => simp [recordSource, recordReply]
    | some message => simp [recordSource, recordReply]

theorem tracked_schedule_length {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (qRaw : Nat) (bounded : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (result : Result × ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat))
    (present : result ∈ support ((simulateQ (trackedImpl source writer sender decode) client).run state)) :
    result.2.2.length ≤ state.2.length + qRaw := by
  induction client using OracleComp.inductionOn generalizing qRaw state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at present
    subst result
    simp
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at present
    obtain ⟨reply, hreply, htail⟩ := present
    have step := tracked_step_length source writer sender decode query state reply hreply
    cases query with
    | inl plaintext =>
      simp at bounded step
      have tail := ih reply.1 qRaw (bounded reply.1) reply.2 result htail
      omega
    | inr raw =>
      simp at bounded step
      have tail := ih reply.1 (qRaw - 1) (bounded.2 reply.1) reply.2 result htail
      omega

open BeaconcryptCore.Refinement.PqxdhConcreteSession

theorem initialized_spent (c : Pqxdh.Crypto) (root : Std.Array Std.U8 32#usize)
    (kernel : ConcreteRatchetKernel)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse c) = ok kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse c) = ok kernel) :
    ConsumedRefines c kernel.refined.send_chain kernel.refined.receive_chain kernel [] := by
  rcases initialized with beacon | server
  · obtain ⟨actual, returned, _, _, refined⟩ := beacon_initial_positions c root
    have equal : actual = kernel := by simpa [beacon] using returned.symm
    subst actual
    exact ⟨_, _, refined, rfl, by simp [Spent], List.nodup_nil⟩
  · obtain ⟨actual, returned, _, _, refined⟩ := server_initial_positions c root
    have equal : actual = kernel := by simpa [server] using returned.symm
    subst actual
    exact ⟨_, _, refined, rfl, by simp [Spent], List.nodup_nil⟩

theorem ConsumedRefines.spent_nodup {c : Pqxdh.Crypto} {sendOrigin receiveOrigin : RatchetChain}
    {kernel : ConcreteRatchetKernel} {spent : List Nat}
    (invariant : ConsumedRefines c sendOrigin receiveOrigin kernel spent) : spent.Nodup := by
  obtain ⟨send, receive, refines, aligned, consumed, unique⟩ := invariant
  exact unique

theorem source_supported_history {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (root : Std.Array Std.U8 32#usize) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (qRaw : Nat) (bounded : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel ∨
      initializeServer root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (present : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      sender decode) client).run state)) :
    ∃ spent, (result.1, (result.2, spent)) ∈ support
        ((simulateQ (trackedImpl source writer sender decode) client).run (state, [])) ∧
      ConsumedRefines source.crypto state.1.owner.kernel.refined.send_chain
        state.1.owner.kernel.refined.receive_chain result.2.1.owner.kernel spent ∧
      spent.Nodup ∧ spent.length ≤ qRaw := by
  rw [← tracked_erasure source writer sender decode client state [], support_map, Set.mem_image] at present
  obtain ⟨tracked, htracked, rfl⟩ := present
  have invariant := tracked_schedule_spent source writer _ _ sender decode client (state, [])
    (initialized_spent source.crypto root state.1.owner.kernel initialized) tracked htracked
  refine ⟨tracked.2.2, htracked, invariant, invariant.spent_nodup, ?_⟩
  simpa only [List.length_nil, Nat.zero_add] using
    tracked_schedule_length source writer sender decode client qRaw bounded (state, []) tracked htracked

theorem tracked_query_bounds {Metadata Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (spent : List Nat) (predicate : unifSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (trackedImpl source writer sender decode) client).run (state, spent)).IsQueryBoundP predicate budget ↔
      ((simulateQ (RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state).IsQueryBoundP predicate budget := by
  rw [← tracked_erasure source writer sender decode client state spent, isQueryBoundP_map_iff]

theorem tracked_raw_success_fresh {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes)
    (state : (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat)
    (invariant : ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.1.owner.kernel state.2)
    (result : core.option.Option RawCtxWholeOwner.Decrypted ×
      ((RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary) × List Nat))
    (present : result ∈ support ((trackedImpl source writer sender decode (.inr raw)).run state))
    (message : RawCtxWholeOwner.Decrypted) (accepted : result.1 = .Some message) :
    message.sequence.val - 1 ∉ state.2 := by
  have preserved := tracked_step_spent source writer sendOrigin receiveOrigin sender decode
    (.inr raw) state invariant result present
  unfold trackedImpl StateT.run at present
  obtain ⟨actual, _, returned⟩ := mem_support_bind_peel _ _ present
  have equal := eq_of_mem_support_pure _ returned
  subst result
  have unique := preserved.spent_nodup
  change actual.1 = .Some message at accepted
  simp only [recordSource, accepted, recordReply, List.nodup_cons] at unique
  exact unique.1

end BeaconcryptCore.Computational.RawCtxReceiveConsumption

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.receive_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.receive_transition

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.success_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.success_fresh

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.preserves_past' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.preserves_past

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.preserves_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.preserves_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.spent_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.Transition.spent_nodup

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.native_receive_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.native_receive_transition

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.native_receive_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.native_receive_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.recordReply_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.recordReply_eq

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.raw_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.raw_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.native_send_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.native_send_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.send_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.send_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.shared_receiveNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.shared_receiveNative

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_step_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_step_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_schedule_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_schedule_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_erasure

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_step_length

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_schedule_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_schedule_length

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.initialized_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.initialized_spent

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.ConsumedRefines.spent_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.ConsumedRefines.spent_nodup

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.source_supported_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.source_supported_history

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_query_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_raw_success_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReceiveConsumption.tracked_raw_success_fresh
