import BeaconcryptCore.Computational.RawCtxSourceSeal
import BeaconcryptCore.Computational.RawCtxKdfBudget

/-!
# One serialized owner for source sends and raw receives

The exact source executors share one whole kernel and complete external primitive
state. Both commitment directions use the same hash request branch; all ratchet
calls use the same KDF branch. Fixed local sender metadata is separate from the
application plaintext and incoming raw bytes. Every optional reply reaches the
original continuation, including failed-send advancement and receive rollback.

These are operational equalities and source-derived interface call caps, not
cryptographic security for evolving keys. The client interface here contains only
send and raw-receive requests; primitive randomness is retained in its interpreter.
Native role/codec/storage correspondence, other client services and explicit client
coin routing, shared-HKDF consistency, key distributions, global freshness and
multi-owner security remain separate. Local copying/serialization/primitive work
is not made free by the query ledger. Noncomputable inherited source normalizers
are not a compiled-runtime claim.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxMixedOwner

abbrev SealAeadSpec := RawCtxSourceSeal.AeadInput →ₒ Option (Pqxdh.Bytes × Pqxdh.Bytes)
abbrev OpenAeadSpec := RawCtxSourceOpen.BaseInput →ₒ Option Pqxdh.Bytes
abbrev HashSpec := Pqxdh.Bytes →ₒ Option Pqxdh.Bytes
abbrev WriterSpec := RawCtxReceive.DecodedFrame →ₒ Option Pqxdh.Bytes
abbrev NativeSpec := RawCtxSharedPrimitive.KdfSpec + (SealAeadSpec + (OpenAeadSpec + (HashSpec + WriterSpec)))

def receiveLift : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp NativeSpec)
  | .inl request => NativeSpec.query (.inl request)
  | .inr (.inl bytes) => NativeSpec.query (.inr (.inr (.inr (.inl bytes))))
  | .inr (.inr input) => NativeSpec.query (.inr (.inr (.inl input)))

def sendLift : QueryImpl RawCtxSourceSeal.NativeSpec (OracleComp NativeSpec)
  | .inl request => NativeSpec.query (.inl request)
  | .inr (.inl input) => NativeSpec.query (.inr (.inl input))
  | .inr (.inr (.inl bytes)) => NativeSpec.query (.inr (.inr (.inr (.inl bytes))))
  | .inr (.inr (.inr frame)) => NativeSpec.query (.inr (.inr (.inr (.inr frame))))

/-- Both directions issue literally the same typed hash query for the same bytes. -/
theorem same_hash (bytes : Pqxdh.Bytes) :
    receiveLift (.inr (.inl bytes)) = sendLift (.inr (.inr (.inl bytes))) := by
  rfl

/-- Both directions issue literally the same typed ratchet KDF query. -/
theorem same_kdf (request : SymmetricRatchetKdfRequest) :
    receiveLift (.inl request) = sendLift (.inl request) := by
  rfl

def receiveAdapter : QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp NativeSpec) :=
  receiveLift ∘ₛ RawCtxSourceOpen.nativeAdapter

def sendAdapter : QueryImpl RawCtxSourceSend.PrimitiveSpec (OracleComp NativeSpec) :=
  sendLift ∘ₛ RawCtxSourceSeal.nativeAdapter

abbrev SourceSpec := RawCtxSourceSend.ApplicationSpec + RawCtxWholeOwner.RawSpec

noncomputable def ownerImpl {Metadata : Type} (senderId : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (RawCtxWholeOwner.OwnerState Metadata) (OracleComp NativeSpec)) :=
  fun query owner => match query with
  | .inl plaintext => simulateQ sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run owner)
  | .inr raw => simulateQ receiveAdapter ((RawCtxWholeOwner.rawReceive decode raw).run owner)

noncomputable def sourceImpl {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl SourceSpec (StateT (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) (OracleComp base)) :=
  fun query => match query with
  | .inl plaintext => RawCtxSourceSend.ownerImpl (impl ∘ₛ sendAdapter) senderId plaintext
  | .inr raw => RawCtxWholeOwner.ownerImpl (impl ∘ₛ receiveAdapter) decode raw

/-- One mixed step retains the actual optional reply, whole owner and complete primitive state. -/
theorem owner_interpretation {Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    (impl.mapStateTBase (ownerImpl (Metadata := Metadata) senderId decode)).flattenStateT =
      sourceImpl impl senderId decode := by
  funext query state
  cases query <;>
    simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
      ownerImpl, sourceImpl, RawCtxSourceSend.ownerImpl, RawCtxSourceSend.sendGame,
      RawCtxWholeOwner.ownerImpl, RawCtxWholeOwner.rawGame,
      ← QueryImpl.simulateQ_compose, bind_pure_comp] <;> rfl

/-- Arbitrary adaptive interleaving preserves the entire source computation, with only state-pair reassociation. -/
theorem schedule_interpretation {Metadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (ownerImpl senderId decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl impl senderId decode) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, owner_interpretation]

inductive CallKind where
  | kdf | sealing | opening | hash | writer
  deriving DecidableEq

def callKind : NativeSpec.Domain → CallKind
  | .inl _ => .kdf
  | .inr (.inl _) => .sealing
  | .inr (.inr (.inl _)) => .opening
  | .inr (.inr (.inr (.inl _))) => .hash
  | .inr (.inr (.inr (.inr _))) => .writer

def receiveKind : RawCtxSourceOpen.NativeSpec.Domain → CallKind
  | .inl _ => .kdf
  | .inr (.inl _) => .hash
  | .inr (.inr _) => .opening

def sendKind : RawCtxSourceSeal.NativeSpec.Domain → CallKind
  | .inl _ => .kdf
  | .inr (.inl _) => .sealing
  | .inr (.inr (.inl _)) => .hash
  | .inr (.inr (.inr _)) => .writer

def receiveCost : CallKind → Nat
  | .kdf => 51
  | .opening | .hash => 1
  | .sealing | .writer => 0

def sendCost : CallKind → Nat
  | .opening => 0
  | _ => 1

/-- Embedding receive effects preserves each counted primitive category. -/
theorem receiveLift_bound {Result : Type} (kind : CallKind)
    (program : OracleComp RawCtxSourceOpen.NativeSpec Result) (bound : Nat)
    (hbound : program.IsQueryBoundP (fun query => receiveKind query = kind) bound) :
    (simulateQ receiveLift program).IsQueryBoundP (fun query => callKind query = kind) bound := by
  apply RawCtxSourceOpen.simulate_bound receiveLift _ _ program bound hbound
  rintro (request | (bytes | input))
  all_goals apply (isQueryBoundP_query_iff (spec := NativeSpec)
    (p := fun query => callKind query = kind) _ _).2
  all_goals simp only [receiveKind, callKind]
  all_goals split_ifs <;> simp_all

/-- Embedding send effects preserves each counted primitive category. -/
theorem sendLift_bound {Result : Type} (kind : CallKind)
    (program : OracleComp RawCtxSourceSeal.NativeSpec Result) (bound : Nat)
    (hbound : program.IsQueryBoundP (fun query => sendKind query = kind) bound) :
    (simulateQ sendLift program).IsQueryBoundP (fun query => callKind query = kind) bound := by
  apply RawCtxSourceOpen.simulate_bound sendLift _ _ program bound hbound
  rintro (request | (input | (bytes | frame)))
  all_goals apply (isQueryBoundP_query_iff (spec := NativeSpec)
    (p := fun query => callKind query = kind) _ _).2
  all_goals simp only [sendKind, callKind]
  all_goals split_ifs <;> simp_all

/-- Every raw attempt has the source-window KDF bound and separate hash/open caps, including all failures. -/
theorem receive_bounds {Metadata : Type} (senderId : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (kind : CallKind) :
    ((ownerImpl senderId decode (.inr raw)).run state).IsQueryBoundP
      (fun query => callKind query = kind) (receiveCost kind) := by
  change (simulateQ (receiveLift ∘ₛ RawCtxSourceOpen.nativeAdapter)
    (RawCtxWholeOwner.rawReceive decode raw state)).IsQueryBoundP _ _
  rw [QueryImpl.simulateQ_compose]
  apply receiveLift_bound
  cases kind <;> simp only [receiveCost]
  case kdf =>
      convert RawCtxKdfBudget.raw_bound decode raw state using 1
      funext query
      rcases query with request | (bytes | input) <;> simp [receiveKind]
  case opening =>
      convert (RawCtxSourceOpen.raw_primitive_bounds decode raw state).2 using 1
      funext query
      rcases query with request | (bytes | input) <;>
        simp [receiveKind, RawCtxSourceOpen.openingPredicate]
  case hash =>
      convert (RawCtxSourceOpen.raw_primitive_bounds decode raw state).1 using 1
      funext query
      rcases query with request | (bytes | input) <;>
        simp [receiveKind, RawCtxSourceOpen.openingPredicate]
  case sealing =>
      convert isQueryBoundP_false
        (simulateQ RawCtxSourceOpen.nativeAdapter (RawCtxWholeOwner.rawReceive decode raw state)) 0 using 1
      funext query
      rcases query with request | (bytes | input) <;> simp [receiveKind]
  case writer =>
      convert isQueryBoundP_false
        (simulateQ RawCtxSourceOpen.nativeAdapter (RawCtxWholeOwner.rawReceive decode raw state)) 0 using 1
      funext query
      rcases query with request | (bytes | input) <;> simp [receiveKind]

/-- Every application send has separate KDF/seal/hash/writer caps, including empty, exhausted and failed requests. -/
theorem send_bounds {Metadata : Type} (senderId : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (kind : CallKind) :
    ((ownerImpl senderId decode (.inl plaintext)).run state).IsQueryBoundP
      (fun query => callKind query = kind) (sendCost kind) := by
  change (simulateQ (sendLift ∘ₛ RawCtxSourceSeal.nativeAdapter)
    ((RawCtxSourceSend.sendOwner senderId plaintext).run state)).IsQueryBoundP _ _
  rw [QueryImpl.simulateQ_compose]
  apply sendLift_bound
  cases kind <;> simp only [sendCost]
  case kdf =>
      convert (RawCtxSourceSeal.nativeSend_bounds senderId plaintext state).1 using 1
      funext query
      rcases query with request | (input | (bytes | frame)) <;> simp [sendKind]
  case sealing =>
      convert (RawCtxSourceSeal.nativeSend_bounds senderId plaintext state).2 .aead using 1
      funext query
      rcases query with request | (input | (bytes | frame)) <;>
        simp [sendKind, RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]
  case hash =>
      convert (RawCtxSourceSeal.nativeSend_bounds senderId plaintext state).2 .hash using 1
      funext query
      rcases query with request | (input | (bytes | frame)) <;>
        simp [sendKind, RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]
  case writer =>
      convert (RawCtxSourceSeal.nativeSend_bounds senderId plaintext state).2 .writer using 1
      funext query
      rcases query with request | (input | (bytes | frame)) <;>
        simp [sendKind, RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]
  case opening =>
      convert isQueryBoundP_false
        (simulateQ RawCtxSourceSeal.nativeAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run state)) 0 using 1
      funext query
      rcases query with request | (input | (bytes | frame)) <;> simp [sendKind]

/-- Selective all-continuation request caps compose through one shared owner without a schedule factor. -/
theorem schedule_bound {Metadata Result : Type} (senderId : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result)
    (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : RawCtxWholeOwner.OwnerState Metadata) (kind : CallKind) :
    ((simulateQ (ownerImpl senderId decode) client).run state).IsQueryBoundP
      (fun query => callKind query = kind) (sendCost kind * qSend + receiveCost kind * qRaw) := by
  induction client using OracleComp.inductionOn generalizing qSend qRaw state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hSend hRaw
      rw [simulateQ_query_bind, StateT.run_bind]
      cases query with
      | inl plaintext =>
          simp only [Sum.isLeft, Sum.isRight, Bool.false_eq_true, not_true_eq_false,
            false_or, ↓reduceIte] at hSend hRaw
          apply (isQueryBoundP_bind (send_bounds senderId decode plaintext state kind)
            (fun result _ => ih result.1 (qSend - 1) qRaw (hSend.2 result.1)
              (hRaw.2 result.1) result.2)).mono
          cases kind <;> simp only [sendCost, receiveCost] <;> omega
      | inr raw =>
          simp only [Sum.isLeft, Sum.isRight, Bool.false_eq_true, not_true_eq_false,
            false_or, ↓reduceIte] at hSend hRaw
          apply (isQueryBoundP_bind (receive_bounds senderId decode raw state kind)
            (fun result _ => ih result.1 qSend (qRaw - 1) (hSend.2 result.1)
              (hRaw.2 result.1) result.2)).mono
          cases kind <;> simp only [sendCost, receiveCost] <;> omega

/-- The five concrete ledgers retain all attempted calls and the actual source receive-window coefficient. -/
theorem schedule_bounds {Metadata Result : Type} (senderId : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result)
    (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    let program := (simulateQ (ownerImpl senderId decode) client).run state
    program.IsQueryBoundP (fun query => callKind query = .kdf) (qSend + 51 * qRaw) ∧
      program.IsQueryBoundP (fun query => callKind query = .sealing) qSend ∧
      program.IsQueryBoundP (fun query => callKind query = .opening) qRaw ∧
      program.IsQueryBoundP (fun query => callKind query = .hash) (qSend + qRaw) ∧
      program.IsQueryBoundP (fun query => callKind query = .writer) qSend := by
  simpa only [sendCost, receiveCost, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using
    And.intro (schedule_bound senderId decode client qSend qRaw hSend hRaw state .kdf)
      (And.intro (schedule_bound senderId decode client qSend qRaw hSend hRaw state .sealing)
        (And.intro (schedule_bound senderId decode client qSend qRaw hSend hRaw state .opening)
          (And.intro (schedule_bound senderId decode client qSend qRaw hSend hRaw state .hash)
            (schedule_bound senderId decode client qSend qRaw hSend hRaw state .writer))))

def ownerFields {Metadata : Type} (state : RawCtxWholeOwner.OwnerState Metadata) :=
  (state.owner.expectedSender, state.owner.associatedData, state.owner.metadata)

/-- Only raw requests increment the outer receive counter; both directions retain immutable owner fields. -/
theorem source_step {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : SourceSpec.Domain)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (result : SourceSpec.Range query × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (supported : result ∈ support ((sourceImpl impl senderId decode query).run state)) :
    result.2.1.rawAttempts = state.1.rawAttempts + (if query.isRight then 1 else 0) ∧
      ownerFields result.2.1 = ownerFields state.1 := by
  cases query with
  | inl plaintext =>
      change Option RawCtxSourceSend.Encrypted × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) at result
      change result ∈ support (RawCtxSourceSend.sendGame (impl ∘ₛ sendAdapter)
        senderId plaintext state.1 state.2 >>= fun sent => pure (sent.1.1, (sent.1.2, sent.2))) at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨sent, hsent, rfl⟩ := supported
      have metadata := RawCtxSourceSend.sendGame_publication (impl ∘ₛ sendAdapter)
        senderId plaintext state.1 state.2 sent hsent
      simp only [Sum.isRight, Bool.false_eq_true, if_false, Nat.add_zero, ownerFields,
        metadata.1, metadata.2.1, metadata.2.2.1, metadata.2.2.2, and_self]
  | inr raw =>
      change core.option.Option RawCtxWholeOwner.Decrypted × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) at result
      change result ∈ support (RawCtxWholeOwner.rawGame (impl ∘ₛ receiveAdapter)
        decode raw state.1 state.2 >>= fun sent => pure (sent.1.1, (sent.1.2, sent.2))) at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨sent, hsent, rfl⟩ := supported
      have metadata := RawCtxWholeOwner.rawGame_preserves_metadata (impl ∘ₛ receiveAdapter)
        decode raw state.1 state.2 sent hsent
      simp only [Sum.isRight, if_true, ownerFields,
        metadata.1, metadata.2.1, metadata.2.2.1, metadata.2.2.2, and_self]

/-- The actual mixed schedule bounds its receive counter and preserves route, AD and complete metadata. -/
theorem source_schedule {Metadata PrimitiveState Result : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (qRaw : Nat)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (supported : result ∈ support ((simulateQ (sourceImpl impl senderId decode) client).run state)) :
    result.2.1.rawAttempts ≤ state.1.rawAttempts + qRaw ∧
      ownerFields result.2.1 = ownerFields state.1 := by
  induction client using OracleComp.inductionOn generalizing qRaw state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨Nat.le_add_right _ _, rfl⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hRaw
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, hstep, htail⟩ := supported
      have hlocal := source_step impl senderId decode query state step hstep
      have rest := ih step.1 _ (hRaw.2 step.1) step.2 result htail
      refine ⟨?_, rest.2.trans hlocal.2⟩
      by_cases right : query.isRight = true
      · simp only [right, if_true] at hlocal rest
        have positive : 0 < qRaw := hRaw.1.resolve_left (not_not.mpr right)
        omega
      · simp only [right, Bool.false_eq_true, if_false, Nat.add_zero] at hlocal rest
        omega

end BeaconcryptCore.Computational.RawCtxMixedOwner

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.same_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.same_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.same_kdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.same_kdf

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.owner_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.owner_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.receiveLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.receiveLift_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.sendLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.sendLift_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.receive_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.receive_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.send_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.send_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.schedule_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.schedule_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.schedule_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.source_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedOwner.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedOwner.source_schedule
