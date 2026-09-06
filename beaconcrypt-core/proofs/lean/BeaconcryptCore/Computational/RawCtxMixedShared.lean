import BeaconcryptCore.Computational.RawCtxMixedOwner

/-!
# Mixed source execution with one actual commitment cache

The common primitive interface is interpreted through the existing source-opening
KDF/hash/open surface. Both directions use the same actual CTX random-oracle cache.
KDF callbacks retain the entire auxiliary/cache pair. Detached AEAD sealing uses
the existing total functional Crypto interface, and the writer is an optional
functional codec; their local computation is not charged as uniform queries.

This instantiates a stronger total-ROM/perfect-AEAD source presentation, not every
optional native hash/AEAD implementation. The preceding MixedOwner equalities
retain arbitrary optional native effects. Writer success does not imply successful
native parsing, canonical encoding, availability or a byte-work bound. The same
cache does not by itself establish consistency of an arbitrary KDF handler with
actual shared HKDF queries. No key independence, fixed-key security transfer,
reveal policy or global cryptographic conclusion follows from these equalities.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxMixedShared
open RawCtxMixedOwner

abbrev Writer := RawCtxReceive.DecodedFrame → Option Pqxdh.Bytes

/-- Total functional sealing and optional functional writing use no additional random oracle; both hash directions forward the same existing source query. -/
def sharedAdapter (c : Pqxdh.Crypto) (writer : Writer) :
    QueryImpl NativeSpec (OracleComp RawCtxSourceOpen.NativeSpec)
  | .inl request => RawCtxSourceOpen.NativeSpec.query (.inl request)
  | .inr (.inl input) => pure (some (c.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inr (.inl input)) => RawCtxSourceOpen.NativeSpec.query (.inr (.inr input))
  | .inr (.inr (.inr (.inl bytes))) => RawCtxSourceOpen.NativeSpec.query (.inr (.inl bytes))
  | .inr (.inr (.inr (.inr frame))) => pure (writer frame)

noncomputable def sharedImpl {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    QueryImpl NativeSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  RawCtxSharedPrimitive.nativeImpl c kdf ∘ₛ sharedAdapter c writer

/-- The same receive service is retained inside arbitrary mixed execution, including every rejected lookup and cache effect. -/
theorem shared_receive {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    sharedImpl c writer kdf ∘ₛ receiveLift = RawCtxSharedPrimitive.nativeImpl c kdf := by
  funext query
  rcases query with request | (bytes | input)
  all_goals simp [QueryImpl.compose, receiveLift, sharedImpl, sharedAdapter, OracleSpec.query]

/-- Every commitment query uses the same existing cache and retains its actual updated state. -/
theorem shared_hash {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (bytes : Pqxdh.Bytes) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((sharedImpl c writer kdf (.inr (.inr (.inr (.inl bytes))))).run state) = (do
      let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2
      pure (some result.1.toList, (state.1, result.2))) := by
  simp [sharedImpl, sharedAdapter, QueryImpl.compose, OracleSpec.query]
  change (do
    let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2
    pure (some result.1.toList, (state.1, result.2))) = _
  rw [bind_pure_comp]
  rfl

/-- The functional detached AEAD presentation returns its true ciphertext/tag and preserves the full shared state. -/
theorem shared_sealing {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSeal.AeadInput) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((sharedImpl c writer kdf (.inr (.inl input))).run state) =
      pure (some (c.aeadSeal input.key input.nonce input.associatedData input.plaintext), state) := by
  simp [sharedImpl, sharedAdapter, QueryImpl.compose, StateT.run_pure]

/-- The optional functional writer returns exactly its actual bytes or failure without changing the shared state. -/
theorem shared_writing {Auxiliary : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (frame : RawCtxReceive.DecodedFrame) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((sharedImpl c writer kdf (.inr (.inr (.inr (.inr frame))))).run state) =
      pure (writer frame, state) := by
  simp [sharedImpl, sharedAdapter, QueryImpl.compose, StateT.run_pure]

/-- Local functional sealing/writing add no uniform queries; the actual forwarded primitive categories retain their caps. -/
theorem sharedAdapter_bound {Result : Type} (c : Pqxdh.Crypto) (writer : Writer) (kind : CallKind)
    (client : OracleComp NativeSpec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (fun query => callKind query = kind) bound) :
    (simulateQ (sharedAdapter c writer) client).IsQueryBoundP
      (fun query => receiveKind query = kind) bound := by
  apply RawCtxSourceOpen.simulate_bound (sharedAdapter c writer) _ _ client bound bounded
  rintro (request | (input | (opening | (bytes | frame))))
  all_goals first
    | exact isQueryBoundP_pure _ _ _
    | apply (isQueryBoundP_query_iff (spec := RawCtxSourceOpen.NativeSpec)
        (p := fun query => receiveKind query = kind) _ _).2
  all_goals simp only [receiveKind, callKind]
  all_goals split_ifs <;> simp_all

/-- Arbitrary mixed primitive execution charges each KDF callback and every commitment miss through the same full state. -/
theorem shared_uniform {Auxiliary Result : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (client : OracleComp NativeSpec Result) (qKdf qHash : Nat)
    (hKdf : client.IsQueryBoundP (fun query => callKind query = .kdf) qKdf)
    (hHash : client.IsQueryBoundP (fun query => callKind query = .hash) qHash)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (sharedImpl c writer kdf) client).run state).IsTotalQueryBound
      (kdfCoins * qKdf + 64 * qHash) := by
  rw [sharedImpl, QueryImpl.simulateQ_compose]
  apply RawCtxSharedPrimitive.native_uniform_bound c kdf kdfCoins bounded _ qKdf qHash
  · convert sharedAdapter_bound c writer .kdf client qKdf hKdf using 1
    funext query
    rcases query with request | (bytes | input) <;> simp [receiveKind]
  · convert sharedAdapter_bound c writer .hash client qHash hHash using 1
    funext query
    rcases query with request | (bytes | input) <;>
      simp [receiveKind, RawCtxSourceOpen.openingPredicate]

noncomputable def sharedSchedule {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ProbComp ((Result × RawCtxWholeOwner.OwnerState Metadata) × RawCtxSharedPrimitive.SharedState Auxiliary) :=
  (simulateQ (sharedImpl c writer kdf) ((simulateQ (ownerImpl senderId decode) client).run owner)).run primitive

/-- The complete shared-cache mixed game is exactly the composed source game, including failed sends and receives. -/
theorem shared_source {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) :
    sharedSchedule c writer kdf senderId decode client owner primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl (sharedImpl c writer kdf) senderId decode) client).run (owner, primitive) := by
  exact schedule_interpretation (sharedImpl c writer kdf) senderId decode client owner primitive

/-- Actual selective send/raw caps imply the complete shared-cache uniform ledger with the source-derived 51 coefficient. -/
theorem shared_schedule_uniform {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto) (writer : Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp SourceSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw) :
    (sharedSchedule c writer kdf senderId decode client owner primitive).IsTotalQueryBound
      (kdfCoins * (qSend + 51 * qRaw) + 64 * (qSend + qRaw)) := by
  have bounds := schedule_bounds senderId decode client qSend qRaw hSend hRaw owner
  exact shared_uniform c writer kdf kdfCoins bounded _ _ _ bounds.1 bounds.2.2.2.1 primitive

end BeaconcryptCore.Computational.RawCtxMixedShared

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_receive

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_sealing

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_writing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_writing

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.sharedAdapter_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.sharedAdapter_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_source

/-- info: 'BeaconcryptCore.Computational.RawCtxMixedShared.shared_schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMixedShared.shared_schedule_uniform
