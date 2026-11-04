-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRepresentation
/-! Concrete ordinary source children share the original private World and the public allocation state. Only successful ciphertext length is a new primitive functional parameter; the actual fixed-tag law and source ROM digest type derive their widths. Writer-attempt instrumentation is a separate trusted analysis receipt, rather than a Rust call or external allocator action. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Primitive)
open RegistrationNativePlatformOrdinarySourceRepresentation (M Functional typed)
variable {Platform E ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem bind_apply {m : Type → Type} [Monad m] {State A B : Type}
    (work : StateT State m A) (next : A → StateT State m B) (before : State) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {m : Type → Type} [Monad m] {State A : Type} (value : A) (before : State) :
    (pure value : StateT State m A) before = pure (value, before) := rfl

private theorem hash_width (setup : Setup base KemSK) (codec : Codec Reader Response)
    (bytes digest : Pqxdh.Bytes) (before after : Primitive)
    (supported : (some digest, after) ∈ support
      ((PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inr (.inl bytes))))).run before)) : digest.length = 64 := by
  unfold PqxdhRecordLiftWorld.primitives PqxdhDeploymentNative.primitives at supported
  dsimp only [StateT.run] at supported
  have hashed : RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
      (.inr (.inr (.inr (.inl bytes)))) ((), before.2) = (do
        let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run before.2
        pure (some result.1.toList, ((), result.2))) :=
    RawCtxMixedShared.shared_hash setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) bytes ((), before.2)
  rw [hashed] at supported
  simp only [simulateQ_bind, simulateQ_pure, bind_apply, pure_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨value, ⟨drawn, _draw, rfl⟩, same⟩ := supported
  have equality : digest = drawn.1.1.toList := Option.some.inj (congrArg Prod.fst same)
  rw [equality]
  exact drawn.1.1.toList_length

private theorem seal_pair (setup : Setup base KemSK) (codec : Codec Reader Response)
    (input : RawCtxSourceSeal.AeadInput) (before after : Primitive) (body tag : Pqxdh.Bytes)
    (supported : (some (body, tag), after) ∈ support ((PqxdhRecordLiftWorld.primitives setup codec (.inr (.inl input))).run before)) :
    (body, tag) = setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext := by
  have actual : ∃ final, (PqxdhRecordLiftWorld.primitives setup codec (.inr (.inl input))).run before =
      pure (some (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext), final) := ⟨_, rfl⟩
  obtain ⟨final, actual⟩ := actual
  rw [actual, support_pure, Set.mem_singleton_iff] at supported
  exact Option.some.inj (congrArg Prod.fst supported)

def AeadLength (crypto : Pqxdh.Crypto) : Prop := ∀ key nonce associated plaintext,
  (crypto.aeadSeal key nonce associated plaintext).1.length ≤ plaintext.length

noncomputable def implementation (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RawCtxSourceSeal.SealSpec (M Primitive Platform) :=
  RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve ∘ₛ RegistrationNativePlatformOrdinaryWorldSeal.inject

private theorem lift_apply {m : Type → Type} [Monad m] {State A : Type} (work : m A) (before : State) :
    (StateT.lift work : StateT State m A) before = (do let value ← work; pure (value, before)) := rfl

private theorem hash_support (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (bytes digest : Pqxdh.Bytes) (before after : Primitive) (previous next : Platform)
    (supported : ((some digest, after), next) ∈ support
      (((implementation setup codec reserve (.inr (.inl bytes))).run before).run previous)) :
    (some digest, after) ∈ support ((PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inr (.inl bytes))))).run before) := by
  simp only [implementation, QueryImpl.apply_compose, RegistrationNativePlatformOrdinaryWorldSeal.inject,
    simulateQ_spec_query, RegistrationNativePlatformOrdinaryWorld.primitives, StateT.run, lift_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨value, original, same⟩ := supported
  have equal := congrArg Prod.fst same
  change _ = value at equal
  rwa [← equal] at original

private theorem seal_support (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (input : RawCtxSourceSeal.AeadInput) (before after : Primitive) (previous next : Platform)
    (body tag : Pqxdh.Bytes)
    (supported : ((some (body, tag), after), next) ∈ support
      (((implementation setup codec reserve (.inl input)).run before).run previous)) :
    (some (body, tag), after) ∈ support ((PqxdhRecordLiftWorld.primitives setup codec (.inr (.inl input))).run before) := by
  simp only [implementation, QueryImpl.apply_compose, RegistrationNativePlatformOrdinaryWorldSeal.inject,
    simulateQ_spec_query, RegistrationNativePlatformOrdinaryWorld.primitives, StateT.run, lift_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨value, original, same⟩ := supported
  have equal := congrArg Prod.fst same
  change _ = value at equal
  rwa [← equal] at original

/-- The concrete World derives tag16 and hash64 from its actual native source; only the primitive ciphertext-length guarantee is supplied separately. -/
theorem functional (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (length : AeadLength setup.source.crypto) :
    Functional (implementation setup codec reserve) := by
  constructor
  · intro input before after previous next digest supported
    exact hash_width setup codec input digest before after (hash_support setup codec reserve input digest before after previous next supported)
  · intro input before after previous next body tag supported
    have same := seal_pair setup codec input before after body tag (seal_support setup codec reserve input before after previous next body tag supported)
    rw [show tag = (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext).2 from congrArg Prod.snd same]
    exact setup.source.crypto.aeadSeal_tag_length _ _ _ _
  · intro input before after previous next body tag supported
    have same := seal_pair setup codec input before after body tag (seal_support setup codec reserve input before after previous next body tag supported)
    rw [show body = (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext).1 from congrArg Prod.fst same]
    exact length _ _ _ _

noncomputable def kdf (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (request : ratchet.SymmetricRatchetKdfRequest) : M Primitive Platform ratchet.RatchetKdfResponse :=
  RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve (.inl request)

noncomputable def aead (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (input : RawCtxSourceSeal.AeadInput) :
    M Primitive Platform RegistrationNativePlatformOrdinarySourceNative.Sealed :=
  RegistrationNativePlatformOrdinarySourceRepresentation.sealed <$> implementation setup codec reserve (.inl input)

noncomputable def hash (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (bytes : Pqxdh.Bytes) :
    M Primitive Platform (Option (Std.Array U8 64#usize)) :=
  AdapterRecordNativeRepresentation.digest <$> implementation setup codec reserve (.inr (.inl bytes))

def receipt : M Primitive Platform Unit := fun before => pure ((), RegistrationNativePlatformOrdinaryWorld.chargeWriter before)

def reserveNative (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : Nat) : M Primitive Platform (core.result.Result Unit E) := StateT.lift (reserve size)

private theorem writer_lift (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (frame : RawCtxReceive.DecodedFrame) :
    RegistrationNativePlatformOrdinaryWriter.write (reserveNative reserve) frame =
      (StateT.lift (RegistrationNativePlatformOrdinaryWriter.write reserve frame) : M Primitive Platform _) := by
  unfold RegistrationNativePlatformOrdinaryWriter.write
  cases RegistrationNativePlatformOrdinaryWriter.capacity frame with
  | none =>
      funext before
      simp only [pure_apply, lift_apply, pure_bind]
  | some size =>
      funext before
      change ((do
        let reserved ← reserveNative reserve size
        match reserved with
        | .Err _ => pure none
        | .Ok _ => pure (some (CborTransport.render frame)) : M Primitive Platform _).run before) = _
      simp only [StateT.run_bind, reserveNative, StateT.run_lift, lift_apply, bind_assoc, pure_bind]
      apply bind_congr
      intro reserved
      cases reserved <;> simp only [StateT.run_pure, pure_bind]

private theorem writer_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (frame : RawCtxReceive.DecodedFrame) :
    RegistrationNativePlatformOrdinarySourceNative.afterAttempt receipt
      (RegistrationNativePlatformOrdinaryWriter.write (reserveNative reserve) frame) =
        implementation setup codec reserve (.inr (.inr frame)) := by
  rw [writer_lift]
  funext before previous
  simp only [RegistrationNativePlatformOrdinarySourceNative.afterAttempt, implementation, QueryImpl.apply_compose,
    RegistrationNativePlatformOrdinaryWorldSeal.inject, simulateQ_spec_query,
    RegistrationNativePlatformOrdinaryWorld.primitives, bind_apply, lift_apply, pure_apply,
    receipt, bind_assoc, pure_bind]

/-- The typed native four-child service has the exact dynamic source writer and one reached-writer analysis receipt, even when capacity refuses before reservation. -/
theorem typed_queries (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinarySourceNative.native (aead setup codec reserve) (hash setup codec reserve)
      (reserveNative reserve) receipt = typed (implementation setup codec reserve) := by
  funext query
  rcases query with input | (bytes | frame)
  · rfl
  · rfl
  · exact writer_native setup codec reserve frame

private theorem raw_queries (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinarySourceRepresentation.model (kdf setup codec reserve) (implementation setup codec reserve) =
      RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve ∘ₛ RawCtxMixedOwner.sendAdapter := by
  funext query
  rcases query with request | input
  · simp only [RegistrationNativePlatformOrdinarySourceRepresentation.model, kdf, QueryImpl.apply_compose,
      RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter, RawCtxMixedOwner.sendLift, simulateQ_spec_query]
  · simp only [RegistrationNativePlatformOrdinarySourceRepresentation.model, QueryImpl.apply_compose,
      RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter]
    have inclusion : RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift = RegistrationNativePlatformOrdinaryWorldSeal.inject := by
      funext request
      rcases request with request | (bytes | frame)
      all_goals simp only [QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, RawCtxSourceSeal.sealLift,
        RegistrationNativePlatformOrdinaryWorldSeal.inject, simulateQ_spec_query]
    rw [← QueryImpl.simulateQ_compose RawCtxMixedOwner.sendLift RawCtxSourceSeal.sealLift, inclusion]
    simp only [implementation, QueryImpl.simulateQ_compose]

private theorem typed_model (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinarySourceOwner.model (kdf setup codec reserve) (aead setup codec reserve) (hash setup codec reserve)
      (reserveNative reserve) receipt = RegistrationNativePlatformOrdinarySourceRepresentation.typedModel
        (kdf setup codec reserve) (implementation setup codec reserve) := by
  funext query
  cases query with
  | inl request => rfl
  | inr input =>
      unfold RegistrationNativePlatformOrdinarySourceOwner.model RegistrationNativePlatformOrdinarySourceRepresentation.typedModel
      dsimp only
      rw [typed_queries, QueryImpl.simulateQ_compose]

/-- Actual outer send, detached sealing, commitment writeback and source Frame3 writing share the concrete private World and one public platform state. Ciphertext representability follows only from the narrow primitive length law and the source Slice bound. -/
theorem source_owner [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (length : AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Std.Array U8 281#usize)
    (sameAD : owner.owner.associatedData = PqxdhRefinement.absBytes associated) :
    (RegistrationNativePlatformOrdinarySourceOwner.ownerResult owner ∘ RegistrationNativePlatformOrdinarySourceNative.abstractOutput) <$>
      simulateQ (RegistrationNativePlatformOrdinarySourceNative.callbacks view failure (kdf setup codec reserve)
        (aead setup codec reserve) (hash setup codec reserve) (reserveNative reserve) erased receipt)
        (AdapterRecordStatefulSend.program owner.owner.kernel
          ⟨plaintext, .None, associated, owner.owner.expectedSender, sender, .Frame⟩) =
      .ok <$> simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (simulateQ RawCtxMixedOwner.sendAdapter
          ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner)) := by
  rw [RegistrationNativePlatformOrdinarySourceOwner.source_owner view converted failure
    (kdf setup codec reserve) (aead setup codec reserve) (hash setup codec reserve) (reserveNative reserve) erased
    owner plaintext sender associated sameAD receipt, typed_model,
    RegistrationNativePlatformOrdinarySourceRepresentation.owner_native (kdf setup codec reserve)
      (implementation setup codec reserve) (functional setup codec reserve length), raw_queries,
    QueryImpl.simulateQ_compose]

/-- The concrete source/native owner equality retains the complete private poststate and common platform poststate jointly, including all failed send outcomes. -/
theorem joint [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (length : AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (owner : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Std.Array U8 281#usize)
    (sameAD : owner.owner.associatedData = PqxdhRefinement.absBytes associated) (before : Primitive) (previous : Platform) :
    (((RegistrationNativePlatformOrdinarySourceOwner.ownerResult owner ∘ RegistrationNativePlatformOrdinarySourceNative.abstractOutput) <$>
      simulateQ (RegistrationNativePlatformOrdinarySourceNative.callbacks view failure (kdf setup codec reserve)
        (aead setup codec reserve) (hash setup codec reserve) (reserveNative reserve) erased receipt)
        (AdapterRecordStatefulSend.program owner.owner.kernel
          ⟨plaintext, .None, associated, owner.owner.expectedSender, sender, .Frame⟩)).run before).run previous =
      ((.ok <$> simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve)
        (simulateQ RawCtxMixedOwner.sendAdapter
          ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run owner))).run before).run previous := by
  rw [source_owner setup codec reserve length view converted failure erased owner plaintext sender associated sameAD]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.functional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.functional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.typed_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.typed_queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.source_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceWorld.joint
