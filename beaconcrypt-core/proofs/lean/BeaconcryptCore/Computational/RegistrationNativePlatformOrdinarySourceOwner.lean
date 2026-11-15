-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceNative
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldLogged
/-! The complete extracted send and its concrete source children implement the ordinary whole-owner byte interface. Source context conversion follows the actual generic Core begin/resume bodies. Empty input, exhaustion, all optional failures and the consumed send kernel are retained in the common monad. The optional unit receipt is trusted analysis instrumentation and is pure by default. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM ratchet ratchet.concrete
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner
open BeaconcryptCore.Refinement
variable {Left Right : Type}

def mapKdf (f : Left → Right) (pending : SendKdf Left) : SendKdf Right :=
  ⟨pending.entry, f pending.context, pending.committed_control, pending.logical, pending.sequence, pending.request⟩
def mapSeal (f : Left → Right) (pending : SendSeal Left) : SendSeal Right :=
  ⟨pending.advanced, f pending.context, pending.logical, pending.sequence, pending.material⟩
def mapStart (f : Left → Right) : SendStart Left → SendStart Right
  | .SendExhausted kernel context => .SendExhausted kernel (f context)
  | .SendKdfRequested pending => .SendKdfRequested (mapKdf f pending)

private theorem begin_map (f : Left → Right) (kernel : ConcreteRatchetKernel) (context : Left) :
    mapStart f <$> begin_send kernel context = begin_send kernel (f context) := by
  obtain ⟨advanced, called⟩ := ratchet.control.advance_send_total kernel.refined.control
  simp only [begin_send, called, bind_tc_ok]
  cases advanced.sequence with
  | none => rfl
  | some sequence =>
      simp only [ratchet.control.SendKey.impl.sequence,
        ratchet.control.RatchetState.impl.send_sequence, RatchetChain.as_bytes,
        SymmetricRatchetKdfRequest.new, bind_tc_ok]
      repeat' first | rfl | split | simp only [bind_tc_ok, core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64]

private theorem resume_map (f : Left → Right) (pending : SendKdf Left) (response : RatchetKdfResponse) :
    mapSeal f <$> pending.resume response = (mapKdf f pending).resume response := by
  obtain ⟨stepped, step⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
  simp only [SendKdf.resume, step, bind_tc_ok]
  rfl

private theorem begin_normalized_map (f : Left → Right) (kernel : ConcreteRatchetKernel) (context : Left) :
    mapStart f (RawCtxSourceSend.beginSend kernel context) = RawCtxSourceSend.beginSend kernel (f context) := by
  have equality := begin_map f kernel context
  rw [RawCtxSourceSend.beginSend_exact, RawCtxSourceSend.beginSend_exact] at equality
  exact RustM.ok.inj equality

private theorem resume_normalized_map (f : Left → Right) (pending : SendKdf Left) (response : RatchetKdfResponse) :
    mapSeal f (RawCtxSourceSend.resumeSend pending response) = RawCtxSourceSend.resumeSend (mapKdf f pending) response := by
  have equality := resume_map f pending response
  rw [RawCtxSourceSend.resumeSend_exact, RawCtxSourceSend.resumeSend_exact] at equality
  exact RustM.ok.inj equality

def context (value : record_effects.SealFrameContext) : RawCtxSourceSend.SealContext :=
  ⟨TranscriptAuthParts.absSlice value.plaintext, value.target_kid, value.sender_kid, PqxdhRefinement.absBytes value.associated_data⟩

def result (value : ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) : RustM RecordEffectsSendBridge.Result :=
  .ok (value.1, value.2.map fun record => ⟨record.ciphertext, record.keyId, record.sequence⟩)

variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}

def model (kdf : SymmetricRatchetKdfRequest → m RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m RegistrationNativePlatformOrdinarySourceNative.Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (receipt : m Unit := pure ()) : QueryImpl RawCtxSourceSend.PrimitiveSpec m
  | .inl request => kdf request
  | .inr input => simulateQ (RegistrationNativePlatformOrdinarySourceNative.native aead hash reserve receipt ∘ₛ RecordEffectsSendBridge.modelAdapter)
      (RawCtxSourceSeal.sealInput input)

private theorem empty_exact (value : Slice U8) : core.slice.Slice.is_empty value = .ok value.val.isEmpty := by
  cases value with
  | mk bytes property =>
      cases bytes <;> simp [core.slice.Slice.is_empty, core.slice.Slice.len, rust_primitives.slice.slice_length]
      apply UScalar.eq_of_val_eq
      rfl

/-- Source admission and context representation derive the complete ordinary native send, including empty/exhausted paths and the advanced kernel after rejection. -/
theorem byte_controller
    (kdf : SymmetricRatchetKdfRequest → m RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m RegistrationNativePlatformOrdinarySourceNative.Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E))
    (kernel : ConcreteRatchetKernel) (value : record_effects.SealFrameContext) (ordinary : value.prefix = .None) (receipt : m Unit := pure ()) :
    RegistrationNativePlatformOrdinarySourceNative.byteController kdf aead hash reserve kernel value receipt =
      if value.plaintext.val.isEmpty then pure (.ok (kernel, .None)) else
        result <$> simulateQ (model kdf aead hash reserve receipt)
          (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel (context value))) := by
  unfold RegistrationNativePlatformOrdinarySourceNative.byteController record_effects.begin_record_send
  rw [empty_exact, ordinary]
  cases empty : value.plaintext.val.isEmpty with
  | true =>
      simp [core.option.Option.is_none, core.option.Option.is_some, bind_tc_ok]
  | false =>
      simp only [bind_tc_ok]
      rw [RawCtxSourceSend.beginSend_exact]
      unfold RawCtxSourceSend.send
      rw [← begin_normalized_map context kernel value]
      cases started : RawCtxSourceSend.beginSend kernel value with
      | SendExhausted entry original => simp only [mapStart, RawCtxSourceSend.program, simulateQ_pure, map_pure]; rfl
      | SendKdfRequested pending =>
          simp only [mapStart, RawCtxSourceSend.program, simulateQ_bind, simulateQ_spec_query, RawCtxSourceSend.adapter,
            model, map_bind]
          apply bind_congr
          intro response
          rw [← resume_normalized_map context pending response]
          simp only [mapSeal, RawCtxSourceSend.arguments, simulateQ_pure, map_pure, bind_assoc, pure_bind]
          apply bind_congr
          intro written
          rw [RecordEffectsSendBridge.finishResult_exact]
          cases written <;> rfl

/-- The actual source driver and all four source/native children implement the complete ordinary native send interface, with source empty-input admission derived. -/
theorem source_send [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (kdf : SymmetricRatchetKdfRequest → m RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m RegistrationNativePlatformOrdinarySourceNative.Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (kernel : ConcreteRatchetKernel) (value : record_effects.SealFrameContext)
    (ordinary : value.prefix = .None) (framed : value.encoding = .Frame) (receipt : m Unit := pure ()) :
    RegistrationNativePlatformOrdinarySourceNative.abstractOutput <$>
      simulateQ (RegistrationNativePlatformOrdinarySourceNative.callbacks view failure kdf aead hash reserve erased receipt)
        (AdapterRecordStatefulSend.program kernel value) =
      if value.plaintext.val.isEmpty then pure (.ok (kernel, .None)) else
        result <$> simulateQ (model kdf aead hash reserve receipt)
          (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel (context value))) := by
  rw [RegistrationNativePlatformOrdinarySourceNative.source_program view converted failure kdf aead hash reserve erased kernel value ordinary framed receipt]
  exact byte_controller kdf aead hash reserve kernel value ordinary receipt

def ownerResult {Metadata : Type} (before : RawCtxWholeOwner.OwnerState Metadata)
    (value : RustM RecordEffectsSendBridge.Result) : RustM (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) := do
  let value ← value
  .ok (_root_.Option.map (fun record => ⟨record.ciphertext, record.key_id, record.seq⟩) value.2,
    { before with owner := { before.owner with kernel := value.1 } })

/-- The extracted send and its actual children retain complete owner metadata and the advanced whole kernel on every normal primitive or allocation outcome. -/
theorem source_owner [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (kdf : SymmetricRatchetKdfRequest → m RatchetKdfResponse)
    (aead : RawCtxSourceSeal.AeadInput → m RegistrationNativePlatformOrdinarySourceNative.Sealed)
    (hash : Pqxdh.Bytes → m (Option (Std.Array U8 64#usize)))
    (reserve : Nat → m (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    {Metadata : Type} (before : RawCtxWholeOwner.OwnerState Metadata)
    (plaintext : Slice U8) (sender : U64) (associated : Std.Array U8 151#usize)
    (sameAD : before.owner.associatedData = PqxdhRefinement.absBytes associated) (receipt : m Unit := pure ()) :
    (ownerResult before ∘ RegistrationNativePlatformOrdinarySourceNative.abstractOutput) <$>
      simulateQ (RegistrationNativePlatformOrdinarySourceNative.callbacks view failure kdf aead hash reserve erased receipt)
        (AdapterRecordStatefulSend.program before.owner.kernel
          ⟨plaintext, .None, associated, before.owner.expectedSender, sender, .Frame⟩) =
      .ok <$> simulateQ (model kdf aead hash reserve receipt)
        ((RawCtxSourceSend.sendOwner sender (TranscriptAuthParts.absSlice plaintext)).run before) := by
  trans ownerResult before <$> (RegistrationNativePlatformOrdinarySourceNative.abstractOutput <$>
    simulateQ (RegistrationNativePlatformOrdinarySourceNative.callbacks view failure kdf aead hash reserve erased receipt)
      (AdapterRecordStatefulSend.program before.owner.kernel
        ⟨plaintext, .None, associated, before.owner.expectedSender, sender, .Frame⟩))
  · rw [Functor.map_map]
    rfl
  rw [source_send view converted failure kdf aead hash reserve erased _ _ rfl rfl receipt]
  unfold RawCtxSourceSend.sendOwner StateT.run
  simp only [TranscriptAuthParts.absSlice, List.isEmpty_map, context, sameAD]
  cases empty : plaintext.val.isEmpty with
  | true => simp only [ite_true, map_pure, simulateQ_pure]; rfl
  | false =>
      simp only [Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_pure, map_bind, map_pure, Functor.map_map]
      rw [← bind_pure_comp]
      apply bind_congr
      intro sent
      rcases sent with ⟨kernel, encrypted⟩
      cases encrypted <;> simp only [ownerResult, result, bind_tc_ok, Option.map_none, Option.map_some, sameAD]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner.byte_controller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner.byte_controller

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner.source_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner.source_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner.source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceOwner.source_owner
