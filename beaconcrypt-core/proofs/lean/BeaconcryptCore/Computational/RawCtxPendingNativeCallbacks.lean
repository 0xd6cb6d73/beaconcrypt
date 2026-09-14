import BeaconcryptCore.Computational.RawCtxPendingFamilyNative

/-!
These callback equations expose the actual private KDF query beneath enriched native pending requests. Non-KDF callbacks retain their original full primitive work. They are used to compare adjacent mutable selective interpreters before a source-selected miss, not to assume fixed outputs or discard local work.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks
open RawCtxPendingNativeCalls RawCtxPendingOwnerQueries

/-- The selected receive callback forwards its original actual KDF request and decodes the complete actual reply in the same backend. -/
theorem receive_kdf {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (request : RawCtxChainReceive.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    pending native publicCalls (.inl (.inl request)) =
      RawCtxInterpretedReceive.decodeResponse <$> native (.inl (RawCtxChainSend.nativeRequest request.request)) := by
  simp [pending, QueryImpl.compose, erase, original, receive, RawCtxInterpretedReceive.nativeAdapter,
    RawCtxWholeOwner.adapter, RawCtxMixedOwner.receiveAdapter, RawCtxMixedOwner.receiveLift,
    RawCtxSourceOpen.nativeAdapter, OracleSpec.query]

/-- The selected send callback forwards the same actual request and retains the actual decoded full response. -/
theorem send_kdf {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (request : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    pending native publicCalls (.inr (.inl (.inl request))) =
      RawCtxInterpretedReceive.decodeResponse <$> native (.inl (RawCtxChainSend.nativeRequest request.request)) := by
  simp [pending, QueryImpl.compose, erase, original, send, RawCtxInterpretedSend.nativeAdapter,
    RawCtxSourceSend.adapter, RawCtxMixedOwner.sendAdapter, RawCtxMixedOwner.sendLift,
    RawCtxSourceSeal.nativeAdapter, OracleSpec.query]

private theorem opening_congr {m : Type → Type*} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (same : ∀ query, query.isLeft = false → left query = right query)
    (opening : (RawCtxInterpretedReceive.ReceiveSpec RatchetMaterial RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain) :
    opening.isLeft = false → receive left opening = receive right opening := by
  intro notKdf
  cases opening with
  | inl _ => cases notKdf
  | inr opening =>
    have inner : (left ∘ₛ RawCtxMixedOwner.receiveLift) ∘ₛ RawCtxSourceOpen.openLift =
        (right ∘ₛ RawCtxMixedOwner.receiveLift) ∘ₛ RawCtxSourceOpen.openLift := by
      funext query
      cases query <;> simp [QueryImpl.compose, RawCtxSourceOpen.openLift,
        RawCtxMixedOwner.receiveLift, OracleSpec.query] <;> exact same _ rfl
    have lifted : ∀ input, (left ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input) =
        (right ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input) := by
      intro input
      simp only [RawCtxMixedOwner.receiveAdapter, QueryImpl.apply_compose,
        RawCtxSourceOpen.nativeAdapter]
      rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, inner]
      simp only [QueryImpl.simulateQ_compose]
    simp only [receive, QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter]
    simp [OracleSpec.query, QueryImpl.apply_compose, RawCtxWholeOwner.adapter]
    split
    · simp only [simulateQ_pure]
    · rename_i input found
      simpa [QueryImpl.compose, OracleSpec.query] using
        congrArg (fun computation => RawCtxOwnerResult.mapReply (RawCtxWholeOwner.decrypted input) <$> computation) (lifted input)

private theorem sealing_congr {m : Type → Type*} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (same : ∀ query, query.isLeft = false → left query = right query)
    (sealing : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext) :
    send left (.inr sealing) = send right (.inr sealing) := by
  have inner : (left ∘ₛ RawCtxMixedOwner.sendLift) ∘ₛ RawCtxSourceSeal.sealLift =
      (right ∘ₛ RawCtxMixedOwner.sendLift) ∘ₛ RawCtxSourceSeal.sealLift := by
    funext query
    rcases query with query | (query | query) <;>
      simp [QueryImpl.compose, RawCtxSourceSeal.sealLift, RawCtxMixedOwner.sendLift, OracleSpec.query] <;>
      exact same _ rfl
  have lifted : ∀ input, (left ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input) =
      (right ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input) := by
    intro input
    simp only [RawCtxMixedOwner.sendAdapter, QueryImpl.apply_compose, RawCtxSourceSeal.nativeAdapter]
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, inner]
    simp only [QueryImpl.simulateQ_compose]
  simp only [send, QueryImpl.apply_compose, RawCtxInterpretedSend.nativeAdapter]
  simpa [OracleSpec.query, QueryImpl.apply_compose, RawCtxSourceSend.adapter] using
    congrArg (fun computation => (fun ciphertext => ciphertext.map
      (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal sealing)))) <$> computation)
      (lifted (RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal sealing)))

/-- Every non-KDF pending callback retains all original opening, sealing or public work when only native KDF replies may differ. -/
theorem non_kdf {m : Type → Type*} [Monad m] [LawfulMonad m]
    (left right : QueryImpl RawCtxMixedOwner.NativeSpec m)
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (same : ∀ query, query.isLeft = false → left query = right query)
    (query : (Spec RatchetChain).Domain)
    (notKdf : RawCtxPendingMixedPrefix.ownerSelected query = false) :
    pending left publicCalls query = pending right publicCalls query := by
  rcases query with (request | opening) | ((request | sealing) | request)
  · cases notKdf
  · simpa [pending, QueryImpl.compose, erase, original, OracleSpec.query] using
      opening_congr left right same (.inr (RawCtxChainInterpretation.mapOpeningChains id id opening)) rfl
  · cases notKdf
  · simpa [pending, QueryImpl.compose, erase, original, OracleSpec.query] using
      sealing_congr left right same (RawCtxChainSend.nativeSeal id id sealing)
  · simp [pending, QueryImpl.compose, erase, original, OracleSpec.query]

end BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks.receive_kdf
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks.send_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks.send_kdf
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks.non_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCallbacks.non_kdf
