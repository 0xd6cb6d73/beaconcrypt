import BeaconcryptCore.Computational.RawCtxInitialSentinel
import BeaconcryptCore.Computational.RawCtxRetainedParentBackend

/-!
The root-domain analysis marker is unreachable by every actual private ratchet request. Removing it therefore preserves the entire native pending family interpreter, not just its derivation replies: original optional opening, sealing, commitment, publication, real public calls and LIVE reads all retain their complete effects. The marker adds no source cache binding or initializer nonce and supplies no cryptographic assumption.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialSentinelBackend
open RawCtxInitialSentinel RawCtxSelectedParentTable
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
variable {A : Type} {S B : Nat}

noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  RawCtxRetainedParentBackend.backend (A := A) source writer prior ∘ₛ RawCtxServerServices.nativeLift

private theorem native_other (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (left right : Prior) (query : RawCtxMixedOwner.NativeSpec.Domain) (notKdf : query.isLeft = false) :
    native (A := A) source writer left query = native source writer right query := by
  cases query with
  | inl request => cases notKdf
  | inr request =>
    simp [native, RawCtxRetainedParentBackend.backend, QueryImpl.compose, RawCtxServerServices.nativeLift,
      RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl, OracleSpec.query]

private theorem native_kdf (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (chain : RatchetChain) :
    native (A := A) source writer prior (.inl (RawCtxChainSend.nativeRequest chain)) =
      pure (RawCtxKdfRequestTable.fullResponse (prior (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain)))) := by
  simp [native, RawCtxRetainedParentBackend.backend, QueryImpl.compose, RawCtxServerServices.nativeLift,
    RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl, OracleSpec.query]

private theorem pending_marker (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput) :
    RawCtxPendingNativeCalls.pending (native (A := A) source writer (lookup prior (entry other extra) target))
      (RawCtxSelectedParentOwner.publicImpl source writer) =
      RawCtxPendingNativeCalls.pending (native source writer prior) (RawCtxSelectedParentOwner.publicImpl source writer) := by
  funext query
  rcases query with (request | opening) | ((request | sealing) | publicQuery)
  · rw [RawCtxPendingNativeCallbacks.receive_kdf, RawCtxPendingNativeCallbacks.receive_kdf,
      native_kdf, native_kdf, lookup_private]
  · exact RawCtxPendingNativeCallbacks.non_kdf _ _ _
      (native_other source writer (lookup prior (entry other extra) target) prior) _ rfl
  · rw [RawCtxPendingNativeCallbacks.send_kdf, RawCtxPendingNativeCallbacks.send_kdf,
      native_kdf, native_kdf, lookup_private]
  · exact RawCtxPendingNativeCallbacks.non_kdf _ _ _
      (native_other source writer (lookup prior (entry other extra) target) prior) _ rfl
  · exact RawCtxPendingNativeCallbacks.non_kdf _ _ _
      (native_other source writer (lookup prior (entry other extra) target) prior) _ rfl

/-- The original whole LIVE backend ignores the unreachable marker, preserving every original primitive effect, real public callback and optional read with the same full shared state. -/
theorem native_marker
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput) :
    RawCtxSelectedParentFamilyMap.nativeLive (A := A) (S := S) (B := B) source writer prior (entry other extra) target =
      RawCtxPendingRetainedExecution.retained source writer prior := by
  rw [← RawCtxRetainedParentBackend.retained_live]
  change RawCtxPendingFamilyLiveQueries.handler
    (RawCtxPendingNativeCalls.pending (native source writer (lookup prior (entry other extra) target))
      (RawCtxRetainedParentBackend.backend source writer (lookup prior (entry other extra) target) ∘ₛ RawCtxServerServices.publicLift))
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) =
      RawCtxPendingFamilyLiveQueries.handler
        (RawCtxPendingNativeCalls.pending (native source writer prior)
          (RawCtxRetainedParentBackend.backend source writer prior ∘ₛ RawCtxServerServices.publicLift))
        (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
  rw [RawCtxRetainedParentBackend.public_calls, RawCtxRetainedParentBackend.public_calls, pending_marker]

end BeaconcryptCore.Computational.RawCtxInitialSentinelBackend

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelBackend.native_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelBackend.native_marker
