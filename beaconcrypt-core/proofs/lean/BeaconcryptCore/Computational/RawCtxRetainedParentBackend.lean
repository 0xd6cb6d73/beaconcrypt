import BeaconcryptCore.Computational.RawCtxPendingRetainedExecution
import BeaconcryptCore.Computational.RawCtxSelectedParentFamilyMap
import BeaconcryptCore.Computational.RawCtxSelectedParentNativeBackend

/-!
The complete retained pending family backend is the exact retained-parent native interpreter. Only private KDF calls use the retained lookup; every opening, sealing, commitment, publication, caller coin, public HKDF evaluation and optional live read keeps its actual source implementation. This operational identity connects the saturated source continuation to the already checked native/label family relation without a supplied callback-compatibility premise.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRetainedParentBackend
open RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdfGame PqxdhSecretInputKdf
variable {A : Type} {S B : Nat}

noncomputable def backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  RawCtxRetainedTable.viewImpl prior (RawCtxProtocolBackend.backend (Auxiliary := A) source writer) ∘ₛ RawCtxSelectiveKdfFamily.compiler

/-- The retained private lookup and every other actual native primitive callback are exactly the existing retained-parent mixed backend. -/
theorem native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    backend (A := A) source writer (lookup prior entry target) ∘ₛ RawCtxServerServices.nativeLift =
      RawCtxSelectedParentNativeBackend.backend source writer prior entry target := by
  funext query
  cases query with
  | inl request =>
    simp [backend, QueryImpl.compose, RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler,
      RawCtxRetainedTable.viewImpl, RawCtxSelectedParentNativeBackend.backend,
      RawCtxSelectedParentSource.response, OracleSpec.query]
  | inr request =>
    simp [backend, QueryImpl.compose, RawCtxServerServices.nativeLift, RawCtxSelectiveKdfFamily.compiler,
      RawCtxRetainedTable.viewImpl, RawCtxSelectedParentNativeBackend.backend,
      RawCtxProtocolBackend.backend, OracleSpec.query]
    rfl

/-- Caller coins, public commitments and public HKDF evaluations remain the exact real source services for any retained private lookup. -/
theorem public_calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    backend (A := A) source writer prior ∘ₛ RawCtxServerServices.publicLift =
      RawCtxSelectedParentOwner.publicImpl source writer := by
  funext query
  rcases query with coins | (bytes | view)
  all_goals simp [backend, QueryImpl.compose, RawCtxServerServices.publicLift,
    RawCtxSelectiveKdfFamily.compiler, RawCtxRetainedTable.viewImpl,
    RawCtxSelectedParentOwner.publicImpl, OracleSpec.query]

/-- The original pending receive, send and public callbacks are exactly the existing retained-parent pending interpreter, without any supplied realization premise. -/
theorem pending (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    RawCtxPendingNativeCalls.pending (RawCtxSelectedParentNativeBackend.backend (Auxiliary := A) source writer prior entry target)
      (RawCtxSelectedParentOwner.publicImpl source writer) =
      RawCtxSelectedParentNativeCompiler.pending source writer prior entry target := by
  unfold RawCtxPendingNativeCalls.pending RawCtxSelectedParentNativeCompiler.pending
  apply congrArg (fun original => original ∘ₛ RawCtxPendingOwnerQueries.erase)
  funext query
  rcases query with (chain | opening) | ((chain | sealing) | publicQuery)
  · simp only [RawCtxPendingNativeCalls.original, RawCtxPendingNativeCalls.receive,
      RawCtxSelectedParentNativeBackend.receive_adapter]
    rfl
  · simp only [RawCtxPendingNativeCalls.original, RawCtxPendingNativeCalls.receive,
      RawCtxSelectedParentNativeBackend.receive_adapter]
    rcases opening with ⟨kernel, context, prepared⟩
    cases prepared <;> rfl
  · simp only [RawCtxPendingNativeCalls.original, RawCtxPendingNativeCalls.send,
      RawCtxSelectedParentNativeBackend.send_adapter]
    rfl
  · simp only [RawCtxPendingNativeCalls.original, RawCtxPendingNativeCalls.send,
      RawCtxSelectedParentNativeBackend.send_adapter]
    rfl
  · rfl

/-- The full retained source family backend is the existing native retained-parent LIVE interpreter, preserving every optional read and all primitive state effects. -/
theorem retained_live (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) :
    RawCtxPendingRetainedExecution.retained (A := A) (S := S) (B := B) source writer (lookup prior entry target) =
      RawCtxSelectedParentFamilyMap.nativeLive source writer prior entry target := by
  change RawCtxPendingFamilyLiveQueries.handler
    (RawCtxPendingNativeCalls.pending (backend source writer (lookup prior entry target) ∘ₛ RawCtxServerServices.nativeLift)
      (backend source writer (lookup prior entry target) ∘ₛ RawCtxServerServices.publicLift))
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) = _
  rw [native, public_calls, pending]
  rfl

end BeaconcryptCore.Computational.RawCtxRetainedParentBackend

/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedParentBackend.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedParentBackend.native
/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedParentBackend.public_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedParentBackend.public_calls
/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedParentBackend.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedParentBackend.pending
/-- info: 'BeaconcryptCore.Computational.RawCtxRetainedParentBackend.retained_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRetainedParentBackend.retained_live
