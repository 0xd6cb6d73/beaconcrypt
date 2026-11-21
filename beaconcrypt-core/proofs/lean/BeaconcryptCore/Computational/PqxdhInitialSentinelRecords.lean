import BeaconcryptCore.Computational.PqxdhInitialSentinelSource
import BeaconcryptCore.Computational.PqxdhInitialGenericRecords

/-!
The analysis-only initializer marker cannot affect an original typed record request. Complete pending source calls establish the equality; arbitrary raw KDF requests are not assumed to carry a ratchet label. The original real public HKDF, shared commitment cache, optional native reads and full protocol poststate remain unchanged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSentinelRecords
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentTable PqxdhInitialGenericProtocolBuilder PqxdhInitialSentinelSource
variable {A M P I D K : Type} {S B : Nat}

/-- The real public interface is independent of any private record-KDF substitution, including its exact public hashes and uniform calls. -/
theorem public_backend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (left right : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    RawCtxServerServices.backendImpl source writer left ∘ₛ RawCtxServerServices.publicLift =
      RawCtxServerServices.backendImpl source writer right ∘ₛ RawCtxServerServices.publicLift := by
  funext query state
  rcases query with coin | bytes | query
  all_goals simp [RawCtxServerServices.publicLift, RawCtxServerServices.backendImpl,
    QueryImpl.compose, OracleSpec.query, RawCtxMixedShared.sharedImpl,
    RawCtxMixedShared.sharedAdapter, RawCtxSharedPrimitive.nativeImpl, StateT.run]

/-- The full actual typed receive/send callbacks remove the initializer marker, including every pending continuation and optional result. -/
theorem native_calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput) :
    RawCtxGenericNativeCalls.calls
      (RawCtxMixedShared.sharedImpl source.crypto writer (retainedKdf (A := A) prior (RawCtxInitialSentinel.entry other extra) target)) =
      RawCtxGenericNativeCalls.calls (RawCtxMixedShared.sharedImpl source.crypto writer (priorKdf prior)) := by
  rw [← RawCtxPendingNativeCalls.calls_interpretation _ (RawCtxSelectedParentOwner.publicImpl source writer),
    ← RawCtxPendingNativeCalls.calls_interpretation _ (RawCtxSelectedParentOwner.publicImpl source writer), pending_marker]

/-- Every original record, public evaluation and live reveal retains the same complete native protocol state after removing the marker through the typed source calls. -/
theorem records (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (other target : RootOutput) (extra : NonceOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    PqxdhInitialPrivateKdf.records (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)
      source writer (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target) sender route decode =
      PqxdhInitialPrivateKdf.records source writer (priorKdf prior) sender route decode := by
  funext query state
  rw [← PqxdhInitialGenericRecords.native_source, ← PqxdhInitialGenericRecords.native_source]
  have left := PqxdhInitialGenericRecords.actual
    (RawCtxServerServices.backendImpl source writer (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target))
    sender route decode (((RawCtxProtocolReveals.SourceSpec S B).query query) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) state
  have right := PqxdhInitialGenericRecords.actual
    (RawCtxServerServices.backendImpl source writer (priorKdf prior))
    sender route decode (((RawCtxProtocolReveals.SourceSpec S B).query query) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) state
  simp only [simulateQ_spec_query, StateT.run] at left right
  rw [left, right, RawCtxServerServices.native_interpretation, RawCtxServerServices.native_interpretation,
    native_calls, public_backend source writer (retainedKdf prior (RawCtxInitialSentinel.entry other extra) target) (priorKdf prior)]

end BeaconcryptCore.Computational.PqxdhInitialSentinelRecords

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelRecords.public_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelRecords.public_backend

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelRecords.native_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelRecords.native_calls

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSentinelRecords.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSentinelRecords.records
