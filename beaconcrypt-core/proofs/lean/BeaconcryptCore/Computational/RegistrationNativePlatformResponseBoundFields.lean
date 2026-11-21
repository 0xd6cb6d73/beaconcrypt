-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseRecordSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerSafe
import BeaconcryptCore.Computational.RegistrationNativeResponsePaired

/-! The literal dynamic record/publication compiler retains its admitted public candidate through actual seal, mutable hash, signing and concrete stateful source encoding. Successful byte provenance is derived internally; allocation failures and complete shared platform poststates remain in the source computation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseBoundFields
open RegistrationNativePlatformBoundCompiler (PublicState)
variable {n : Nat} {Platform E : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "wire" => RegistrationNativePlatformConcreteSource.wire

omit primitive in
private theorem publication (pending : registration.ServerResponseHash) :
    simulateQ (RegistrationNativePlatformPublicationCompiler.target (n := n) source (fun _ => none) sign writer)
      (RegistrationNativePlatformPublicationCompiler.program pending) =
      RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformSigningCompiler.signing (n := n) source (fun _ => none) sign)
        (RegistrationNativePlatformPublicationCompiler.encoding (n := n) writer) pending := by
  unfold RegistrationNativePlatformPublicationCompiler.program
  rw [RegistrationNativePlatformServerPublication.program_interpret]
  simp only [RegistrationNativePlatformPublicationCompiler.signLift,RegistrationNativePlatformPublicationCompiler.encodeLift,
    simulateQ_spec_query,RegistrationNativePlatformPublicationCompiler.target]

/-- The literal stateful record/publication compiler returns source bytes encoding exactly its admitted public candidate fields. -/
theorem compile (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) (before after : PublicState Platform)
    (supported : (.ok (.Ok published),after) ∈ support ((RegistrationNativePlatformBoundCompiler.compile (n := n)
      source view failure allocation erased helper sign writer initial output).run before)) :
    RegistrationNativeResponsePaired.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse initial (TranscriptAuthParts.absSlice published.encoded) := by
  simp only [RegistrationNativePlatformBoundCompiler.compile,RegistrationNativePlatformBoundCompiler.program,
    simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨record,recorded,continued⟩ := supported
  cases actual : record.1 with
  | fail error | div =>
    simp only [actual,RegistrationNativePlatformServerPublication.continueResult,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
    cases continued
  | ok outcome => cases outcome with
    | Err previous =>
      simp only [actual,RegistrationNativePlatformServerPublication.continueResult,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at continued
      cases continued
    | Ok response =>
      simp only [RegistrationNativePlatformBoundCompiler.target,RegistrationNativePlatformBoundCompiler.liftPlatform,StateT.run,support_map] at recorded
      obtain ⟨localResult,possible,equal⟩ := recorded
      cases equal
      change localResult.1 = .ok (.Ok response) at actual
      have old := RegistrationNativePlatformResponseRecordSupport.factored _ _ _ initial output response
        ⟨before.2,localResult.2,by simpa only [RegistrationNativePlatformRecordCompiler.record,StateT.run,←actual,Prod.mk.eta] using possible⟩
      have cipher := RegistrationNativeResponseCipherCandidate.factored_ciphertext initial output response old
      have identity := RegistrationNativeResponseCandidate.factored_identity initial output response old
      have publishedSupport : (.ok (.Ok published),after) ∈ support
          ((RegistrationNativePlatformServerPublication.program
            (RegistrationNativePlatformSigningCompiler.signing (n := n) source (fun _ => none) sign)
            (RegistrationNativePlatformPublicationCompiler.encoding (n := n) writer) response).run (before.1,localResult.2)) := by
        simp only [actual,RegistrationNativePlatformServerPublication.continueResult,simulateQ_spec_query,
          RegistrationNativePlatformBoundCompiler.target] at continued
        rw [publication] at continued
        exact continued
      have fields := RegistrationNativePlatformResponsePublicationConcrete.program reserve source (fun _ => none) sign response published _ _ publishedSupport
      rw [cipher,identity] at fields
      exact fields

end BeaconcryptCore.Computational.RegistrationNativePlatformResponseBoundFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseBoundFields.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseBoundFields.compile
