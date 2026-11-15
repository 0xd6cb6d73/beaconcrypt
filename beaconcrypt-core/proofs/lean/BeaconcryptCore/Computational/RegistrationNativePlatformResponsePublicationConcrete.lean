-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhEnvironmentForward
import BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource

/-! Concrete response source bytes and the admitted candidate fields are derived from the literal extracted serializer, complete length gate and stateful public reservation. Hash/sign/source encoding retain every failure and shared platform poststate; this is successful data provenance, not an infallible writer claim. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete
variable {n : Nat} {Platform E : Type}
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before=Prod.map f id <$> work before := StateT.run_map f work before

def vectorEncode (view : registration.SignedResponseView) : core.option.Option (alloc.vec.Vec U8) :=
  if admitted : RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view) ≤ CborSizing.maxMessageSize
  then .Some (RegistrationNativeSourceWriterReadback.responseVector view admitted) else .None

/-- Every concrete response-source success returns the serializer's exact vector and has passed its complete size gate. Every refused reservation remains a separate actual failure path. -/
theorem source_writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.SignedResponseView) (before : Platform)
    (result : RustM (core.option.Option (alloc.vec.Vec U8)) × Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSourceCompletion.encodeWith
      (RegistrationNativePlatformConcreteSource.writer reserve) view).run before))
    (bytes : alloc.vec.Vec U8) (returned : result.1=.ok (.Some bytes)) : vectorEncode view=.Some bytes := by
  by_cases admitted : RegistrationSerializerResponseBytes.totalLength (RegistrationNativeSourceEncoders.responseSyntax view) ≤ CborSizing.maxMessageSize
  · obtain ⟨capacity,_width,source⟩ := RegistrationNativePlatformConcreteSource.response_writer reserve view admitted
    have encoded := congrFun source before
    simp only [RegistrationNativePlatformSourceCompletion.encodeWith,StateT.run] at supported
    rw [encoded,map_apply,support_map] at supported
    obtain ⟨allocation,_reserved,same⟩ := supported
    rcases allocation with ⟨allocation,after⟩
    cases allocation with
    | Err error =>
      have reply := congrArg Prod.fst same
      rw [returned] at reply
      cases reply
    | Ok value =>
      have reply := congrArg Prod.fst same
      rw [returned] at reply
      have equal := Option.some.inj (RustM.ok.inj reply)
      simp only [vectorEncode,dite_eq_left admitted]
      exact congrArg core.option.Option.Some equal
  · have rejected := congrFun (RegistrationNativePlatformConcreteSource.response_rejected reserve view (Nat.lt_of_not_ge admitted)) before
    simp only [RegistrationNativePlatformSourceCompletion.encodeWith,StateT.run] at supported
    rw [rejected] at supported
    cases supported
    cases returned

/-- The actual publication encoder's public-coin forwarding retains its exact successful source bytes and complete platform result. -/
theorem encoding (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.SignedResponseView) (before : RegistrationNativePlatformPublicationCompiler.PublicState Platform)
    (result : RustM (core.option.Option (alloc.vec.Vec U8)) × RegistrationNativePlatformPublicationCompiler.PublicState Platform)
    (supported : result ∈ support ((RegistrationNativePlatformPublicationCompiler.encoding (n := n)
      (RegistrationNativePlatformConcreteSource.writer reserve) view).run before))
    (bytes : alloc.vec.Vec U8) (returned : result.1=.ok (.Some bytes)) : vectorEncode view=.Some bytes := by
  simp only [RegistrationNativePlatformPublicationCompiler.encoding,StateT.run,support_map] at supported
  obtain ⟨actual,called,equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  exact source_writer reserve view before.2 actual original bytes ((congrArg Prod.fst equal).trans returned)

/-- Successful source vector encoding is the literal mathematical wire encoding, with decoder readback independently proved in the maintained source codec. -/
theorem wire_encoding (view : registration.SignedResponseView) (bytes : alloc.vec.Vec U8)
    (encoded : vectorEncode view=.Some bytes) :
    RegistrationNativePlatformConcreteSource.wire.encodeResponse view=.Some (TranscriptAuthParts.absSlice bytes) := by
  unfold vectorEncode at encoded
  split at encoded
  · rename_i admitted
    have equal := Option.some.inj encoded
    rw [←equal]
    exact RegistrationNativeConcreteCodec.response_bytes view admitted
  · cases encoded

/-- Complete actual response hash/sign/source encoding retains its admitted ciphertext and Server identity, deriving concrete source serialization internally. -/
theorem program (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (frame : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse (alloc.vec.Vec U8))
    (before after : RegistrationNativePlatformPublicationCompiler.PublicState Platform)
    (supported : (.ok (.Ok published),after) ∈ support
      ((RegistrationNativePlatformServerPublication.program
        (RegistrationNativePlatformSigningCompiler.signing (n := n) source frame sign)
        (RegistrationNativePlatformPublicationCompiler.encoding (RegistrationNativePlatformConcreteSource.writer reserve)) pending).run before)) :
    RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
      pending.candidate.kem_ciphertext (TranscriptAuthParts.absSlice published.encoded) ∧
    RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
      pending.candidate.server_identity_public_key (TranscriptAuthParts.absSlice published.encoded) := by
  have pureSupport := RegistrationNativePlatformResponsePublicationSupport.program
    (RegistrationNativePlatformSigningCompiler.signing source frame sign)
    (RegistrationNativePlatformPublicationCompiler.encoding (RegistrationNativePlatformConcreteSource.writer reserve))
    vectorEncode (fun view bytes possible => by
      obtain ⟨previous,next,actual⟩ := possible
      exact encoding reserve view previous (.ok (.Some bytes),next) actual bytes rfl)
    pending published ⟨before,after,supported⟩
  obtain ⟨cipherView,encoded,ciphertext⟩ := RegistrationNativeResponseCiphertext.program_ciphertext vectorEncode pending published pureSupport
  obtain ⟨identityView,identityEncoded,identity⟩ := RegistrationNativeResponseIdentity.program_identity vectorEncode pending published pureSupport
  exact ⟨⟨cipherView,wire_encoding cipherView published.encoded encoded,ciphertext⟩,
    ⟨identityView,wire_encoding identityView published.encoded identityEncoded,identity⟩⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.source_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.source_writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.encoding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.wire_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.wire_encoding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationConcrete.program
