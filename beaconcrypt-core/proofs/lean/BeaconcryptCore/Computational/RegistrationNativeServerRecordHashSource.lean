-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHashReceipt
import BeaconcryptCore.Computational.RegistrationNativeServerRecordTrace

/-! Every actual issued first-record source cut retains its exact commitment preimage and digest in the same later cache anchor. The actual writer continuation supplies the cache extension after hashing, so no final-cache membership is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerRecordHashSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeServerRecordTrace (Trace)
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded : Type} {base : OracleSpec ι}

/-- The actual Server first record's commitment query remains in its supplied later cache by the proved source writer extension. -/
theorem run (setup : Setup base KemSK) (codec : Codec Reader Encoded)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (before after : RegistrationWorldAgreement.State n Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((simulateQ (RegistrationWorldRecords.handler setup codec) (RegistrationServerRecordExecutor.fromInitial initial)).run before))
    (extension : after.world.1.primitive.2 ≤ cache) :
    ∃ trace : Trace (RegistrationWorldRecords.handler setup codec) initial completed before after,
    ∃ digest, trace.digestReply = .Some (RegistrationAuthenticationShared.digestArray digest) ∧
      cache ((), absBytes trace.transcript.bytes) = some digest := by
  obtain ⟨trace⟩ := RegistrationNativeServerRecordTrace.run (RegistrationWorldRecords.handler setup codec) initial completed before after supported
  obtain ⟨digest, replyEq, _beforeHash, cached⟩ := RegistrationNativeRecordHashReceipt.world setup codec trace.transcript trace.third trace.fourth trace.digestReply trace.hashCalled
  have throughWrite : trace.fourth.world.1.primitive.2 ≤ after.world.1.primitive.2 :=
    (RegistrationNativeWorldStageCache.records setup codec (RegistrationRecordPrimitives.Spec.query (.write trace.writeRequest))
      trace.fourth (trace.writeReply, after) (by simpa only [simulateQ_spec_query] using trace.writeCalled)).1
  exact ⟨trace, digest, replyEq, extension (throughWrite cached)⟩

/-- A same-run issued-response record cut supplies an actual commitment-query witness at that actual native call's later shared-cache anchor. -/
theorem issued (setup : Setup base KemSK) (codec : Codec Reader Encoded)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (cache : CtxRomAuth.CtxRO.QueryCache)
    (cut : RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup codec initial completed cache) :
    ∃ (before after : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
      (trace : Trace (RegistrationWorldRecords.handler setup codec) initial completed before after),
    ∃ digest, trace.digestReply = .Some (RegistrationAuthenticationShared.digestArray digest) ∧
      cache ((), absBytes trace.transcript.bytes) = some digest := by
  obtain ⟨before, after, supported, extension⟩ := cut
  obtain ⟨trace, digest, replyEq, cached⟩ := run setup codec initial completed before after cache supported extension
  exact ⟨before, after, trace, digest, replyEq, cached⟩

end BeaconcryptCore.Computational.RegistrationNativeServerRecordHashSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordHashSource.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordHashSource.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordHashSource.issued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordHashSource.issued
