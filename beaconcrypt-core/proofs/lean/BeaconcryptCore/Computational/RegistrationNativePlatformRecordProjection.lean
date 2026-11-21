-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTraceAdapter

/-! Every successful actual platform first-record trace supplies the exact existing five-callback source trace after forgetting only enclosing RustM failure constructors and the proven-irrelevant mutable transcript replacement. Complete callback states and actual supported successful replies are retained. This is a local trace projection, not a whole-profile game equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordProjection
open RegistrationRecordPrimitives (Spec)
open RegistrationNativePlatformRecordTrace (Seal Hash Write)
variable {S A : Type}

open RegistrationNativePlatformTraceAdapter (implementation optional digest)

/-- Actual successful source platform callbacks yield the same five callback operands, states and exact source resumes in the existing trace interface. -/
noncomputable def project (original : QueryImpl Spec (StateT S ProbComp)) (sealing : Seal S) (hash : Hash S) (write : Write S)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (actual : RegistrationNativePlatformRecordTrace.Trace original sealing hash write initial completed before after) :
    RegistrationNativeServerRecordTrace.Trace (implementation original sealing hash write) initial completed before after := by
  refine ⟨actual.initialRequest, actual.initialReply, actual.first, actual.ratchet,
    actual.ratchetRequest, actual.ratchetReply, actual.second, actual.aead, actual.aeadRequest, actual.aeadReply,
    actual.third, actual.commitmentState, actual.transcript, actual.digestReply, actual.fourth, actual.writer,
    actual.writeRequest, actual.writeReply, actual.initialRequested, actual.initialCalled, actual.initialResumed,
    actual.ratchetRequested, actual.ratchetCalled, actual.ratchetResumed, actual.aeadRequested, ?_, actual.aeadResumed,
    actual.hashRequested, ?_, actual.hashResumed, actual.writeRequested, ?_, actual.writeResumed⟩
  · rw [implementation, StateT.run_map, support_map]
    exact Set.mem_image_of_mem (Prod.map optional id) actual.aeadCalled
  · rw [implementation, StateT.run_map, support_map]
    exact Set.mem_image_of_mem (Prod.map digest id) actual.hashCalled
  · rw [implementation, StateT.run_map, support_map]
    exact Set.mem_image_of_mem (Prod.map optional id) actual.writeCalled

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordProjection.project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordProjection.project
