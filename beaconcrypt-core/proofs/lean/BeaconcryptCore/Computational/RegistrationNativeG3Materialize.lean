-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld
import BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter

/-! Materializing the actual thin native World AST exposes only its existing hidden-reference installations as canonical slot requests. Every other request remains the literal actual World query. Interpreting these requests with the hidden branch reconstructs the entire original counted World execution, with no callback or frontend equality premise. The known branch is reserved for the actual stage-erasure proofs and the explicit repeated-role coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3Materialize
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedWorld (Spec Request Seeds step)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def materialize : QueryImpl (WorldSpec n) (OracleComp (Spec n))
  | .inl created => (Spec n).query (.ordinary (.inl created) trivial)
  | .inr (.inl (.inl coin)) => (Spec n).query (.ordinary (.inr (.inl (.inl coin))) trivial)
  | .inr (.inl (.inr capability)) => match capability with
      | .installServer keyId binding (.hidden slot) => (Spec n).query (.server keyId binding slot)
      | .installBeacon owner shell (.hidden slot) => (Spec n).query (.beacon owner shell slot)
      | .installServer keyId binding (.known kernel) =>
          (Spec n).query (.ordinary (.inr (.inl (.inr (.installServer keyId binding (.known kernel))))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
      | .installBeacon owner shell (.known kernel) =>
          (Spec n).query (.ordinary (.inr (.inl (.inr (.installBeacon owner shell (.known kernel))))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
      | .peerPresent keyId => (Spec n).query (.ordinary (.inr (.inl (.inr (.peerPresent keyId)))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
      | .ownerPresent owner => (Spec n).query (.ordinary (.inr (.inl (.inr (.ownerPresent owner)))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
      | .appendOwner identity keyId phase => (Spec n).query (.ordinary (.inr (.inl (.inr (.appendOwner identity keyId phase)))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
      | .advanceOwner owner phase => (Spec n).query (.ordinary (.inr (.inl (.inr (.advanceOwner owner phase)))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
      | .hash bytes => (Spec n).query (.ordinary (.inr (.inl (.inr (.hash bytes)))) (by simp [RegistrationNativeG3KnownWorldFrameCore.Allowed, RegistrationNativeSeedDelayFrames.ReadsSeed]))
  | .inr (.inr record) => (Spec n).query (.ordinary (.inr (.inr record)) trivial)

/-- Every materialized hidden capability is the same actual counted callback; ordinary queries and their complete poststates stay literal. -/
theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (WorldSpec n).Domain) :
    simulateQ (step setup codec route seeds false) (materialize query) =
      PqxdhRecordLiftWorld.handler setup codec route query := by
  rcases query with created | (coin | capability) | record
  · simp only [materialize, simulateQ_spec_query, step]
  · simp only [materialize, simulateQ_spec_query, step]
  · cases capability <;> try simp only [materialize, simulateQ_spec_query, step]
    all_goals rename_i ref
    all_goals cases ref <;> simp only [simulateQ_spec_query, step]
    all_goals rfl
  · simp only [materialize, simulateQ_spec_query, step]

/-- The complete actual World program is recovered through its materialized AST, including all adaptive errors, records, CTX operations and kernel installations. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) :
    simulateQ (step setup codec route seeds false) (simulateQ materialize work) =
      simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : step setup codec route seeds false ∘ₛ materialize = PqxdhRecordLiftWorld.handler setup codec route := by
    funext query
    exact query_source setup codec route seeds query
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeG3Materialize
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Materialize.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Materialize.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3Materialize.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3Materialize.program_source
