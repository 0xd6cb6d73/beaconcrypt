-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCounterIndependence
import BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform
import BeaconcryptCore.Computational.RegistrationNativeKemWorldAgreement

/-! Literal native first-record and outgoing response-signing primitives keep their complete state, logs and shared cache independently of the omitted private uniform-count input. This is the local operational fact used to open ordinary SDK response construction around a selected KEM getter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationNativeKemWorldAgreement (mask)
open RegistrationNativeKemCounterIndependence (Stable program_stable)
variable {ι KemSK Reader Response Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

private theorem record_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldRecords.record setup codec query).run before =
      Prod.map id mask <$> (RegistrationWorldRecords.record setup codec query).run (mask before) := by
  have law := congrArg (fun work => (fun result => (result.1,
      { before with world := ({ before.world.1 with primitive := result.2 }, before.world.2) })) <$> work)
    (RegistrationNativeKemWorldRecordUniform.primitive_input setup codec query before.world.1.primitive)
  simp only [RegistrationWorldRecords.record, StateT.run, Functor.map_map, Prod.map, id_eq,
    mask, RegistrationNativeKemWorldUniform.mask, RegistrationNativeKemWorldRecordUniform.primitiveMask] at law ⊢
  convert law using 1

private theorem shared_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldRecords.shared setup codec query).run before =
      Prod.map id mask <$> (RegistrationWorldRecords.shared setup codec query).run (mask before) := by
  cases query with
  | inl query =>
      have law := congrArg (fun work => (fun result => (result.1,
          { before with world := (result.2, before.world.2) })) <$> work)
        (RegistrationNativeKemWorldEffects.effects_input (.inr (.hash query.2)) before.world.1)
      simp only [RegistrationWorldRecords.shared, StateT.run, Functor.map_map, Prod.map, id_eq,
        mask, RegistrationNativeKemWorldUniform.mask] at law ⊢
      convert law using 1
  | inr query => exact record_input setup codec query before

/-- Initial64, ongoing76, raw writer, AEAD and commitment callbacks retain the exact request-kind log and populated AD under the uniform-count projection. -/
theorem record_handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldRecords.handler setup codec query).run before =
      Prod.map id mask <$> (RegistrationWorldRecords.handler setup codec query).run (mask before) := by
  have law := congrArg (fun work => (fun result => (result.1,
      { result.2 with recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall query] })) <$> work)
    (program_stable mask (fun _ => rfl) (RegistrationWorldRecords.shared setup codec) (shared_input setup codec)
      (RegistrationRecordPrimitives.callbacks setup.source query) before)
  simp only [RegistrationWorldRecords.handler, StateT.run, Functor.map_map, Prod.map, id_eq, mask] at law ⊢
  convert law using 1

/-- Every actual first-record controller, including all optional failure branches, has the same complete projected output. -/
theorem record_program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : State n Auxiliary) :
    Prod.map id mask <$> (simulateQ (RegistrationWorldRecords.handler setup codec) work).run before =
      Prod.map id mask <$> (simulateQ (RegistrationWorldRecords.handler setup codec) work).run (mask before) :=
  program_stable mask (fun _ => rfl) _ (record_handler_input setup codec) work before

def signingMask (before : RegistrationWorldSigning.State n) : RegistrationWorldSigning.State n :=
  (RegistrationNativeKemWorldUniform.mask before.1, before.2)

/-- Outgoing signing samples its actual primitive and preserves every chronological receipt, including failures, in the same shared cache. -/
theorem signing_input
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldSigning.State n) :
    Prod.map id signingMask <$> (RegistrationWorldSigning.outgoing sign query).run before =
      Prod.map id signingMask <$> (RegistrationWorldSigning.outgoing sign query).run (signingMask before) := by
  cases query with
  | hash request =>
      have law := congrArg (fun work => (fun result => (result.1, (result.2, before.2))) <$> work)
        (RegistrationNativeKemWorldEffects.effects_input
          (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) before.1)
      simp only [RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map, id_eq, signingMask] at law ⊢
      convert law using 1
  | sign request payload digest =>
      have law := congrArg (fun work => (fun result => (result.1, (result.2,
          before.2 ++ [⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩, digest⟩]))) <$> work)
        (RegistrationNativeKemWorldUniform.sampled_input (sign request) before.1)
      simp only [RegistrationWorldSigning.outgoing, StateT.run, Functor.map_map, Prod.map, id_eq, signingMask] at law ⊢
      convert law using 1

/-- Arbitrary native response signing/publication programs preserve the same source state under the counter-only projection. -/
theorem signing_program_input
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : RegistrationWorldSigning.State n) :
    Prod.map id signingMask <$> (simulateQ (RegistrationWorldSigning.outgoing sign) work).run before =
      Prod.map id signingMask <$> (simulateQ (RegistrationWorldSigning.outgoing sign) work).run (signingMask before) :=
  program_stable signingMask (fun _ => rfl) _ (signing_input sign) work before

end BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.record_handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.record_handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.record_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.record_program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.signing_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.signing_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.signing_program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompletionPrimitives.signing_program_input
