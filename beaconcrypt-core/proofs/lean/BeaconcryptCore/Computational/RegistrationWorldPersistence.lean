-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldRecords

/-! Actual native authentication hashes, agreement draws, first-record primitives, outgoing signatures, ongoing records and installations retain the same canonical private seed table and every earlier used-role marker. Persistence is derived from the concrete handlers and arbitrary adaptive schedules, including failed callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldPersistence
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (Persistent persistent_refl persistent_trans)
open RegistrationWorldAgreement (State)
variable {n : Nat} {Auxiliary Encoded Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Native agreement sampling preserves the canonical seed cache and used-role markers on every actual reply. -/
theorem agreement (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (before : State n Auxiliary)
    (result : RegistrationAgreementExecutor.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldAgreement.agreement source primitive query).run before)) :
    Persistent before.world.1 result.2.world.1 := by
  simp only [RegistrationWorldAgreement.agreement, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordLiftWorld.sampled_persists _ before.world.1 inner reached

/-- Actual outgoing hashing and optional signing preserve earlier private key material, including failed signatures. -/
theorem outgoing (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldSigning.State n)
    (result : RegistrationSigningShared.Spec.Range query × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((RegistrationWorldSigning.outgoing sign query).run before)) :
    Persistent before.1 result.2.1 := by
  cases query with
  | hash request =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact PqxdhRecordLiftWorld.effects_persists _ before.1 inner reached
  | sign request payload digest =>
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact PqxdhRecordLiftWorld.sampled_persists _ before.1 inner reached

/-- Response hashes, signing attempts and every native continuation retain the same earlier private seed. -/
theorem outgoing_program (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : RegistrationWorldSigning.State n)
    (result : Value × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((simulateQ (RegistrationWorldSigning.outgoing sign) work).run before)) :
    Persistent before.1 result.2.1 :=
  simulateQ_run_preservesInv _ (fun state => Persistent before.1 state.1)
    (fun query state previous after reached => persistent_trans before.1 state.1 after.2.1 previous
      (outgoing sign query state after reached)) work before (persistent_refl before.1) result supported

/-- The original World and actual outgoing source dispatch both preserve persistent private coordinates. -/
theorem signing_handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationWorldSigning.Spec n Encoded).Domain) (before : RegistrationWorldSigning.State n)
    (result : (RegistrationWorldSigning.Spec n Encoded).Range query × RegistrationWorldSigning.State n)
    (supported : result ∈ support ((RegistrationWorldSigning.handler setup codec route sign query).run before)) :
    Persistent before.1 result.2.1 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldSigning.handler, StateT.run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact PqxdhRecordLiftWorld.handler_persists setup codec route query before.1 inner reached
  | inr request => exact outgoing_program sign _ before result supported

/-- Interleaved native agreement, signing, administrative and ongoing-record queries preserve earlier material. -/
theorem agreement_handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : (RegistrationWorldAgreement.Spec n Encoded).Domain) (before : State n Auxiliary)
    (result : (RegistrationWorldAgreement.Spec n Encoded).Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldAgreement.handler setup codec route sign primitive query).run before)) :
    Persistent before.world.1 result.2.world.1 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldAgreement.handler, StateT.run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact signing_handler setup codec route sign query before.world inner reached
  | inr query => exact agreement setup.source primitive query before result supported

/-- Native first-record primitives update their actual primitive state without replacing canonical private seeds. -/
theorem record (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State n Auxiliary)
    (result : RawCtxMixedOwner.NativeSpec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.record setup codec query).run before)) :
    Persistent before.world.1 result.2.world.1 := by
  simp only [RegistrationWorldRecords.record, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact persistent_refl before.world.1

/-- First-record and authentication-style hashes share the same persistent World. -/
theorem shared (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary)
    (result : MldsaSharedNative.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.shared setup codec query).run before)) :
    Persistent before.world.1 result.2.world.1 := by
  cases query with
  | inl query =>
      simp only [RegistrationWorldRecords.shared, StateT.run, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      exact PqxdhRecordLiftWorld.effects_persists _ before.world.1 inner reached
  | inr query => exact record setup codec query before result supported

/-- Every actual first-record callback preserves the private receipt even if later encoding or signing rejects. -/
theorem record_handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : State n Auxiliary)
    (result : RegistrationRecordPrimitives.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldRecords.handler setup codec query).run before)) :
    Persistent before.world.1 result.2.world.1 := by
  simp only [RegistrationWorldRecords.handler, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact simulateQ_run_preservesInv _ (fun state => Persistent before.world.1 state.world.1)
    (fun query state previous after reached => persistent_trans before.world.1 state.world.1 after.2.world.1 previous
      (shared setup codec query state after reached)) _ before (persistent_refl before.world.1) inner reached

abbrev Spec (n : Nat) (Encoded : Type) := RegistrationWorldAgreement.Spec n Encoded + RegistrationRecordPrimitives.Spec

/-- The private source schedule combines the concrete existing handlers. -/
noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl (Spec n Encoded) (StateT (State n Auxiliary) ProbComp)
  | .inl query => RegistrationWorldAgreement.handler setup codec route sign primitive query
  | .inr query => RegistrationWorldRecords.handler setup codec query

/-- Every supported query of the combined actual native schedule preserves earlier canonical seeds and use markers. -/
theorem query_persists (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : (Spec n Encoded).Domain) (before : State n Auxiliary)
    (result : (Spec n Encoded).Range query × State n Auxiliary)
    (supported : result ∈ support ((handler setup codec route sign primitive query).run before)) :
    Persistent before.world.1 result.2.world.1 := by
  cases query with
  | inl query => exact agreement_handler setup codec route sign primitive query before result supported
  | inr query => exact record_handler setup codec query before result supported

/-- Arbitrary source interleavings preserve persistent material; the theorem has no preservation premise. -/
theorem program_persists (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp (Spec n Encoded) Value) (before : State n Auxiliary)
    (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (handler setup codec route sign primitive) work).run before)) :
    Persistent before.world.1 result.2.world.1 :=
  simulateQ_run_preservesInv _ (fun state => Persistent before.world.1 state.world.1)
    (fun query state previous after reached => persistent_trans before.world.1 state.world.1 after.2.world.1 previous
      (query_persists setup codec route sign primitive query state after reached))
    work before (persistent_refl before.world.1) result supported

/-- The actual cached seed, rather than merely its presence, and every earlier role-use bit survive the complete native suffix. -/
theorem program_receipts (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp (Spec n Encoded) Value) (before : State n Auxiliary)
    (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (handler setup codec route sign primitive) work).run before))
    (slot : PqxdhRecordLiftInterface.Slot n) (seed : PqxdhRecordLiftSeed.Seed)
    (cached : before.world.1.seeds.1 slot = some seed) :
    result.2.world.1.seeds.1 slot = some seed ∧
      ∀ other role, before.world.1.used other role = true → result.2.world.1.used other role = true := by
  have kept := program_persists setup codec route sign primitive work before result supported
  exact ⟨kept.1 cached, kept.2⟩

end BeaconcryptCore.Computational.RegistrationWorldPersistence

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.outgoing_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.outgoing_program
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.signing_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.signing_handler
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.agreement_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.agreement_handler
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.record
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.shared
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.record_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.record_handler
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.query_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.query_persists
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.program_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.program_persists
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldPersistence.program_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldPersistence.program_receipts
