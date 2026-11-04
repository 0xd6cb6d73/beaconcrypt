-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishRecordDictionary
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

theorem unlogged_program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec A) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (RegistrationNativeRecordJournal.unlogged setup wire) work : M n KemSK source Auxiliary A).run owners).run env) =
      (fun reply => ((reply, owners), env)) <$> simulateQ (RegistrationNativeRecordJournal.core setup wire) work := by
  have leaves : RegistrationNativeRecordJournal.unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire =
      (fun query => RegistrationNativeAgreementJournal.lift (RegistrationNativeRecordJournal.core setup wire query)) :=
    funext (RegistrationNativeRecordJournal.core_lift setup wire)
  rw [leaves, RegistrationNativeAgreementJournal.simulate_lift, RegistrationNativeAgreementJournal.lift_run]

noncomputable def tree (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (agreed : agreement.BeaconAgreement) (journal : RegistrationNativeRecordJournal.Journal) :
    OracleComp (Trusted n KemSK) (RustM RegistrationBeaconRecordExecutor.Result × RegistrationNativeRecordJournal.Journal) :=
  (simulateQ (RegistrationNativeRecordJournal.traced (RegistrationNativeRecordJournal.core setup wire))
    (RegistrationBeaconRecordExecutor.begin agreed)).run journal

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] {E : Type}
variable [localOps : LocalOperations (RustT (M n KemSK source Auxiliary))]

theorem source_erasure (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (authentication : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (M n KemSK source Auxiliary))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (agreed : agreement.BeaconAgreement)
    (owners : List (Owner source)) (env : EnvState Auxiliary) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
      AdapterPublicWrapperChildren.children authentication (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    (((AdapterPublicFinishBody.beginOpen (m := M n KemSK source Auxiliary) self agreed).run.run owners).run env) =
      (fun result => ((AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result.1), owners), env)) <$>
        tree setup wire agreed env.recordRequests := by
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
    AdapterPublicWrapperChildren.children authentication (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  rw [AdapterPublicFinishRecordDictionary.first_open setup wire erased authentication writer initial self agreed]
  rw [StateT.run_map, StateT.run_map, unlogged_program, Functor.map_map]
  have projected := congrArg (fun computation : OracleComp (Trusted n KemSK) (RustM RegistrationBeaconRecordExecutor.Result) =>
      (fun reply => ((AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid reply), owners), env)) <$> computation)
    (RegistrationNativeRecordJournal.traced_erasure
      (RegistrationNativeRecordJournal.core (n := n) setup wire) (RegistrationBeaconRecordExecutor.begin agreed) env.recordRequests)
  simpa only [tree, Functor.map_map, Prod.map, id_eq] using projected.symm

theorem source_with_journal (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (authentication : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (M n KemSK source Auxiliary))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (agreed : agreement.BeaconAgreement)
    (owners : List (Owner source)) (env : EnvState Auxiliary) :
    letI : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
      AdapterPublicWrapperChildren.children authentication (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    ((((simulateQ (RegistrationNativeBeaconFrontend.record setup wire) (RegistrationBeaconRecordExecutor.begin agreed) : M n KemSK source Auxiliary _).run owners).run env) =
      (fun result => ((result.1, owners), {env with recordRequests := result.2})) <$> tree setup wire agreed env.recordRequests) ∧
    ((((AdapterPublicFinishBody.beginOpen (m := M n KemSK source Auxiliary) self agreed).run.run owners).run env) =
      (fun result => ((AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result.1), owners), env)) <$>
        tree setup wire agreed env.recordRequests) := by
  let : ChildOperations (RustT (M n KemSK source Auxiliary)) :=
    AdapterPublicWrapperChildren.children authentication (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  exact ⟨RegistrationNativeRecordJournal.native_program setup wire _ owners env,
    source_erasure setup wire erased authentication writer initial self agreed owners env⟩
end BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal.unlogged_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal.unlogged_program
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal.source_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal.source_erasure
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal.source_with_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRecordJournal.source_with_journal
