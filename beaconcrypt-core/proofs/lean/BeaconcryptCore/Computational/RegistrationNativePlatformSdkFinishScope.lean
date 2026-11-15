-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree
import BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame
/-! The whole actual extracted Beacon finish tree emits only native World effects and indexed private KEM queries. Authentication, agreement and first-record safety are derived from their concrete request handlers, including optional failure continuations. This discharges the local Native reassembly frame without assuming a whole-controller frame. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishScope
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Trusted Owner)

variable {n : Nat} {I KemSK A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Scoped (work : OracleComp (Trusted n KemSK) A) := work.AllQueriesSatisfy (RegistrationNativeWorldOwnerFrame.Safe (n := n) (KemSK := KemSK))

private theorem pure_safe (value : A) : Scoped (pure value : OracleComp (Trusted n KemSK) A) := allQueriesSatisfy_pure _ _

private theorem query_safe (query : (Trusted n KemSK).Domain) (allowed : RegistrationNativeWorldOwnerFrame.Safe query) : Scoped ((Trusted n KemSK).query query : OracleComp (Trusted n KemSK) _) :=
  (allQueriesSatisfy_query_iff query RegistrationNativeWorldOwnerFrame.Safe).mpr allowed

private theorem map_safe (observe : A → B) (work : OracleComp (Trusted n KemSK) A) (safe : Scoped work) : Scoped (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind safe (fun value => pure_safe _)

private theorem simulate_safe {J : Type} {queries : OracleSpec J}
    (handler : QueryImpl queries (OracleComp (Trusted n KemSK))) (safe : ∀ query, Scoped (handler query))
    (work : OracleComp queries A) : Scoped (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (safe query) ih

private theorem coins_safe (work : ProbComp A) : Scoped (RegistrationNativeAgreementJournal.coins (n := n) (KemSK := KemSK) work) :=
  simulate_safe (queries := unifSpec) (fun query => ((Trusted n KemSK).query (.inl (.inl query)) : OracleComp (Trusted n KemSK) _))
    (fun query => query_safe (.inl (.inl query)) trivial) work

private theorem authentication_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Scoped (BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.authentication (n := n) (source := source) setup query) := by
  cases query with
  | hash request =>
      unfold BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.authentication
      exact allQueriesSatisfy_bind (query_safe _ trivial) (fun _ => pure_safe _)
  | mldsa request | ed25519 request => exact pure_safe _

private theorem primitive_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveRequest) :
    Scoped (RegistrationNativeAgreementJournal.primitive (n := n) setup owner scalar query) := by
  unfold RegistrationNativeAgreementJournal.primitive
  apply simulate_safe
  intro lower
  cases lower with
  | inl other => exact coins_safe _
  | inr lower => exact query_safe _ trivial

private theorem agreement_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Scoped (RegistrationNativeAgreementJournal.core (n := n) setup owner scalar query) := by
  cases query with
  | root request => exact pure_safe _
  | _ => exact primitive_safe setup owner scalar _

private theorem record_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) : Scoped (RegistrationNativeRecordJournal.core (n := n) setup wire query) := by
  cases query with
  | adHash request =>
      unfold RegistrationNativeRecordJournal.core
      exact allQueriesSatisfy_bind (query_safe _ trivial) (fun _ => pure_safe _)
  | hash transcript =>
      unfold RegistrationNativeRecordJournal.core
      exact allQueriesSatisfy_bind (query_safe _ trivial) (fun _ => pure_safe _)
  | _ => exact coins_safe _

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

private theorem suffix_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (phase : agreement.AgreementEffect) :
    Scoped (BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.recordSuffix (n := n) setup wire self phase) := by
  cases phase with
  | Rejected optional => cases optional <;> exact pure_safe _
  | BeaconComplete agreed => exact map_safe _ _ (simulate_safe _ (record_safe setup wire) _)
  | _ => exact pure_safe _

private theorem accepted_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    Scoped (BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.accepted (n := n) setup wire self owner scalar authenticated) := by
  unfold BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.accepted
  apply allQueriesSatisfy_bind (simulate_safe _ (agreement_safe setup owner scalar) _)
  intro result
  cases result with
  | fail error | div => exact pure_safe _
  | ok phase => exact suffix_safe setup wire self phase

private theorem after_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Scoped (BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.afterAuthentication (n := n) setup wire self owner scalar reply) := by
  cases reply with
  | fail error | div => exact pure_safe _
  | ok result => cases result with
    | Err control => exact pure_safe _
    | Ok authenticated => exact accepted_safe setup wire self owner scalar authenticated

theorem program_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Scoped (BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.program (n := n) setup wire self pending input owner scalar) := by
  unfold BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.program
  exact allQueriesSatisfy_bind (simulate_safe _ (authentication_safe setup) _)
    (after_safe setup wire _ owner scalar)

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishScope.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishScope.program_safe
