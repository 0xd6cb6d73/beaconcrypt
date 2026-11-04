-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree
import BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame
/-! The whole actual extracted Beacon finish tree emits only native World effects and indexed private KEM queries. Authentication, agreement and first-record safety are derived from their concrete request handlers, including optional failure continuations. This discharges the local Native reassembly frame without assuming a whole-controller frame. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Trusted Owner)
open RegistrationNativeLocalEnvironmentFrame (Allowed)
variable {n : Nat} {I KemSK A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Safe (work : OracleComp (Trusted n KemSK) A) := work.AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK))

theorem pure_safe (value : A) : Safe (pure value : OracleComp (Trusted n KemSK) A) := allQueriesSatisfy_pure _ _

theorem query_safe (query : (Trusted n KemSK).Domain) (allowed : Allowed query) : Safe ((Trusted n KemSK).query query : OracleComp (Trusted n KemSK) _) :=
  (allQueriesSatisfy_query_iff query Allowed).mpr allowed

theorem map_safe (observe : A → B) (work : OracleComp (Trusted n KemSK) A) (safe : Safe work) : Safe (observe <$> work) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind safe (fun value => pure_safe _)

theorem simulate_safe {J : Type} {queries : OracleSpec J}
    (handler : QueryImpl queries (OracleComp (Trusted n KemSK))) (safe : ∀ query, Safe (handler query))
    (work : OracleComp queries A) : Safe (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (safe query) ih

theorem coins_safe (work : ProbComp A) : Safe (RegistrationNativeAgreementJournal.coins (n := n) (KemSK := KemSK) work) :=
  simulate_safe (queries := unifSpec) (fun query => ((Trusted n KemSK).query (.inl (.inl query)) : OracleComp (Trusted n KemSK) _))
    (fun query => query_safe (.inl (.inl query)) trivial) work

theorem authentication_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Safe (AdapterPublicFinishFreeTree.authentication (n := n) (source := source) setup query) := by
  cases query with
  | hash request =>
      unfold AdapterPublicFinishFreeTree.authentication
      exact allQueriesSatisfy_bind (query_safe _ trivial) (fun _ => pure_safe _)
  | mldsa request | ed25519 request => exact pure_safe _

theorem primitive_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveRequest) :
    Safe (RegistrationNativeAgreementJournal.primitive (n := n) setup owner scalar query) := by
  unfold RegistrationNativeAgreementJournal.primitive
  apply simulate_safe
  intro lower
  cases lower with
  | inl other => exact coins_safe _
  | inr lower => exact query_safe _ trivial

theorem agreement_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Safe (RegistrationNativeAgreementJournal.core (n := n) setup owner scalar query) := by
  cases query with
  | root request => exact pure_safe _
  | _ => exact primitive_safe setup owner scalar _

theorem record_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) : Safe (RegistrationNativeRecordJournal.core (n := n) setup wire query) := by
  cases query with
  | hash transcript =>
      unfold RegistrationNativeRecordJournal.core
      exact allQueriesSatisfy_bind (query_safe _ trivial) (fun _ => pure_safe _)
  | _ => exact coins_safe _

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

theorem suffix_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (phase : agreement.AgreementEffect) :
    Safe (AdapterPublicFinishFreeTree.recordSuffix (n := n) setup wire self phase) := by
  cases phase with
  | Rejected optional => cases optional <;> exact pure_safe _
  | BeaconComplete agreed => exact map_safe _ _ (simulate_safe _ (record_safe setup wire) _)
  | _ => exact pure_safe _

theorem accepted_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    Safe (AdapterPublicFinishFreeTree.accepted (n := n) setup wire self owner scalar authenticated) := by
  unfold AdapterPublicFinishFreeTree.accepted
  apply allQueriesSatisfy_bind (simulate_safe _ (agreement_safe setup owner scalar) _)
  intro result
  cases result with
  | fail error | div => exact pure_safe _
  | ok phase => exact suffix_safe setup wire self phase

theorem after_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Safe (AdapterPublicFinishFreeTree.afterAuthentication (n := n) setup wire self owner scalar reply) := by
  cases reply with
  | fail error | div => exact pure_safe _
  | ok result => cases result with
    | Err control => exact pure_safe _
    | Ok authenticated => exact accepted_safe setup wire self owner scalar authenticated

theorem program_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    Safe (AdapterPublicFinishFreeTree.program (n := n) setup wire self pending input owner scalar) := by
  unfold AdapterPublicFinishFreeTree.program
  exact allQueriesSatisfy_bind (simulate_safe _ (authentication_safe setup) _)
    (after_safe setup wire _ owner scalar)

end BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.pure_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.pure_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.query_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.map_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.map_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.simulate_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.simulate_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.coins_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.coins_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.authentication_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.authentication_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.primitive_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.primitive_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.agreement_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.agreement_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.record_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.record_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.suffix_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.suffix_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.accepted_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.accepted_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.after_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.after_safe

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety.program_safe
