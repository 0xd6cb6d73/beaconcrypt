-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend

/-! Native verification, agreement, record and World callbacks do not mutate the outer Beacon owner list. Their complete environment, primitive/cache and indexed-KEM effects remain in the computation. This derived source footprint supports arbitrary owner-history invariants without assuming that the cryptographic callbacks preserve them. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def ReadOnly (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.1.2 = owners

private theorem pure_readonly (value : Value) :
    ReadOnly (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (pure value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_readonly {Next : Type} (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : ReadOnly work) (later : ∀ value, ReadOnly (next value)) :
    ReadOnly (work >>= next) := by
  intro owners env result supported
  rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨value, currentOwners⟩, currentEnv⟩, reached, continued⟩ := supported
  exact (later value currentOwners currentEnv result continued).trans (first owners env _ reached)

private theorem lift_readonly (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    ReadOnly (source := source) (StateT.lift work) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp] at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

theorem program_readonly {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (step : ∀ query, ReadOnly (implementation query)) (work : OracleComp spec Value) :
    ReadOnly (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_readonly value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_readonly _ _ (step query) ih

private theorem sample_readonly (work : ProbComp Value) :
    ReadOnly (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (sample work) :=
  program_readonly (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => lift_readonly _) work

theorem authentication_readonly (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    ReadOnly (n := n) (Auxiliary := Auxiliary) (authentication setup source query) := by
  cases query with
  | hash request => exact bind_readonly _ _ (lift_readonly _) (fun _ => pure_readonly _)
  | mldsa request => exact pure_readonly _
  | ed25519 request => exact pure_readonly _

theorem primitive_readonly (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    ReadOnly (n := n) (Auxiliary := Auxiliary) (primitive setup owner oneTime query) := by
  unfold primitive
  apply program_readonly
  intro lower
  cases lower with
  | inl query => exact sample_readonly _
  | inr query => exact lift_readonly _

theorem agreement_readonly (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Spec.Domain) :
    ReadOnly (n := n) (Auxiliary := Auxiliary) (agreement setup owner oneTime query) := by
  unfold agreement
  apply bind_readonly _ _ (lift_readonly _)
  intro _
  cases query
  all_goals first | exact primitive_readonly setup owner oneTime _ | exact pure_readonly _

theorem record_readonly (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    ReadOnly (n := n) (source := source) (Auxiliary := Auxiliary) (record setup wire query) := by
  unfold record
  apply bind_readonly _ _ (lift_readonly _)
  intro _
  cases query
  all_goals first
    | exact sample_readonly _
    | exact bind_readonly _ _ (lift_readonly _) (fun _ => pure_readonly _)

theorem abort_readonly (owner : Owner source) :
    ReadOnly (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (abort owner) :=
  bind_readonly _ _ (lift_readonly _) (fun _ => pure_readonly _)

end BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.program_readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.program_readonly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.authentication_readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.authentication_readonly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.primitive_readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.primitive_readonly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.agreement_readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.agreement_readonly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.record_readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.record_readonly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.abort_readonly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFootprint.abort_readonly
