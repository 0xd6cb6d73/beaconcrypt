-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointFinish

/-! The complete native owner as one executable private-service client. All original tail requests and their shared state remain in the same experiment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler
open PqxdhRefinement PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointFinish (State onPool onNative)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

abbrev Spec (KemSK Response : Type) := PqxdhLiveKemBirth.Spec KemSK + PqxdhBeaconPhase2Publication.NativeTailSpec Response

def poolLift : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (Spec KemSK Response)) :=
  fun query => (Spec KemSK Response).query (.inl query)

def tailLift : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (OracleComp (Spec KemSK Response)) :=
  fun query => (Spec KemSK Response).query (.inr query)

noncomputable def compiler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhRegistrationJointFinish.Spec Response) (OracleComp (Spec KemSK Response))
  | .inl query => simulateQ poolLift (PqxdhRegistrationJointPreparation.compiler setup codec query)
  | .inr query => (Spec KemSK Response).query (.inr query)

noncomputable def impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (Spec KemSK Response) (StateT (State KemSK) ProbComp)
  | .inl query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query)
  | .inr query => onNative (sourceBeaconTail setup codec query)

/-- Every emitted private service request and native tail request is interpreted as the exact original callback, including its whole product state and optional reply. -/
theorem compiler_interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    impl setup codec ∘ₛ compiler setup codec = PqxdhRegistrationJointFinish.callbacks setup codec := by
  have routed : impl setup codec ∘ₛ poolLift =
      fun query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query) := by
    funext query
    exact simulateQ_spec_query (impl setup codec) (.inl query)
  funext query state
  cases query with
  | inl query =>
      simp only [QueryImpl.apply_compose, compiler, ← QueryImpl.simulateQ_compose, routed]
      change (simulateQ (fun query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query))
        (PqxdhRegistrationJointPreparation.compiler setup codec query)).run state = _
      rw [PqxdhRegistrationJointFinish.pool_program]
      rfl
  | inr query =>
      simp only [QueryImpl.apply_compose, compiler, simulateQ_spec_query]
      rfl

/-- The complete compiled adaptive program has exactly the original indexed callbacks and full state; intermediate service replies remain internal to the source continuation. -/
theorem program_interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (PqxdhRegistrationJointFinish.Spec Response) Result) :
    simulateQ (impl setup codec) (simulateQ (compiler setup codec) program) =
      simulateQ (PqxdhRegistrationJointFinish.callbacks setup codec) program := by
  rw [← QueryImpl.simulateQ_compose, compiler_interpreted]

abbrev Kind := Option PqxdhRegistrationJointPreparationCosts.Kind

/-- `none` counts the original native tail. `some localCall` counts every other private-service capability, including generation, signing, reveals and local coins. -/
def classify : (Spec KemSK Response).Domain → Kind
  | .inl query => some (PqxdhRegistrationJointPreparationCosts.serviceClass (KemSK := KemSK) query)
  | .inr _ => none

def cap : Kind → Nat
  | none => 56
  | some kind => PqxdhRegistrationJointPreparationCosts.serviceCap kind

/-- Routing a private service program preserves every selective service-class count exactly, without adding a native-tail request. -/
theorem pool_queries (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (kind : Kind) (budget : Nat) :
    (simulateQ (poolLift (Response := Response)) program).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) budget ↔
      program.IsQueryBoundP
        (fun query => classify (KemSK := KemSK) (Response := Response) (.inl query) = kind) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, poolLift, isQueryBoundP_query_bind_iff, ih]
      rfl

/-- The original native tail counts only in its own class; routing it introduces no identity, KEM, reveal or local-coin service request. -/
theorem tail_queries (program : OracleComp (PqxdhBeaconPhase2Publication.NativeTailSpec Response) Result)
    (budget : Nat) (bounded : program.IsTotalQueryBound budget) (kind : Kind) :
    (simulateQ (tailLift (KemSK := KemSK)) program).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (if kind = none then budget else 0) := by
  cases kind with
  | none =>
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => True) _ program budget bounded.isQueryBoundP
      intro query
      simp [tailLift, classify, isQueryBoundP_query_iff]
  | some kind =>
      apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ program 0 (isQueryBoundP_false program 0)
      intro query
      simp [tailLift, classify, isQueryBoundP_query_iff]

def preCap : Kind → Nat
  | none => 0
  | some kind => PqxdhRegistrationJointPreparationCosts.serviceCap kind

/-- The actual compiled preparation emits one optional decapsulation, one optional joint identity DH, no other private-service capability, and no tail request. -/
theorem prepare_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (identity : PqxdhRegistrationJointBundle.Identity)
    (prekey oneTime : ScalarBytes) (keys : PqxdhRegistrationJointBundle.Key) (raw : Pqxdh.Bytes) (kind : Kind) :
    (simulateQ (poolLift (Response := Response))
      (simulateQ (PqxdhRegistrationJointPreparation.compiler setup codec)
        (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime keys raw))).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (preCap kind) := by
  rw [pool_queries]
  cases kind with
  | none =>
      simpa only [classify, reduceCtorEq, preCap] using isQueryBoundP_false
        (simulateQ (PqxdhRegistrationJointPreparation.compiler setup codec)
        (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime keys raw)) 0
  | some kind =>
      simpa only [classify, Option.some.injEq, preCap] using
        PqxdhRegistrationJointPreparationCosts.compiler_prepare_classes setup codec control identity prekey oneTime keys raw kind

end BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.compiler_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.compiler_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.program_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.program_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.pool_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.pool_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.tail_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.tail_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.prepare_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointFinishCompiler.prepare_queries
