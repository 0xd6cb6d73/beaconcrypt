-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPhase

/-! The private candidate phase is absent until the selected parsed attempt begins. This invariant is derived from the actual routing and actual SDK counter update, independently of session handles, getter counts, authentication success and arbitrary native failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeKemOpenProvider (State implementation counter)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def Safe (parsed : Nat) (state : State n mlSource KemSK) : Prop := counter state ≤ parsed → state.2 = none

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Every native call outside the selected parsed attempt preserves the private candidate phase. -/
theorem parsed_ordinary (query : TypedSpec.Domain) (before after : State n mlSource KemSK)
    (different : counter before ≠ parsed) (value : TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed query)).run).run before)) :
    after.2 = before.2 := by
  let call := query
  cases query with
  | inl coin =>
      exact RegistrationNativeKemOpenPhase.routed_program setup checks wire route representation created credential
        selected pairs publicKey real (RegistrationNativeKemDispatcherCompiler.handler setup wire checks call) before after value supported
  | inr command =>
      cases command with
      | accept packet =>
          simp only [RegistrationNativeKemParsedRouting.handler, RegistrationNativeKemParsedRouting.get,
            simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind] at supported
          rw [RegistrationNativeKemOpenProvider.get_run] at supported
          simp only [pure_bind, Option.elim_some] at supported
          have different' : (RegistrationNativeKemServerState.mask before.1.1).parsedAccepts ≠ parsed := different
          have flag : decide ((RegistrationNativeKemServerState.mask before.1.1).parsedAccepts = parsed) = false := by simp [different']
          rw [flag] at supported
          exact RegistrationNativeKemOpenPhase.routed_program setup checks wire route representation created credential
            selected pairs publicKey real (RegistrationNativeKemDispatcherCompiler.handler setup wire checks call)
              _ after value supported
      | _ =>
          exact RegistrationNativeKemOpenPhase.routed_program setup checks wire route representation created credential
            selected pairs publicKey real (RegistrationNativeKemDispatcherCompiler.handler setup wire checks call) before after value supported

/-- Every nonaccept native command preserves the phase even when its counter is the selected ordinal. -/
theorem parsed_nonaccept (query : TypedSpec.Domain) (nonaccept : RegistrationNativeKemOpenTypedCounter.increment query = 0)
    (before after : State n mlSource KemSK) (value : TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed query)).run).run before)) :
    after.2 = before.2 := by
  let call := query
  cases query with
  | inl coin =>
      exact RegistrationNativeKemOpenPhase.routed_program setup checks wire route representation created credential
        selected pairs publicKey real (RegistrationNativeKemDispatcherCompiler.handler setup wire checks call) before after value supported
  | inr command =>
      cases command with
      | accept packet => cases nonaccept
      | _ =>
          exact RegistrationNativeKemOpenPhase.routed_program setup checks wire route representation created credential
            selected pairs publicKey real (RegistrationNativeKemDispatcherCompiler.handler setup wire checks call) before after value supported

/-- The actual typed dispatcher preserves the initialized absence of a candidate before the selected attempt. -/
theorem typed_safe (query : TypedSpec.Domain) (before after : State n mlSource KemSK) (prior : Safe parsed before)
    (value : TypedSpec.Range query)
    (supported : (some value, after) ∈ support
      (((simulateQ provider (RegistrationNativeKemParsedRouting.handler setup checks wire parsed query)).run).run before)) :
    Safe parsed after := by
  have advanced := RegistrationNativeKemOpenTypedCounter.parsed_counter setup checks wire route representation created credential
    selected pairs publicKey real parsed query before after value supported
  intro later
  have earlier : counter before ≤ parsed := by omega
  by_cases nonaccept : RegistrationNativeKemOpenTypedCounter.increment query = 0
  · exact (parsed_nonaccept setup checks wire route representation created credential selected pairs publicKey real parsed
      query nonaccept before after value supported).trans (prior earlier)
  · have one : RegistrationNativeKemOpenTypedCounter.increment query = 1 := by
      cases query with
      | inl coin => cases nonaccept rfl
      | inr command => cases command <;> simp_all [RegistrationNativeKemOpenTypedCounter.increment]
    have different : counter before ≠ parsed := by omega
    exact (parsed_ordinary setup checks wire route representation created credential selected pairs publicKey real parsed
      query before after different value supported).trans (prior earlier)

/-- Arbitrary original typed programs derive the same preselected-phase invariant under the actual candidate provider. -/
theorem typed_work_safe (work : OracleComp TypedSpec Value) (before after : State n mlSource KemSK)
    (prior : Safe parsed before) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ (provider ∘ₛ RegistrationNativeKemParsedRouting.handler setup checks wire parsed) work).run).run before)) :
    Safe parsed after := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure original =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
      rw [supported.2]
      exact prior
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
      cases reply with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
            reduceCtorEq, false_and] at tail
      | some reply =>
          exact ih reply reached after
            (typed_safe setup checks wire route representation created credential selected pairs publicKey real parsed
              query before reached prior reply called) tail

/-- The actual raw adapter preserves the same invariant through parsing, public failure projection and every original typed callback. -/
theorem raw_work_safe (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before after : State n mlSource KemSK) (prior : Safe parsed before) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ (RegistrationNativeKemOpenRawCounter.native setup checks wire route representation created credential
        selected pairs publicKey real parsed) work).run).run before)) : Safe parsed after := by
  apply typed_work_safe setup checks wire route representation created credential selected pairs publicKey real parsed
    (RegistrationNativeRawAdapter.compile wire work) before after prior value
  simpa only [RegistrationNativeRawAdapter.compile, RegistrationNativeKemOpenRawCounter.native,
    QueryImpl.simulateQ_compose] using supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.parsed_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.parsed_ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.parsed_nonaccept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.parsed_nonaccept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.typed_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.typed_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.typed_work_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.typed_work_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.raw_work_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPhaseCounter.raw_work_safe
