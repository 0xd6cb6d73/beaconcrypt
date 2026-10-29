-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService

/-! The selective backend introduces only environment coin queries for nonselected protected outputs. Actual physical allocation still occurs exclusively at the frontend's literal append request. These footprints are proved from the actual selective demand and old non-demand callbacks under every provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativeHiddenAllocationCore (Allowed WorldAllowed mapped)
open RegistrationNativeHiddenAllocationService (EffectAllowed)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

private theorem no_capabilities (work : OracleComp (EnvEffects n) Value)
    (free : work.IsQueryBoundP RegistrationNativeHiddenServiceBounds.IsCapability 0) :
    AllQueriesSatisfy work EffectAllowed := by
  classical
  apply (isQueryBoundP_zero_iff work EffectAllowed).mp
  apply OracleComp.IsQueryBoundP.of_imp _ free
  intro query forbidden
  cases query with
  | inl coin => exact (forbidden rfl).elim
  | inr capability => trivial

private theorem other_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (safe : Allowed query)
    (other : ¬RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK) query) :
    AllQueriesSatisfy ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query).run before)
      WorldAllowed := by
  rw [RegistrationNativeSelectiveHiddenInterpreter.query_other setup wire sign seed scalar candidate provider query other]
  exact mapped _ _ WorldAllowed (RegistrationNativeHiddenAllocationService.handler setup wire sign seed scalar provider query before.1 safe)

/-- Every actual selective callback forwards physical allocation only at the same literal append operation. -/
theorem handler_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (safe : Allowed query) :
    AllQueriesSatisfy ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query).run before)
      WorldAllowed := by
  rcases query with (message | ((message | (publication | effect)) | kem)) | record
  · exact other_safe setup wire sign seed scalar candidate provider _ before safe (by intro impossible; cases impossible)
  · apply mapped _ _ WorldAllowed
    exact RegistrationNativeHiddenAllocationService.effect _ (no_capabilities _
      (RegistrationNativeSelectiveHiddenServiceInvariant.demand_free _ _ _ _ _ _))
  · exact other_safe setup wire sign seed scalar candidate provider _ before safe (by intro impossible; cases impossible)
  · exact other_safe setup wire sign seed scalar candidate provider _ before safe (by intro impossible; cases impossible)
  · exact other_safe setup wire sign seed scalar candidate provider _ before safe (by intro impossible; cases impossible)
  · exact other_safe setup wire sign seed scalar candidate provider _ before safe (by intro impossible; cases impossible)

/-- Every allocation-free actual frontend AST remains allocation-free through the complete selective backend. -/
theorem program_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState)
    (safe : AllQueriesSatisfy work Allowed) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before)
      WorldAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (handler_safe setup wire sign seed scalar candidate provider query before first)
        (fun reply => ih reply.1 reply.2 (later reply.1))

end BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService.handler_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService.program_safe
