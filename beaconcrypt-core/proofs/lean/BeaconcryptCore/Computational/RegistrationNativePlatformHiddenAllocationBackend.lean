-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyBackend
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService
/-! Actual selective material and external platform services preserve physical owner allocation. Only a literal forwarded appendOwner may allocate a World owner; prepare, material slots, indexed KEM rows, record operations and arbitrary public sampler effects keep that physical footprint zero. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeHiddenAllocationCore (WorldAllowed mapped simulation)
open RegistrationNativeHiddenAllocationService (EffectAllowed effect coins)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveHiddenInterpreter (State)
variable {n : Nat} {I KemSK ProviderState A : Type} {base : OracleSpec I}

def Allowed : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativeHiddenAllocationCore.Allowed query
  | .inr _ => True
private theorem all_true {J : Type} {spec : OracleSpec J} {V : Type} (work : OracleComp spec V) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem material (slot : PqxdhRecordLiftInterface.Slot n)
    (before : RegistrationNativeHiddenService.State n) :
    AllQueriesSatisfy ((RegistrationNativeHiddenService.material slot).run before) EffectAllowed := by
  simp only [RegistrationNativeHiddenService.material, StateT.run]
  split
  · trivial
  · apply mapped _ _ EffectAllowed
    apply simulation _ (fun _ => True) EffectAllowed _ _ (all_true _)
    intro query _
    exact (allQueriesSatisfy_query_iff _ _).mpr rfl

private theorem hidden_demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (message : RegistrationNativeRelatedFamily.Message)
    (before : RegistrationNativeHiddenService.State n) :
    AllQueriesSatisfy ((RegistrationNativeHiddenService.demand source input inside message).run before) EffectAllowed := by
  simp only [RegistrationNativeHiddenService.demand, StateT.run]
  repeat' split
  all_goals first
    | trivial
    | exact mapped _ _ EffectAllowed (material _ _)


private theorem known (bytes : Pqxdh.Bytes) (before : RegistrationNativeSelectiveHiddenService.State n) :
    AllQueriesSatisfy ((RegistrationNativeSelectiveHiddenService.known bytes).run before) EffectAllowed := by
  simp only [RegistrationNativeSelectiveHiddenService.known, StateT.run]
  split
  · trivial
  · exact mapped _ _ EffectAllowed (coins _)

private theorem selective_demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (message : RegistrationNativeRelatedFamily.Message) (before : RegistrationNativeSelectiveHiddenService.State n) :
    AllQueriesSatisfy ((RegistrationNativeSelectiveHiddenService.demand source input inside candidate message).run before) EffectAllowed := by
  simp only [RegistrationNativeSelectiveHiddenService.demand, StateT.run]
  repeat' split
  all_goals first
    | exact mapped _ _ EffectAllowed (known _ _)
    | simpa only [RegistrationNativeSelectiveHiddenService.onHidden, StateT.run] using
        mapped _ _ EffectAllowed (hidden_demand source input (RegistrationNativeSelectiveHiddenService.selected inside candidate) message before.1)

/-- One actual new backend leaf cannot append a physical owner unless its public source query explicitly requests it. -/
theorem query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (request : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState)
    (safe : Allowed (KemSK := KemSK) request) :
    AllQueriesSatisfy ((RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider request).run before) WorldAllowed := by
  cases request with
  | inr coin =>
    simp only [RegistrationNativePlatformSelectiveEntropyBackend.handler, StateT.run_lift, bind_pure_comp]
    exact mapped _ _ WorldAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
  | inl request =>
    change AllQueriesSatisfy ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider request).run before) WorldAllowed
    by_cases demanded : RegistrationNativePublicCaps.IsDemand (KemSK := KemSK) request
    · rcases request with (prepare | (message | common) | kem) | record
      all_goals try exact demanded.elim
      simp only [RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onKeys, StateT.run]
      exact mapped _ _ WorldAllowed (effect _ (selective_demand _ _ _ _ _ _))
    · rw [RegistrationNativeSelectiveHiddenInterpreter.query_other setup wire sign seed scalar candidate provider request demanded]
      simp only [RegistrationNativeSelectiveHiddenInterpreter.onBase, StateT.run]
      exact mapped _ _ WorldAllowed (RegistrationNativeHiddenAllocationService.handler setup wire sign seed scalar provider request before.1 safe)

/-- Arbitrary actual public query trees transport the same zero-append footprint through their full reached private state. -/
theorem program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A) (before : State n KemSK ProviderState)
    (safe : AllQueriesSatisfy work (Allowed (KemSK := KemSK))) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider) work).run before) WorldAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (query setup wire sign seed scalar candidate provider request before first)
      (fun reply => ih reply.1 reply.2 (later reply.1))
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend.program
