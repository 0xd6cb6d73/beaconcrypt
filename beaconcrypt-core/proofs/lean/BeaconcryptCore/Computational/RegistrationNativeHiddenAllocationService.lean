-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! The thin service can allocate material and private KEM handles, while physical World owner allocation is reserved for the literal forwarded append capability. This follows from its actual coin, hash, native publication and key-service ASTs under every provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeHiddenAllocationProtocol (effectDelta delta)
open RegistrationNativeHiddenAllocationCore (Allowed WorldAllowed mapped simulation)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (State Provider)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def EffectAllowed (query : (EnvEffects n).Domain) : Prop := effectDelta query = 0

private theorem all_true {Index : Type} {spec : OracleSpec Index} {Result : Type} (work : OracleComp spec Result) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

/-- Every literal coin effect preserves physical owner allocation. -/
theorem coins (work : ProbComp Value) :
    AllQueriesSatisfy (PqxdhDeploymentEnvironment.coins (n := n) work) EffectAllowed := by
  apply simulation _ (fun _ => True) EffectAllowed _ work (all_true work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr rfl

/-- Forwarding a non-append environment effect into the one World preserves its footprint. -/
theorem effect (work : OracleComp (EnvEffects n) Value) (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ effectLift work) WorldAllowed := by
  apply simulation effectLift EffectAllowed WorldAllowed _ work safe
  intro query permitted
  exact (allQueriesSatisfy_query_iff _ _).mpr permitted

private theorem shared (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain) :
    AllQueriesSatisfy (RegistrationBoundSourceCompiler.sharedCompiler (n := n) source writer query) EffectAllowed := by
  cases query with
  | inl query => exact (allQueriesSatisfy_query_iff _ _).mpr rfl
  | inr query =>
      change AllQueriesSatisfy (simulateQ (PqxdhDeploymentEnvironment.primFwd source.crypto source)
        (RawCtxMixedShared.sharedAdapter source.crypto writer query)) EffectAllowed
      apply simulation _ (fun _ => True) EffectAllowed _ _ (all_true _)
      intro query _
      rcases query with request | (bytes | input)
      · trivial
      · exact mapped _ _ EffectAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
      · trivial

/-- Actual native record and ML publication callbacks use only coins and shared hash capabilities. -/
theorem publication (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (receipts : List RegistrationSigningShared.Receipt) :
    AllQueriesSatisfy ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run receipts) EffectAllowed := by
  cases query with
  | inl query =>
      apply mapped _ _ EffectAllowed
      exact simulation _ (fun _ => True) EffectAllowed (fun request _ => shared source writer request) _ (all_true _)
  | inr query => cases query with
    | hash request => exact mapped _ _ EffectAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
    | sign request payload digest => exact mapped _ _ EffectAllowed (coins _)

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

private theorem demand (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (message : RegistrationNativeRelatedFamily.Message)
    (before : RegistrationNativeHiddenService.State n) :
    AllQueriesSatisfy ((RegistrationNativeHiddenService.demand source input inside message).run before) EffectAllowed := by
  simp only [RegistrationNativeHiddenService.demand, StateT.run]
  repeat' split
  all_goals first
    | trivial
    | exact mapped _ _ EffectAllowed (material _ _)

/-- Every actual thin-backend query forwards physical allocation only when it is explicitly requested by the frontend. -/
theorem handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (safe : Allowed query) :
    AllQueriesSatisfy ((RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider query).run before) WorldAllowed := by
  rcases query with (message | ((message | (query | query)) | query)) | query
  · trivial
  · apply mapped _ _ WorldAllowed
    exact effect _ (demand _ _ _ _ _)
  · apply mapped _ _ WorldAllowed
    exact effect _ (publication _ _ _ query before.receipts)
  · simp only [RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect, StateT.run_lift, bind_pure_comp]
    exact mapped _ _ WorldAllowed ((allQueriesSatisfy_query_iff _ _).mpr (show delta (.inr (.inl query)) = 0 from safe))
  · apply mapped _ _ WorldAllowed
    apply simulation _ (fun _ => True) WorldAllowed _ _ (all_true _)
    intro coin _
    exact (allQueriesSatisfy_query_iff _ _).mpr rfl
  · simp only [RegistrationNativeHiddenInterpreter.handler, StateT.run_lift, bind_pure_comp]
    cases query with
    | inl server => cases server <;> exact mapped _ _ WorldAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
    | inr owner => rcases owner with ⟨owner, send | raw⟩ <;> exact mapped _ _ WorldAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)

/-- An allocation-free actual frontend AST remains allocation-free after the complete same-World thin interpretation. -/
theorem program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) (safe : AllQueriesSatisfy work Allowed) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider) work).run before)
      WorldAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (handler setup wire sign seed scalar provider query before first)
        (fun reply => ih reply.1 reply.2 (later reply.1))

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.coins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.publication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService.program
