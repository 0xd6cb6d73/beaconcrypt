-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace

/-! The actual inlined Server build emits only its actual material demand and shared World effects. Its chronological observer forwards each literal request once, so it retains every existing footprint used by the receipt-preserving source diagrams. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint
open RegistrationNativeG3MaterializedTracedServerTrace (Allowed handler)
variable {n : Nat} {KemSK Value : Type}

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem effect_allowed (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    AllQueriesSatisfy (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK) query) Allowed := by
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem effect_program_allowed (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) work) Allowed :=
  RegistrationNativeHiddenAllocationCore.simulation _ (fun _ => True) Allowed
    (fun query _ => effect_allowed query) work (every work)

private theorem service_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.PublicSpec n).Domain) (env : RegistrationServerReferenceCompiler.Environment) :
    AllQueriesSatisfy ((RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      (RegistrationServerOpenReferenceCompiler.demand (KemSK := KemSK)) source writer sign query).run env) Allowed := by
  cases query with
  | inl message =>
      simp only [RegistrationNativeCommonCompiler.service, StateT.run_lift, bind_pure_comp]
      exact RegistrationNativeHiddenAllocationCore.mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  | inr query =>
      simp only [RegistrationNativeCommonCompiler.service]
      rw [RegistrationNativeCommonCompiler.common_map]
      exact effect_program_allowed _

private theorem service_program_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) (env : RegistrationServerReferenceCompiler.Environment) :
    AllQueriesSatisfy ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      (RegistrationServerOpenReferenceCompiler.demand (KemSK := KemSK)) source writer sign) work).run env) Allowed := by
  induction work using OracleComp.inductionOn generalizing env with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (service_allowed source writer sign query env) (fun reached => ih reached.1 reached.2)

/-- The concrete current-Env build derives its zero direct-private-publication footprint from the actual inlined compiler. -/
theorem build_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (control : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) :
    AllQueriesSatisfy (((RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK)
      source wire checks sign handle application).run control).run env) Allowed :=
  service_program_allowed source wire.frameWrite sign _ env

/-- The actual chronological observer retains every original query footprint, including the no-direct-publication current-Env boundary. -/
theorem observed_allowed (predicate : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain → Prop)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (allowed : AllQueriesSatisfy work predicate) (before : RegistrationNativeG2Trace.State) :
    AllQueriesSatisfy ((simulateQ handler work).run before) predicate := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨current, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply allQueriesSatisfy_bind
      · exact RegistrationNativeHiddenAllocationCore.mapped _ _ predicate ((allQueriesSatisfy_query_iff _ _).mpr current)
      · intro reached
        exact ih reached.1 (later reached.1) reached.2

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint.build_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint.build_allowed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint.observed_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint.observed_allowed
