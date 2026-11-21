-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! Actual Server build inlines publication against its current mutable Env and therefore emits no direct private-publication callback. Its derived footprint permits the receipt-preserving concrete state reassociation, after which the full native known108/public44 build equation applies. Both Env and private receipt logs remain distinct throughout. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild
open RegistrationNativeG3MaterializedFrontend (State ServiceSpec)
open RegistrationNativeG3MaterializedCurrentEnv (Allowed move back keys fallback)
open RegistrationNativeG3MaterializedBeaconComplete (localImpl)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK KeyState Value : Type}

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem effect_allowed (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    AllQueriesSatisfy (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK) query) (Allowed (KemSK := KemSK)) := by
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem effect_program_allowed (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) work) (Allowed (KemSK := KemSK)) :=
  RegistrationNativeHiddenAllocationCore.simulation _ (fun _ => True) (Allowed (KemSK := KemSK))
    (fun query _ => effect_allowed query) work (every work)

private theorem service_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.PublicSpec n).Domain) (env : RegistrationServerReferenceCompiler.Environment) :
    AllQueriesSatisfy ((RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      (RegistrationServerOpenReferenceCompiler.demand (KemSK := KemSK)) source writer sign query).run env) (Allowed (KemSK := KemSK)) := by
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
      (RegistrationServerOpenReferenceCompiler.demand (KemSK := KemSK)) source writer sign) work).run env) (Allowed (KemSK := KemSK)) := by
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
      source wire checks sign handle application).run control).run env) (Allowed (KemSK := KemSK)) :=
  service_program_allowed source wire.frameWrite sign _ env

/-- Known108 and public44 build have identical concrete mixed-private outcomes; the caller's current Env receipts and the separate private receipts are both retained. -/
theorem build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (control : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) (before : State n KeyState) :
    (simulateQ (localImpl true source wire.frameWrite sign seeds service implementation)
      (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)).run before =
      (simulateQ (localImpl false source wire.frameWrite sign seeds service implementation)
        (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)).run before := by
  have finiteSource := RegistrationNativeG3MaterializedFrontendBuild.build_source seeds (keys service) (fallback implementation)
    source wire checks sign handle application control (env, move before)
  simp only [RegistrationNativeG3MaterializedFrontendInterface.lower, StateT.run] at finiteSource
  have restored := congrArg (Functor.map (fun result => ((result.1, result.2.1), result.2.2))) finiteSource
  simp only [Functor.map_map, id_map'] at restored
  change (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface true seeds (keys service) (fallback implementation))
    (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)).run (move before) =
    (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface false seeds (keys service) (fallback implementation))
      (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)).run (move before) at restored
  have first := RegistrationNativeG3MaterializedCurrentEnv.program_source true source wire.frameWrite sign seeds service implementation
    (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)
    (build_allowed source wire checks sign handle application control env) before
  have second := RegistrationNativeG3MaterializedCurrentEnv.program_source false source wire.frameWrite sign seeds service implementation
    (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)
    (build_allowed source wire checks sign handle application control env) before
  have equal := first.trans (restored.trans second.symm)
  have original := congrArg (Functor.map (Prod.map id back)) equal
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def, back, move, id_map'] using original

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild.build_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild.build_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnvBuild.build
