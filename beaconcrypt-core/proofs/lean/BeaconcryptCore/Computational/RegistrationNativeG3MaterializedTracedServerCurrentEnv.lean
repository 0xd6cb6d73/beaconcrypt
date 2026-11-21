-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild

/-! The original current-environment state reassociation applies to the actual observed Server build AST. The trace is retained as part of the full result, and both receipt coordinates and the entire World remain literal throughout the known/thin comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCurrentEnv
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedFrontend (State ServiceSpec)
open RegistrationNativeG3MaterializedBeaconComplete (localImpl)
open RegistrationNativeG3MaterializedCurrentEnv (move back keys fallback)
variable {n : Nat} {KemSK KeyState : Type}

/-- Exact actual current-Env build preserves its chronological observer, complete native result, both receipt logs and World. -/
theorem build (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (control : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) (trace : RegistrationNativeG2Trace.State) (before : State n KeyState) :
    (simulateQ (localImpl true source wire.frameWrite sign seeds service implementation)
      ((simulateQ RegistrationNativeG3MaterializedTracedServerTrace.handler
        (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)).run trace)).run before =
      (simulateQ (localImpl false source wire.frameWrite sign seeds service implementation)
        ((simulateQ RegistrationNativeG3MaterializedTracedServerTrace.handler
          (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run control).run env)).run trace)).run before := by
  let work := ((simulateQ RegistrationNativeG3MaterializedTracedServerTrace.handler
    (((RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK) source wire checks sign handle application).run control).run env)).run trace)
  have allowed : AllQueriesSatisfy work (RegistrationNativeG3MaterializedCurrentEnv.Allowed (KemSK := KemSK)) :=
    RegistrationNativeG3MaterializedTracedServerFootprint.observed_allowed _ _
      (RegistrationNativeG3MaterializedCurrentEnvBuild.build_allowed source wire checks sign handle application control env) trace
  have finiteSource := RegistrationNativeG3MaterializedTracedServerObservedBuild.build seeds (keys service) (fallback implementation)
    source wire checks sign handle application control env trace (move before)
  have first := RegistrationNativeG3MaterializedCurrentEnv.program_source true source wire.frameWrite sign seeds service implementation work allowed before
  have second := RegistrationNativeG3MaterializedCurrentEnv.program_source false source wire.frameWrite sign seeds service implementation work allowed before
  have equal := first.trans (finiteSource.trans second.symm)
  have restored := congrArg (Functor.map (Prod.map id back)) equal
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def, back, move, id_map'] using restored

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCurrentEnv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCurrentEnv.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerCurrentEnv.build
