-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityPreparationSource
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRealizePrefix

/-! Complete native preparation source correspondence retains the current owner roster, mutable environment, context and World. Actual private seed-prefix persistence derives the stability of all previously owned public credentials. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePreparation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation ambient)
open RegistrationNativeIdentityRealization (Owned owners observe preparedReply)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Actual seed-free preparation realizes the complete original seed-bearing source preparation, including all optional failures and all current World/Env/owner fields. -/
theorem prepare_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : State n KemSK) (owned : Owned setup.joint before.identities current) :
    observe preparedReply <$>
      (simulateQ (implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before =
      (simulateQ (ambient (mlSource := source) setup checks representation created)
        (((RegistrationNativeBeaconFrontend.prepare source edPin mlPin keyId).run (owners before.identities current)).run env)).run before.context := by
  simp only [RegistrationNativeIdentitySourcePrepare.prepare_run,
    RegistrationNativeIdentitySourceNativeProgram.prepare_run, simulateQ_map, StateT.run_map, Functor.map_map]
  have projected := congrArg (fun (work : ProbComp (RustM (Option (RegistrationNativeBeaconFrontend.Prepared source)) × RegistrationNativeIdentityWorld.Context n KemSK)) => (fun result => (((result.1, owners before.identities current), env), result.2)) <$> work)
    (RegistrationNativeIdentityPreparationSource.program_source (source := source) setup checks representation created edPin mlPin keyId before)
  simp only [Functor.map_map, observe, ] at projected ⊢
  rw [← projected]
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result reached
  have same := RegistrationNativeIdentitySourceRealizePrefix.program_owners setup checks representation created
    (RegistrationNativeIdentitySourcePrepare.program source edPin mlPin keyId) before result current owned reached
  simp only [Function.comp_def, same]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePreparation.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePreparation.prepare_source
