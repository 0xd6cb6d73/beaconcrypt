-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate

/-! The complete indexed-identity native constructor realizes the literal original native constructor through its actual optional preparation and source KEM/owner allocation. Previously owned credentials are an internal source invariant, not public eligibility. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceConstruction
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation ambient)
open RegistrationNativeIdentityRealization (Owned owners observe preparedReply)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Actual complete seed-free owner creation has the complete original source result and native roster/Env/World on every optional failure or successful birth. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : State n KemSK) (owned : Owned setup.joint before.identities current) :
    observe (fun _ reply => reply) <$>
      (simulateQ (implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId).run current).run env)).run before =
      (simulateQ (ambient (mlSource := source) setup checks representation created)
        (((RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId).run (owners before.identities current)).run env)).run before.context := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor, RegistrationNativeBeaconFrontend.create]
  simp only [StateT.run_bind, simulateQ_bind, map_bind]
  rw [← RegistrationNativeIdentitySourcePreparation.prepare_source setup checks representation created edPin mlPin keyId current env before owned,
    bind_map_left]
  apply bind_congr
  rintro ⟨⟨⟨earlier, nextOwners⟩, nextEnv⟩, nextPrivate⟩
  cases earlier with
  | fail error =>
      simp only [observe, preparedReply, StateT.run_pure, simulateQ_pure, map_pure]
  | div =>
      simp only [observe, preparedReply, StateT.run_pure, simulateQ_pure, map_pure]
  | ok reply => cases reply with
    | none =>
        simp only [observe, preparedReply, Option.map_none, StateT.run_pure, simulateQ_pure, map_pure]
    | some prepared =>
        simp only [observe, preparedReply, Option.map_some]
        exact RegistrationNativeIdentitySourceCreate.append_source setup checks representation created source edPin keyId prepared
          nextOwners nextEnv nextPrivate

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceConstruction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceConstruction.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceConstruction.create_source
