-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate

/-! Literal native KEM/owner allocation introduces no extra Ed identity after preparation. The complete public create operation therefore has one structural Ed-create bill on all replies and failure paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityFrontend (M Ambient)
open RegistrationNativeIdentityBirthCaps (Creates)
variable {n : Nat} {ι KemSK Value Other : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem ambient_zero (work : OracleComp (Ambient n KemSK) Value) :
    (simulateQ RegistrationNativeIdentityFrontend.ambientLift work).IsQueryBoundP (Creates n KemSK) 0 := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativeIdentityFrontend.ambientLift, isQueryBoundP_query_iff, Creates,
    RegistrationNativeIdentityNoCreate.Allowed]

theorem append_zero (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativeIdentitySourceCreate.append (n := n) setup source edPin keyId prepared).run owners).run env).IsQueryBoundP
      (Creates n KemSK) 0 := by
  rw [RegistrationNativeIdentitySourceCreate.append_program]
  exact ambient_zero _

private theorem pure_zero (value : Value) (owners : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    (((pure value : M n KemSK RegistrationServerRoleBackend.State source Value).run owners).run env).IsQueryBoundP
      (Creates n KemSK) 0 := by
  simp only [StateT.run_pure]
  exact isQueryBoundP_pure _ _ _

private theorem bind_bound (work : M n KemSK RegistrationServerRoleBackend.State source Value)
    (next : Value → M n KemSK RegistrationServerRoleBackend.State source Other) (first later : Nat)
    (beforeBound : ∀ owners env, ((work.run owners).run env).IsQueryBoundP (Creates n KemSK) first)
    (afterBound : ∀ value owners env, (((next value).run owners).run env).IsQueryBoundP (Creates n KemSK) later)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    ((((work >>= next).run owners).run env)).IsQueryBoundP (Creates n KemSK) (first + later) := by
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (beforeBound owners env)
    (fun result _ => afterBound result.1.1 result.1.2 result.2)

/-- The actual complete native owner constructor creates at most one indexed Ed identity under every trusted reply. -/
theorem create_one (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativeIdentityFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env).IsQueryBoundP
      (Creates n KemSK) 1 := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor]
  apply bind_bound _ _ 1 0 (RegistrationNativeIdentityBirthCaps.prepare_one source edPin mlPin keyId) _ owners env
  intro prepared current currentEnv
  cases prepared with
  | fail error | div => exact pure_zero _ current currentEnv
  | ok result => cases result with
    | none => exact pure_zero _ current currentEnv
    | some prepared => exact append_zero setup edPin keyId prepared current currentEnv

end BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps.ambient_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps.ambient_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps.append_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps.append_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps.create_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCreateCaps.create_one
