-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityNoCreate
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepare

/-! Actual native preparation requests at most one indexed Ed identity, independently of every optional ML or pin failure. Ordinary source randomness and pin hashing create none. These are structural whole-AST bills, suitable for finite multi-user routing rather than only an event-relative handle bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps
open RegistrationNativeIdentityFrontend (Trusted Ambient)
variable {n : Nat} {KemSK Value Auxiliary : Type}

abbrev Creates (n : Nat) (KemSK : Type) : (Trusted n KemSK).Domain → Prop :=
  fun query => ¬ RegistrationNativeIdentityNoCreate.Allowed n KemSK query

theorem coins_zero (work : ProbComp Value) :
    (simulateQ (RegistrationNativeIdentitySourcePrepare.coins (n := n) (KemSK := KemSK)) work).IsQueryBoundP (Creates n KemSK) 0 := by
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativeIdentitySourcePrepare.coins, isQueryBoundP_query_iff, Creates,
    RegistrationNativeIdentityNoCreate.Allowed]

theorem hash_zero (request : beaconcrypt_core.registration.HashRequest) :
    (RegistrationNativeIdentitySourcePrepare.hash (n := n) (KemSK := KemSK) request).IsQueryBoundP (Creates n KemSK) 0 := by
  simp [RegistrationNativeIdentitySourcePrepare.hash, isQueryBoundP_query_iff, Creates,
    RegistrationNativeIdentityNoCreate.Allowed]

theorem identity_one :
    (RegistrationNativeIdentityInterface.create (Ambient n KemSK)).IsQueryBoundP (Creates n KemSK) 1 := by
  unfold RegistrationNativeIdentityInterface.create
  apply (isQueryBoundP_map_iff (spec := Trusted n KemSK) (p := Creates n KemSK) _ _ 1).mpr
  rw [isQueryBoundP_query_iff]
  simp [Creates, RegistrationNativeIdentityNoCreate.Allowed]

/-- The exact whole public preparation AST issues at most its one generated-identity request on every reply path. -/
theorem program_one (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    (RegistrationNativeIdentitySourcePrepare.program (n := n) (KemSK := KemSK) source edPin mlPin keyId).IsQueryBoundP
      (Creates n KemSK) 1 := by
  unfold RegistrationNativeIdentitySourcePrepare.program
  apply isQueryBoundP_bind (n := 0) (m := 1) (coins_zero _)
  intro generated _
  cases generated with
  | none => exact isQueryBoundP_pure (Creates n KemSK) _ 1
  | some credentials =>
      dsimp only
      cases begun : beaconcrypt_core.registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error | div => exact isQueryBoundP_pure (Creates n KemSK) _ 1
      | ok pending =>
          simp only
          cases requested : pending.request with
          | fail error | div => simpa only [requested] using isQueryBoundP_pure (Creates n KemSK) _ 1
          | ok request =>
              simp only
              apply isQueryBoundP_bind (n := 0) (m := 1) (hash_zero _)
              intro digest _
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error | div => exact isQueryBoundP_pure (Creates n KemSK) _ 1
              | ok result => cases result with
                | none => exact isQueryBoundP_pure (Creates n KemSK) _ 1
                | some pin =>
                    apply isQueryBoundP_bind (n := 1) (m := 0) identity_one
                    intro identity _
                    cases identity with
                    | none => exact isQueryBoundP_pure (Creates n KemSK) _ 0
                    | some identity =>
                        exact isQueryBoundP_bind (m := 0) (n := 0) (coins_zero _) (fun _ _ => isQueryBoundP_pure (Creates n KemSK) _ 0)

/-- The actual nested native constructor preparation has the same structural one-identity bill. -/
theorem prepare_one (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeIdentityFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env).IsQueryBoundP
      (Creates n KemSK) 1 := by
  rw [RegistrationNativeIdentitySourcePrepare.prepare_run, isQueryBoundP_map_iff]
  exact program_one source edPin mlPin keyId

end BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.coins_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.coins_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.hash_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.hash_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.identity_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.identity_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.program_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.program_one
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.prepare_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBirthCaps.prepare_one
