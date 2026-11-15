-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePreparation
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth

/-! The public identity constructor retains the literal indexed KEM and World-owner allocation suffix. Its private identity realization commutes with native owner append and the complete constructor's optional failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityFrontend (Ambient Trusted M Prepared)
open RegistrationNativeIdentityWorld (State implementation ambient)
open RegistrationNativeIdentityRealization (Owned owners observe)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def append (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (prepared : Prepared source) :
    M n KemSK RegistrationServerRoleBackend.State source (RustM (Option Nat)) := do
  let born ← RegistrationNativeIdentityFrontend.kem (.inr (.inl .create))
  let worldOwner ← RegistrationNativeIdentityFrontend.effect (.inr (.appendOwner keyId edPin .fresh))
  let current ← get
  let owner : RegistrationNativeIdentityFrontend.Owner source :=
    ⟨prepared.pin, prepared.identity, prepared.prekey,
      PqxdhRootTableInitialization.rootArray (setup.dh.publicKey prepared.prekey), born.1, born.2, worldOwner, .fresh, []⟩
  set (current ++ [owner])
  pure (.ok (some current.length))

/-- The actual public constructor delegates only the successful preparation branch to its literal indexed-birth suffix. -/
theorem create_factor (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeIdentityFrontend.create (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source edPin mlPin keyId = (do
      match ← RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok none => pure (.ok none)
      | .ok (some prepared) => append setup source edPin keyId prepared) := rfl

/-- The suffix forwards only actual ordinary KEM and owner-allocation queries before appending its public owner. -/
theorem append_program (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (prepared : Prepared source)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    ((append (n := n) setup source edPin keyId prepared).run current).run env =
      simulateQ (RegistrationNativeIdentityFrontend.ambientLift (n := n) (KemSK := KemSK)) (do
        let born ← ((Ambient n KemSK).query (.inr (.inr (.inl .create))) : OracleComp (Ambient n KemSK) (Nat × PqxdhKemIndCca.MlKem768PublicKey))
        let worldOwner ← ((Ambient n KemSK).query (.inl (.inr (.appendOwner keyId edPin .fresh))) : OracleComp (Ambient n KemSK) Nat)
        let owner : RegistrationNativeIdentityFrontend.Owner source :=
          ⟨prepared.pin, prepared.identity, prepared.prekey,
            PqxdhRootTableInitialization.rootArray (setup.dh.publicKey prepared.prekey), born.1, born.2, worldOwner, .fresh, []⟩
        pure ((.ok (some current.length), current ++ [owner]), env)) := by
  simp only [append, RegistrationNativeIdentityFrontend.kem, RegistrationNativeIdentityFrontend.effect,
    StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT.run_get, bind_pure_comp,
    simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityFrontend.ambientLift]
  all_goals rfl

/-- The actual indexed-birth suffix realizes the complete original source owner append, retaining its full current World, Env and context. -/
theorem append_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (prepared : Prepared source)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK) :
    observe (fun _ reply => reply) <$>
      (simulateQ (implementation (mlSource := source) setup checks representation created)
        (((append setup source edPin keyId prepared).run current).run env)).run before =
      (simulateQ (ambient (mlSource := source) setup checks representation created)
        (((RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin
          (RegistrationNativeIdentityRealization.seedFor before.identities prepared.identity) prepared.prekey).run
            (owners before.identities current)).run env)).run before.context := by
  rw [append_program, RegistrationNativeIdentitySourceFrame.ambient_program, RegistrationNativeBeaconBirth.append_program]
  simp only [map_bind, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  apply bind_congr
  intro born
  apply bind_congr
  intro worldOwner
  simp only [simulateQ_pure, StateT.run_pure, map_pure, observe,
    RegistrationNativeIdentityRealization.owner,
    RegistrationNativeIdentityFrontend.restore, RegistrationNativeBeaconBirth.owner,
    owners, List.length_map, List.map_append, List.map_cons, List.map_nil]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate.create_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate.create_factor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate.append_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate.append_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate.append_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate.append_source
