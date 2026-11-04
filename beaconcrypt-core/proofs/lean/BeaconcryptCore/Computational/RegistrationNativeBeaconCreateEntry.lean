-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Constructor owner registration is explicit proof administration after the same generated KEM reply. This factors the existing native entry without repeating key generation, changing an owner index, or replacing any prior state. -/
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry
open RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def register (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : Prepared source) (born : Nat × PqxdhKemIndCca.MlKem768PublicKey) :
    M n KemSK source Auxiliary (RustM (Option Nat)) := do
  let worldOwner ← effect (.inr (.appendOwner keyId edPin .fresh))
  let owners ← get
  set (owners ++ [RegistrationNativeBeaconBirth.owner setup source prepared.pin prepared.credentials prepared.identity prepared.prekey born worldOwner])
  pure (.ok (some owners.length))

theorem append_program (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : Prepared source) :
    (appendBorn (n := n) setup source edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey : M n KemSK source Auxiliary _) =
    (do
      let born ← kem (.inr (.inl .create))
      register setup edPin keyId prepared born) := rfl

theorem create_program (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    (create (n := n) setup source edPin mlPin keyId : M n KemSK source Auxiliary _) = (do
      let prepared ← RegistrationNativeBeaconCreateProgram.program source edPin mlPin keyId
      match prepared with
      | .ok (some ready) =>
        let born ← kem (.inr (.inl .create))
        register setup edPin keyId ready born
      | .ok none => pure (.ok none)
      | .fail error => pure (.fail error)
      | .div => pure .div) := by
  unfold create
  rw [RegistrationNativeBeaconCreateProgram.prepare_program]
  apply bind_congr
  intro prepared
  cases prepared with
  | fail error => rfl
  | div => rfl
  | ok selected => cases selected with
    | none => rfl
    | some ready => exact append_program setup edPin keyId ready

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem register_run (implementation : QueryImpl (Trusted n KemSK) m)
    (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : Prepared source) (born : Nat × PqxdhKemIndCca.MlKem768PublicKey)
    (owners : State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((RegistrationNativePlatformGenericBundle.liftLegacy implementation (register setup edPin keyId prepared born)).run owners).run env = (do
      let worldOwner ← implementation (.inl (.inr (.appendOwner keyId edPin .fresh)))
      pure ((.ok (some owners.length), owners ++
        [RegistrationNativeBeaconBirth.owner setup source prepared.pin prepared.credentials prepared.identity prepared.prekey born worldOwner]), env)) := by
  change simulateQ implementation (((register setup edPin keyId prepared born).run owners).run env) = _
  simp only [register, effect, StateT.run_bind, StateT.run_lift, StateT.run_get,
    StateT.run_map, StateT.run_set, Functor.map_map, map_pure,
    simulateQ_map, simulateQ_spec_query, bind_pure_comp]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry.append_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry.append_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry.create_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry.create_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry.register_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCreateEntry.register_run
