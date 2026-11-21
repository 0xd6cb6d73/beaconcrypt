-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSuffix

/-! Native and indexed-identity constructors share literal pure full-pin selection. This shared public effect program retains every RustM pin outcome before either indexed-identity/prekey suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCommon
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeIdentityFrontend (Ambient Trusted)
variable {n : Nat} {KemSK Value : Type}

abbrev Base (_ : RegistrationNativeMldsa.Source) := session.ServerAuthenticationPin

noncomputable def program (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : OracleComp (EnvEffects n) (RustM (Option (Base source))) :=
  match registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok pin => pure (.ok (some pin))

def afterNative {source : RegistrationNativeMldsa.Source} (earlier : RustM (Option (Base source))) :
    OracleComp (Ambient n KemSK) (RustM (Option (RegistrationNativeBeaconFrontend.Prepared source))) :=
  match earlier with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok none => pure (.ok none)
  | .ok (some prepared) => RegistrationNativeIdentitySourceSuffix.native (source := source) prepared

def afterExposed {source : RegistrationNativeMldsa.Source} (earlier : RustM (Option (Base source))) :
    OracleComp (Trusted n KemSK) (RustM (Option (RegistrationNativeIdentityFrontend.Prepared source))) :=
  match earlier with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok none => pure (.ok none)
  | .ok (some prepared) => RegistrationNativeIdentitySourceSuffix.exposed (source := source) prepared

noncomputable def nativeProgram (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    OracleComp (Ambient n KemSK) (RustM (Option (RegistrationNativeBeaconFrontend.Prepared source))) :=
  simulateQ RegistrationBeaconReferenceNativeRecord.environment (program source edPin mlPin keyId) >>= afterNative

noncomputable def exposedProgram (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    OracleComp (Trusted n KemSK) (RustM (Option (RegistrationNativeIdentityFrontend.Prepared source))) :=
  simulateQ RegistrationNativeIdentityFrontend.ambientLift
    (simulateQ RegistrationBeaconReferenceNativeRecord.environment (program source edPin mlPin keyId)) >>= afterExposed

private theorem sample_forward (work : ProbComp Value) :
    simulateQ RegistrationNativeIdentityFrontend.ambientLift
      (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (simulateQ (RegistrationWorldCoinCompiler.envCoin (n := n)) work)) =
      simulateQ (RegistrationNativeIdentitySourcePrepare.coins (n := n) (KemSK := KemSK)) work := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun implementation => simulateQ implementation work)
  funext query
  simp only [QueryImpl.apply_compose, RegistrationWorldCoinCompiler.envCoin,
    RegistrationBeaconReferenceNativeRecord.environment, RegistrationNativeIdentityFrontend.ambientLift,
    simulateQ_spec_query, RegistrationNativeIdentitySourcePrepare.coins]

/-- The complete actual public preparation AST factors through the literal shared pure-pin prefix. -/
theorem exposed_factor (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeIdentitySourcePrepare.program (n := n) (KemSK := KemSK) source edPin mlPin keyId =
      exposedProgram source edPin mlPin keyId := by
  unfold RegistrationNativeIdentitySourcePrepare.program exposedProgram program
  cases initial : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => simp only [simulateQ_pure, afterExposed, pure_bind]
  | ok pin =>
      simp only [simulateQ_pure, afterExposed, pure_bind, RegistrationNativeIdentitySourceSuffix.exposed,
        RegistrationNativeIdentitySourceSuffix.newSample, RegistrationNativeIdentitySourceSuffix.oldSample, sample_forward]
      rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCommon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCommon.exposed_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCommon.exposed_factor
