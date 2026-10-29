-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCommon

/-! The original seed-bearing constructor preparation has the same public ML/pin prefix and literal ordinary seed/prekey suffix query program. This is an operational source factor, including every optional native refusal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram
open RegistrationNativeIdentityFrontend (Ambient)
variable {n : Nat} {KemSK Value Result : Type}

def lift {source : RegistrationNativeMldsa.Source} (work : OracleComp (Ambient n KemSK) Value) :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value := StateT.lift (StateT.lift work)

private theorem lift_bind {source : RegistrationNativeMldsa.Source}
    (work : OracleComp (Ambient n KemSK) Value) (next : Value → OracleComp (Ambient n KemSK) Result) :
    lift (source := source) (work >>= next) = (lift work >>= fun value => lift (next value)) := by
  funext owners env
  simp only [lift, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure, bind_assoc, pure_bind]

private theorem lift_pure {source : RegistrationNativeMldsa.Source} (value : Value) :
    lift (n := n) (KemSK := KemSK) (source := source) (pure value) = pure value := by
  funext owners env
  simp only [lift, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure, pure_bind]

private theorem sample_lift {source : RegistrationNativeMldsa.Source} (work : ProbComp Value) :
    lift (source := source) (simulateQ RegistrationBeaconReferenceNativeRecord.environment
      (simulateQ (RegistrationWorldCoinCompiler.envCoin (n := n)) work)) =
      RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) work :=
  (RegistrationNativeScalarSource.sample_effects work).symm

/-- Literal original preparation factors into the same common prefix and ordinary seed/prekey source suffix used by the indexed identity realization. -/
theorem prepare_program (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) source edPin mlPin keyId =
      lift (RegistrationNativeIdentitySourceCommon.nativeProgram source edPin mlPin keyId) := by
  simp only [RegistrationNativeBeaconFrontend.prepare, RegistrationNativeIdentitySourceCommon.nativeProgram,
    RegistrationNativeIdentitySourceCommon.program, simulateQ_bind, lift_bind, sample_lift, bind_assoc]
  apply congrArg (fun continuation =>
    (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) (RegistrationNativeMldsa.generate source) >>= continuation))
  funext generated
  cases generated with
  | none => simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, lift_pure]
  | some credentials =>
      cases initial : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error => simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, lift_pure]
      | div => simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, lift_pure]
      | ok pending =>
          cases requested : pending.request with
          | fail error => simp only [requested, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, simulateQ_pure, lift_pure]
          | div => simp only [requested, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, simulateQ_pure, lift_pure]
          | ok request =>
              simp only [requested, simulateQ_bind, simulateQ_spec_query, lift_bind, RegistrationBeaconReferenceNativeRecord.environment, bind_assoc]
              apply congrArg (fun continuation =>
                (RegistrationNativeBeaconFrontend.hash (n := n) (KemSK := KemSK) (mldsaSource := source)
                  (Auxiliary := RegistrationServerRoleBackend.State) request >>= continuation))
              funext digest
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error => simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, lift_pure]
              | div => simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, lift_pure]
              | ok reply => cases reply with
                | none => simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind, lift_pure]
                | some pin =>
                    simp only [simulateQ_pure, RegistrationNativeIdentitySourceCommon.afterNative, pure_bind,
                      RegistrationNativeIdentitySourceSuffix.native, RegistrationNativeIdentitySourceSuffix.oldSample,
                      lift_bind, lift_pure, sample_lift]

/-- The original preparation changes neither the current source roster nor its local mutable environment while executing that query program. -/
theorem prepare_run (source : RegistrationNativeMldsa.Source) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    ((RegistrationNativeBeaconFrontend.prepare (n := n) (KemSK := KemSK) source edPin mlPin keyId).run owners).run env =
      (fun reply => ((reply, owners), env)) <$> RegistrationNativeIdentitySourceCommon.nativeProgram source edPin mlPin keyId := by
  rw [prepare_program]
  simp only [lift, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram.prepare_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram.prepare_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceNativeProgram.prepare_run
