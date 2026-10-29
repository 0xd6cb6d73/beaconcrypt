-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHiddenStage
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenDemandWorld

/-! The native current-environment material service separates only its two mutable state coordinates: demand runs the actual selective private callback, and Common publication runs the actual native environment compiler. World effects remain shared and unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialService
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec effectLift)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Value Next : Type} {base : OracleSpec ι}

abbrev Local (n : Nat) (Auxiliary KemSK ProviderState : Type) :=
  EnvState Auxiliary × RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState

def onEnv (work : StateT (EnvState Auxiliary) (OracleComp (WorldSpec n)) Value) :
    StateT (Local n Auxiliary KemSK ProviderState) (OracleComp (WorldSpec n)) Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

def onKeys (work : RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState Value) :
    StateT (Local n Auxiliary KemSK ProviderState) (OracleComp (WorldSpec n)) Value := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$> work.run before.2

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl

private theorem env_pure (value : Value) : onEnv (KemSK := KemSK) (ProviderState := ProviderState)
    (pure value : StateT (EnvState Auxiliary) (OracleComp (WorldSpec n)) Value) = pure value := by
  apply StateT.ext
  intro before
  simp only [onEnv, StateT.run, pure_apply, map_pure]

private theorem env_bind (work : StateT (EnvState Auxiliary) (OracleComp (WorldSpec n)) Value)
    (next : Value → StateT (EnvState Auxiliary) (OracleComp (WorldSpec n)) Next) :
    onEnv (KemSK := KemSK) (ProviderState := ProviderState) (work >>= next) =
      (onEnv work >>= fun value => onEnv (next value)) := by
  apply StateT.ext
  intro before
  simp only [onEnv, StateT.run, bind_apply, map_bind, bind_map_left]

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n)
      (StateT (Local n Auxiliary KemSK ProviderState) (OracleComp (WorldSpec n)))
  | .inl message => onKeys (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider
      (.inl (.inr (.inl (.inl message)))))
  | .inr query => onEnv (RegistrationNativeCommonCompiler.common effectLift setup.source wire.frameWrite sign query)

/-- The actual Common component preserves the private material coordinate while retaining the complete current environment. -/
theorem common_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (before : Local n Auxiliary KemSK ProviderState) :
    (simulateQ (handler (Auxiliary := Auxiliary) setup wire sign seed scalar candidate provider)
      (simulateQ RegistrationNativePairedServerService.publicCommon work)).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (simulateQ (RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) effectLift setup.source wire.frameWrite sign) work).run before.1 := by
  have source : simulateQ (handler (Auxiliary := Auxiliary) setup wire sign seed scalar candidate provider)
        (simulateQ RegistrationNativePairedServerService.publicCommon work) =
      onEnv (simulateQ (RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) effectLift setup.source wire.frameWrite sign) work) := by
    induction work using OracleComp.inductionOn with
    | pure value => simp only [simulateQ_pure, env_pure]
    | query_bind query next ih =>
        simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePairedServerService.publicCommon,
          handler, env_bind]
        congr 1
        funext reply
        exact ih reply
  rw [source]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialService.common_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialService.common_program
