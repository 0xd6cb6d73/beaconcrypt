-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceMaterial

/-! The freshly prepared reference is demanded before the real Beacon opening and installation. The known branch is its actual source World program, including every failed authentication/decode reply and the consumed kernel, with the private memo, pool and signing history retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativeOrdinaryFinishSourceMaterial (common service)
open RegistrationNativeKemReferenceWorld (withWorld)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

/-- Explicit installation and lifecycle effects use the current actual World and keep the full private frame. -/
theorem effects_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp (EnvEffects n) Value)
    (before : Private n KemSK) :
    (simulateQ (common setup wire route sign seed scalar)
      (simulateQ RegistrationHiddenInstall.effectLift work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [← QueryImpl.simulateQ_compose]
  have step : common (n := n) setup wire route sign seed scalar ∘ₛ RegistrationHiddenInstall.effectLift =
      fun query => withWorld (PqxdhRecordLiftWorld.effects query) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationHiddenInstall.effectLift, simulateQ_spec_query]
    rfl
  rw [step]
  exact RegistrationNativeKemReferenceWorld.world_program PqxdhRecordLiftWorld.effects work before

/-- The complete known-root branch runs the actual source opening and installs that branch's entire consumed kernel. -/
theorem known_stage (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner : Nat) (sender : U64)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) (before : Private n KemSK) :
    (simulateQ (common setup wire route sign seed scalar)
      (RegistrationNativePairedBeaconService.knownStage setup.source owner sender descriptor output)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects (do
          let result ← simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite)
            (RegistrationNativePairedBeaconService.program setup.source descriptor output)
          RegistrationNativePairedBeaconService.after owner sender (fun completed => .known completed.kernel) result)).run before.world := by
  simp only [RegistrationNativePairedBeaconService.knownStage, simulateQ_bind, StateT.run_bind,
    map_bind]
  rw [RegistrationNativeOrdinaryFinishSourceMaterial.raw_program]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨result, reached⟩
  exact effects_program setup wire route sign seed scalar _ { before with world := reached }

/-- The actual stored capability supplies its own freshly prepared root before any opening operation. -/
theorem admitted_known (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    {mlSource : RegistrationNativeMldsa.Source} (owner : RegistrationBeaconReferenceCompiler.SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput)
    (before : Private n KemSK) (prepared : before.extra.1 ready.reference = some root) :
    (simulateQ (service setup wire route sign seed scalar)
      (RegistrationNativePairedBeaconService.admitted setup.source owner.worldOwner
        owner.pin.binding.identity_key_id ready.descriptor ready.reference)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          (RegistrationBeaconReferenceNativeCompletion.knownEffects setup.source wire.frameWrite owner ready.descriptor root)).run
            before.world := by
  simp only [RegistrationNativePairedBeaconService.admitted, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind]
  rw [RegistrationNativeOrdinaryFinishSourceMaterial.demand_run]
  simp only [prepared, Option.map_some, pure_bind]
  rw [← QueryImpl.simulateQ_compose]
  have step : service (n := n) setup wire route sign seed scalar ∘ₛ
      RegistrationNativePairedServerService.publicCommon = common setup wire route sign seed scalar := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePairedServerService.publicCommon, simulateQ_spec_query]
    rfl
  rw [step]
  exact known_stage setup wire route sign seed scalar owner.worldOwner owner.pin.binding.identity_key_id
    ready.descriptor (PqxdhServerAuthKeySchedule.fromRoot setup.source root) before

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown.effects_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown.effects_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown.known_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown.known_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown.admitted_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown.admitted_known
