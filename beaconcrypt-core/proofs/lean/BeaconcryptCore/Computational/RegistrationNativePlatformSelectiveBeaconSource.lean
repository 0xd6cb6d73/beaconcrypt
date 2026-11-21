-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
/-! The actual source material completion is natural in its demand and World dictionary. Its selective interpretation retains every reached private material state and physical result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec effectLift)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {I KemSK ProviderState Auxiliary Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

/-- The literal source completion forwards exactly its own demand and source World effects into any lawful shared monad. -/
theorem natural {m : Type → Type} [Monad m] [LawfulMonad m]
    (implementation : QueryImpl (Spec n KemSK) m)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    simulateQ implementation
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer
        (implementation ∘ₛ RegistrationBeaconReferenceCompiler.effect)
        (fun message => implementation (.inr (.inl (.inl message)))) owner ready).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left,simulateQ_bind,RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    simulateQ_spec_query]
  apply bind_congr
  intro choice
  cases choice with
  | none =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort,seqRight_eq_bind,StateT.run_lift,StateT.run_map,
      bind_pure_comp,Functor.map_map,simulateQ_map,QueryImpl.apply_compose]
  | some choice =>
    change simulateQ implementation (simulateQ RegistrationBeaconReferenceCompiler.effect _) = _
    rw [← QueryImpl.simulateQ_compose]
    rfl

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
local notation "backend" => RegistrationNativeSelectiveHiddenInterpreter.handler (n := n) setup wire sign seed scalar candidate provider
local notation "localImpl" => backend ∘ₛ RegistrationNativePublicFrontend.liftLocal (n := n) false

/-- The actual native local completion closes through the same selective material demand and private-preserving source effects. -/
theorem complete_source (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    simulateQ localImpl
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite
        (RegistrationNativePlatformSelectiveBeaconMaterial.effects (KemSK := KemSK) (ProviderState := ProviderState))
        (RegistrationNativePlatformSelectiveBeaconMaterial.demand setup wire sign seed scalar candidate provider) owner ready).run current).run env) := by
  rw [natural]
  have environment : localImpl ∘ₛ RegistrationBeaconReferenceCompiler.effect =
      RegistrationNativePlatformSelectiveBeaconMaterial.effects (n := n) (KemSK := KemSK) (ProviderState := ProviderState) := by
    funext query
    apply StateT.ext
    intro before
    simp only [QueryImpl.apply_compose,RegistrationBeaconReferenceCompiler.effect,RegistrationNativePublicFrontend.liftLocal,
      simulateQ_spec_query,RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.effect,StateT.run,
      RegistrationNativePlatformSelectiveBeaconMaterial.effects]
    rfl
  have demanded : (fun message => localImpl (.inr (.inl (.inl message)))) =
      RegistrationNativePlatformSelectiveBeaconMaterial.demand setup wire sign seed scalar candidate provider := by
    funext message
    simp only [QueryImpl.apply_compose,RegistrationNativePublicFrontend.liftLocal,simulateQ_spec_query,
      RegistrationNativePlatformSelectiveBeaconMaterial.demand,RegistrationNativePlatformSelectiveMaterialService.handler]
  rw [environment,demanded]

/-- Every supported selected application in the literal native local tree has its physical hidden origin at that same final control. -/
theorem complete_hidden
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (env : EnvState Auxiliary) (before : State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : (((((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State n KemSK ProviderState) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((simulateQ backend (simulateQ (RegistrationNativePublicFrontend.liftLocal false)
        (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
          RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env))).run before) shell world secret))
    (application : Pqxdh.Bytes) (successful : result.1.1.1.1.1.1 = .ok (some application)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner.worldOwner) = some slot := by
  rw [← QueryImpl.simulateQ_compose,complete_source] at supported
  exact RegistrationNativePlatformSelectiveBeaconMaterial.complete_hidden setup wire sign seed scalar candidate provider service codec route
    owner current ready selected env before shell world secret result supported application successful

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource.natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource.natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource.complete_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource.complete_hidden
