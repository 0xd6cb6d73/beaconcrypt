-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveMaterialService
/-! Actual selective demand and corrected Beacon source completion share their reached private material state and physical World. A successful selected descriptor uses its actual hidden reply and physical owner origin. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec effectLift)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSelectiveHiddenInterpreter (State)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {I KemSK ProviderState Auxiliary Reader Response Secret A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def effects : QueryImpl (EnvEffects n) (StateT (State n KemSK ProviderState) (OracleComp (WorldSpec n))) :=
  fun query => StateT.lift (effectLift query)

/-- Every actual Env-only continuation keeps the reached opaque material/provider state literally. -/
theorem effects_source (work : OracleComp (EnvEffects n) A) (before : State n KemSK ProviderState) :
    (simulateQ effects work).run before = (fun value => (value,before)) <$> simulateQ effectLift work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,effects,StateT.run_bind,StateT.run_lift,
      bind_pure_comp,bind_map_left,map_bind,ih]

/-- The complete actual chosen source continuation retains all private demand state while running its same source World program. -/
theorem chosen_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (env : EnvState Auxiliary) (before : State n KemSK ProviderState) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer effects owner ready choice).run current).run env).run before =
      (fun value => (value,before)) <$> (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer effectLift owner ready choice).run current).run env) :=
  effects_source _ before

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def demand (message : RegistrationNativeRelatedFamily.Message) :
    StateT (State n KemSK ProviderState) (OracleComp (WorldSpec n)) (Option (RegistrationNativePairedChoice.Choice n)) :=
  RegistrationNativePlatformSelectiveMaterialService.handler setup wire sign seed scalar candidate provider (.inl message)

/-- The actual selected demand followed by all source opening and settlement effects installs a physical hidden origin on every returned application. -/
theorem complete_hidden (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (selected : ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some bytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)
    (env : EnvState Auxiliary) (before : State n KemSK ProviderState)
    (shell : CborRecordWorldClient.Shell) (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : (((((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × State n KemSK ProviderState) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite effects
        (demand setup wire sign seed scalar candidate provider) owner ready).run current).run env).run before) shell world secret))
    (application : Pqxdh.Bytes) (successful : result.1.1.1.1.1.1 = .ok (some application)) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner.worldOwner) = some slot := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,asked,continued⟩ := supported
  cases chosen : middle.1.1.1.1 with
  | none =>
    simp only [chosen,RegistrationNativePlatformBeaconMaterialFrontend.abort,seqRight_eq_bind,effects,
      StateT.run_lift,StateT.run_map,bind_pure_comp,Functor.map_map,
      RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at continued
    obtain ⟨ended,_called,equal⟩ := continued
    cases equal
    cases successful
  | some choice =>
    obtain ⟨reference,hidden⟩ := RegistrationNativePlatformSelectiveMaterialService.demand_hidden
      setup wire sign seed scalar candidate provider service codec route ready.reference selected before shell world secret middle asked choice chosen
    subst choice
    simp only [chosen] at continued
    rw [chosen_source,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at continued
    obtain ⟨finished,actual,equal⟩ := continued
    cases equal
    exact ⟨reference.slot,RegistrationNativePlatformRecordHiddenBeaconMaterial.chosen_hidden service codec route setup.source wire.frameWrite
      owner current ready reference env middle.1.1.2 middle.1.2 middle.2 finished actual application successful⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial.effects_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial.chosen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial.chosen_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial.complete_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconMaterial.complete_hidden
