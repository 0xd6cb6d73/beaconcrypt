-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenStage
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
/-! Successful actual Beacon material completion keeps the physical hidden slot installed by the same native assigned-ID callback. Source raw opening and terminal owner settlement retain all actual failure and World states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift Slot)
open PqxdhRecordLiftProtocol (Control)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {Auxiliary Reader Response Secret : Type} {source : RegistrationNativeMldsa.Source}

/-- The actual hidden chosen program uses the same source opening and actual corrected installation before owner settlement. -/
theorem hidden_chosen {m : Type → Type} [Monad m] [LawfulMonad m]
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (environment : QueryImpl (EnvEffects n) m) (owner : SelectedOwner source)
    (ready : RegistrationBeaconReferenceRoot.Ready) (reference : RegistrationNativePairedDemand.Reference n) :
    RegistrationNativePlatformBeaconMaterialFrontend.chosen (Auxiliary := Auxiliary) crypto writer environment owner ready (.hidden reference) = (do
      let _ ← StateT.lift (RegistrationBeaconMaterialRead.charge .initialKdf)
      let _ ← if RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
        (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
        then StateT.lift (RegistrationBeaconMaterialRead.charge .ratchetKdf) else pure ()
      let opened ← StateT.lift (simulateQ (RegistrationBeaconChargedSource.primitive
        (RegistrationBeaconMaterialRead.read environment crypto writer))
        (RegistrationBeaconSeed.program crypto ready.descriptor
          (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBeaconSeed.fixedSeed)))
      RegistrationNativePlatformBeaconMaterialFrontend.installed environment owner (fun _ => .hidden reference.slot) opened) := by
  apply StateT.ext
  intro current
  apply StateT.ext
  intro before
  unfold RegistrationNativePlatformBeaconMaterialFrontend.chosen RegistrationNativePlatformBeaconMaterialFrontend.program
    RegistrationNativePlatformPairedBeaconOwner.publicBranch RegistrationNativePlatformPairedBeaconOwner.publicHidden
    RegistrationNativePlatformPairedBeaconOwner.hiddenStage
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals simp only [valid,ite_true,ite_false,StateT.run_bind,StateT.run_lift,
    RegistrationBeaconMaterialRead.charge,StateT.run_modify,pure_bind,simulateQ_bind,bind_pure_comp,bind_map_left]
  all_goals simp only [RegistrationBeaconMaterialRead.primitive_program (n := n) (Auxiliary := Auxiliary) environment crypto writer]
  all_goals simp only [bind_assoc]
  all_goals apply bind_congr
  all_goals rintro ⟨opened,reached⟩
  all_goals
    have transported := RegistrationNativePlatformBeaconMaterialFrontend.installed_run environment owner current
      (fun _ => .hidden reference.slot) opened reached
    simpa only [RegistrationNativePlatformBeaconMaterialFrontend.installed,StateT.run_bind,StateT.run_lift,
      bind_pure_comp,simulateQ_bind,bind_map_left] using transported

variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A returned application can arise only from successful installation; its final physical control is that insertion's control. -/
theorem after_success (owner current : SelectedOwner source) (published : RustM RegistrationNativePairedBeaconService.Result)
    (env : EnvState Auxiliary) (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : ((((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (((RegistrationNativePlatformBeaconMaterialFrontend.after effectLift owner published).run current).run env) shell world secret))
    (application : Pqxdh.Bytes) (successful : result.1.1.1.1.1 = .ok (some application)) :
    (∃ completed, published = .ok (.Ok completed)) ∧ result.1.2 = world := by
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind,StateT.run_lift,StateT.run_map,bind_pure_comp,Functor.map_map,
      RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at supported
    obtain ⟨reached,_called,equal⟩ := supported
    cases equal
    cases successful
  | ok outcome => cases outcome with
    | Err previous =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind,StateT.run_lift,StateT.run_map,bind_pure_comp,Functor.map_map,
        RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at supported
      obtain ⟨reached,_called,equal⟩ := supported
      cases equal
      cases successful
    | Ok completed =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after,StateT.run_bind,StateT.run_modify,
        pure_bind,StateT.run_pure,CborRawRecordOriginFlatten.interpret_pure,mem_support_pure_iff] at supported
      cases supported
      exact ⟨⟨completed,rfl⟩,rfl⟩

private theorem paired_after_run (owner : Nat) (slot : Slot n) (opened : RustM RegistrationBeaconRecordExecutor.Result)
    (before : EnvState Auxiliary) :
    ((RegistrationNativePlatformPairedBeaconService.after
      (fun query => StateT.lift (effectLift query)) owner (fun _ => .hidden slot) opened).run before) =
      (fun reply => (reply,before)) <$> RegistrationNativePlatformPairedBeaconService.after effectLift owner (fun _ => .hidden slot) opened := by
  cases opened with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

/-- Actual successful native insertion followed by owner settlement keeps the same hidden physical origin. -/
theorem installed_hidden (owner current : SelectedOwner source) (slot : Slot n)
    (opened : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary)
    (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : ((((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (((RegistrationNativePlatformBeaconMaterialFrontend.installed effectLift owner (fun _ => .hidden slot) opened).run current).run env) shell world secret))
    (application : Pqxdh.Bytes) (successful : result.1.1.1.1.1 = .ok (some application)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner.worldOwner) = some slot := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.installed,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left] at supported
  rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,inserted,settled⟩ := supported
  rw [paired_after_run,RegistrationNativeHiddenEnvironmentWorld.interpret_map,support_map] at inserted
  obtain ⟨physical,actual,equal⟩ := inserted
  cases equal
  have finished := after_success service codec route owner current physical.1.1.1 env
    physical.1.1.2 physical.1.2 physical.2 result settled application successful
  obtain ⟨completed,published⟩ := finished.1
  have hidden := RegistrationNativePlatformRecordHiddenPublication.beacon service codec route owner.worldOwner slot opened completed
    shell world secret physical actual published
  rw [finished.2]
  exact hidden

/-- The complete actual hidden material program attaches the same returned application to its physical owner slot. -/
theorem chosen_hidden (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (reference : RegistrationNativePairedDemand.Reference n) (env : EnvState Auxiliary)
    (shell : CborRecordWorldClient.Shell) (world : Control n) (secret : Secret)
    (result : ((((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary) × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer effectLift owner ready (.hidden reference)).run current).run env) shell world secret))
    (application : Pqxdh.Bytes) (successful : result.1.1.1.1.1 = .ok (some application)) :
    PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner.worldOwner) = some reference.slot := by
  rw [hidden_chosen] at supported
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals
    simp only [valid,ite_true,ite_false,StateT.run_bind,StateT.run_lift,RegistrationBeaconMaterialRead.charge,
      StateT.run_modify,pure_bind,bind_pure_comp,bind_map_left] at supported
    rw [CborRawRecordOriginFlatten.interpret_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,_opened,completed⟩ := supported
    exact installed_hidden service codec route owner current reference.slot middle.1.1.1.1 middle.1.1.1.2
      middle.1.1.2 middle.1.2 middle.2 result completed application successful

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.hidden_chosen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.hidden_chosen
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.after_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.after_success

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.installed_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.installed_hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.chosen_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordHiddenBeaconMaterial.chosen_hidden
