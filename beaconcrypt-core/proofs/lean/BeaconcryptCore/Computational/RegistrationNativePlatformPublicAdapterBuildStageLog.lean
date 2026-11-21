-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStages
/-! A pure observation injection embeds the same Builder operation log into the canonical source event list without filtering or reconstructing any earlier callback markers. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded)
abbrev Spec := RegistrationNativePlatformPublicAdapterBuildStages.Spec
variable [primitive : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {Reader Response : Type}
variable {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT P ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Base" => StateT P ProbComp

variable {Log : Type}

noncomputable def physical (note : Stage → Log) (initial : registration.ServerInitialKdf) :
    StateT (Backend n KemSK × List Log) Base (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))) :=
  simulateQ (recorded
    (RegistrationNativePlatformPublicAdapterBuildPublication.handler (n:=n) coins setup codec view failure allocation helper erased sign writer)
    (fun query reply => (RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
    (RegistrationNativePlatformPublicAdapterBuildStages.code initial)

theorem source (note : Stage → Log) (initial : registration.ServerInitialKdf) (before : Native × List Log) :
    Prod.map id (Prod.map backend id) <$>
      (simulateQ (recorded (RegistrationNativePlatformPublicAdapterBuildStages.native coins setup codec view failure allocation helper erased sign writer)
        (fun query reply => (RegistrationNativePlatformPublicAdapterBuildStages.observation query reply).map note))
        (RegistrationNativePlatformPublicAdapterBuildStages.code initial)).run before =
      (physical coins setup codec view failure allocation helper erased sign writer note initial).run (backend before.1,before.2) := by
  apply RegistrationNativePlatformPublicAdapterSourceTrace.source
  intro query current
  exact RegistrationNativePlatformPublicAdapterBuildPublication.query_source coins setup codec view failure allocation helper erased sign writer query current

theorem erase (note : Stage → Log) (initial : registration.ServerInitialKdf) (before : Backend n KemSK × List Log) :
    Prod.map id Prod.fst <$> (physical coins setup codec view failure allocation helper erased sign writer note initial).run before =
      (RegistrationNativePlatformPublicAdapterBuildPublication.beforeInstall coins setup codec view failure allocation helper erased sign writer initial).run before.1 := by
  rw [physical,RegistrationNativePlatformPublicAdapterSourceTrace.erase,RegistrationNativePlatformPublicAdapterBuildStages.interpret]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStageLog.erase
