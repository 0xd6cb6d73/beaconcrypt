-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundlePrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCutProbability
/-! The whole original prefix/resumption coupling has the SAME normalized journal image as the actual marked prefix followed by its plain source suffix. Original private failure witnesses are retained only in analysis events. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeObservedStageTrace (mapCall)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop)
open RegistrationNativeIdentityCensorBundlePrefix (Cut stop resume)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)

local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "signed" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint actual
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "WholeState" => Whole n KemSK Platform mlSource
local notation "PlainState" => RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform mlSource
local notation "normalized" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder
local notation "plain" => (fun query => RegistrationNativePlatformIdentityCtxMain.interpret setup.joint (normalized query))
local notation "canonical" => RegistrationNativeIdentityCensorCanonicalSource.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder
local notation "project" => RegistrationNativeIdentityCensorActualHashSource.project
local notation "originalProject" => RegistrationNativeIdentityCensorNormalizedJournal.project placeholder


local notation "originalMap" => RegistrationNativeIdentityCensorIssuedImageProbability.originalMap placeholder
local notation "marked" => RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder true normalized

noncomputable def originalPrefix (work : OracleComp TypedSpec A) (before : WholeState) :=
  (simulateQ (RegistrationNativeStageTrace.handler signed) (stop position work 0)).run (before,[])

noncomputable def markedPrefix (work : OracleComp TypedSpec A) (before : WholeState) :=
  (simulateQ (RegistrationNativeObservedStageTrace.handler project marked) (stop position work 0)).run
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
      ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before),[])

omit primitive setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder in
def markedMap (result : Cut A × (FullState × List (Call TypedSpec PlainState))) :
    Cut A × (PlainState × List (Call TypedSpec PlainState)) :=
  (result.1,(project result.2.1,result.2.2))

/-- The actual marked before-b prefix and original signed before-b prefix share the complete SAME normalized state and chronological journal distribution. -/
theorem prefix_source (work : OracleComp TypedSpec A) (before : WholeState) :
    originalMap <$> originalPrefix setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      position work before =
    markedMap <$> markedPrefix setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before := by
  have ordinary := RegistrationNativeIdentityCensorNormalizedJournal.full_source setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve placeholder (stop position work 0) before []
  have markedSource := RegistrationNativeIdentityCensorBundlePrefix.observed_source setup.joint selected position placeholder true normalized work 0
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
      ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before)) []
    (Nat.zero_le position) rfl rfl
  change (Prod.map id (fun current => (originalProject current.1,current.2.map (mapCall originalProject)))) <$>
      (simulateQ (RegistrationNativeStageTrace.handler signed) (stop position work 0)).run (before,[]) =
    Prod.map id (Prod.map project id) <$>
      (simulateQ (RegistrationNativeObservedStageTrace.handler project marked) (stop position work 0)).run
        (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
          ({knownInputs:=before.2.2.2} : RegistrationNativeIdentityCensorCompiler.Mode) (drop before),[])
  exact ordinary.trans markedSource.symm


noncomputable def markedPlainJoint (work : OracleComp TypedSpec A) (before : WholeState) := do
  let cut ← markedPrefix setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder work before
  let final ← (simulateQ (RegistrationNativeStageTrace.handler plain) (resume cut.1)).run (project cut.2.1,cut.2.2)
  pure (cut,final)

omit primitive setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position in
def originalJointMap (result :
    (Cut A × (WholeState × List (Call TypedSpec WholeState))) ×
      (A × (WholeState × List (Call TypedSpec WholeState)))) :=
  (originalMap result.1,originalMap result.2)

omit primitive setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder in
def markedJointMap (result :
    (Cut A × (FullState × List (Call TypedSpec PlainState))) ×
      (A × (PlainState × List (Call TypedSpec PlainState)))) :=
  (markedMap result.1,result.2)

/-- Prefix and full original suffix remain joint across the actual source equation. No original failure or private snapshot chooses an executable branch. -/
theorem joint_source (work : OracleComp TypedSpec A) (before : WholeState) :
    originalJointMap placeholder <$> RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before =
      markedJointMap <$> markedPlainJoint setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position placeholder work before := by
  have prefixLaw := congrArg (fun distribution => do
    let cut ← distribution
    let final ← (simulateQ (RegistrationNativeStageTrace.handler plain) (resume cut.1)).run cut.2
    pure (cut,final))
    (prefix_source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before)
  calc
    _ = (do
      let cut ← originalPrefix setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        position work before
      let final ← (simulateQ (RegistrationNativeStageTrace.handler plain) (resume cut.1)).run ((originalMap cut).2)
      pure (originalMap cut,final)) := by
        simp only [RegistrationNativeIdentityCensorIssuedCutProbability.coupled,originalPrefix,map_bind,map_pure]
        apply bind_congr
        intro cut
        have suffix := congrArg (Functor.map (fun final => (originalMap cut,final)))
          (RegistrationNativeIdentityCensorNormalizedJournal.full_source setup checks wire route representation created credential keys failure allocation
            reserveRegistration reservePeer reserveFrame erased helper reserve placeholder (resume cut.1) cut.2.1 cut.2.2)
        simpa only [bind_pure_comp,Functor.map_map,originalJointMap,RegistrationNativeIdentityCensorIssuedImageProbability.originalMap,Prod.map_def,id_eq] using suffix
    _ = _ := by
      simpa only [bind_map_left,markedPlainJoint,map_bind,map_pure,bind_pure_comp,markedJointMap,Functor.map_map,RegistrationNativeIdentityCensorIssuedImageProbability.originalMap,markedMap] using prefixLaw

/-- Original issued cutoff events are bounded by their exact same-run source image with the actual full marked-prefix state retained. -/
theorem bound (work : OracleComp TypedSpec A) (before : WholeState)
    (bad : (Cut A × (WholeState × List (Call TypedSpec WholeState))) ×
      (A × (WholeState × List (Call TypedSpec WholeState))) → Prop) :
    Pr{let result ← (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before)}[bad result] ≤
    Pr{let result ← (markedPlainJoint setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before)}[
        ∃ original∈support (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before),bad original ∧
          originalJointMap placeholder original=markedJointMap result] := by
  have same := congrArg (fun distribution => Pr{let result ← distribution}[
    ∃ original∈support (RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint actual position work before),bad original ∧
      originalJointMap placeholder original=result])
    (joint_source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before)
  simp only [prEvent_map] at same
  refine le_trans ?_ same.le
  apply prEvent_mono_of_support
  intro result reached failed
  exact ⟨result,reached,failed,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage.prefix_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage.joint_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage.joint_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedPrefixImage.bound
