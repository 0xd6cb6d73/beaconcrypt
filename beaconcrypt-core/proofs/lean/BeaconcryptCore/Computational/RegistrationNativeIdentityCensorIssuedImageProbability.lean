-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCanonicalSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedJournal
/-! Original private journal events transport through an exact source-image coupling to the same canonical source suffix. The original witness remains private analysis state, never an executable selector or reduction capture. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeObservedStageTrace (mapCall)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
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

omit primitive in
private theorem trace_prefix {X V : Type} (implementation : QueryImpl TypedSpec (StateT X ProbComp))
    (work : OracleComp TypedSpec V) (before : X) (leading : List (Call TypedSpec X)) :
    (fun result => (result.1,(result.2.1,leading++result.2.2))) <$>
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,[]) =
      (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (before,leading) := by
  have mapped := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RegistrationNativeStageTrace.handler implementation) (RegistrationNativeStageTrace.handler implementation)
    (fun current => (current.1,leading++current.2)) (by
      intro query current
      simp only [RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,Prod.map_def,id_eq,List.append_assoc]) work (before,[])
  simpa only [Prod.map_def,id_eq,List.append_nil] using mapped

omit primitive setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position in
def originalMap (result : A × (WholeState × List (Call TypedSpec WholeState))) : A × (PlainState × List (Call TypedSpec PlainState)) :=
  (result.1,(originalProject result.2.1,result.2.2.map (mapCall originalProject)))

omit primitive setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position in
def canonicalMap (leading : List (Call TypedSpec WholeState)) (result : A × (FullState × List (Call TypedSpec FullState))) :
    A × (PlainState × List (Call TypedSpec PlainState)) :=
  (result.1,(project result.2.1,leading.map (mapCall originalProject)++result.2.2.map (mapCall project)))

omit primitive setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder in
def canonicalImage (leading : List (Call TypedSpec PlainState)) (result : A × (FullState × List (Call TypedSpec FullState))) :
    A × (PlainState × List (Call TypedSpec PlainState)) :=
  (result.1,(project result.2.1,leading++result.2.2.map (mapCall project)))

/-- Any actual reached canonical source suffix restores its exact plain source journal marginal, retaining a given original observed leading journal. -/
theorem canonical_source (work : OracleComp TypedSpec A) (before : FullState)
    (leading : List (Call TypedSpec PlainState)) (seed : PqxdhJointIdentity.IdentitySeed)
    (ready : RegistrationNativeIdentityCensorCanonicalSource.Ready selected seed before) :
    canonicalImage leading <$>
      (simulateQ (RegistrationNativeStageTrace.handler canonical) work).run (before,[]) =
    (simulateQ (RegistrationNativeStageTrace.handler plain) work).run (project before,leading) := by
  have full := RegistrationNativeObservedStageTrace.full_project project canonical work (before,[])
  have observed := congrArg (Functor.map (Prod.map id (Prod.map project id))) full
  simp only [List.map_nil] at observed
  rw [RegistrationNativeIdentityCensorCanonicalSource.observed_source setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder work seed before [] ready] at observed
  rw [←trace_prefix plain work (project before) leading,←observed]
  simp only [Functor.map_map]
  rfl

/-- The full original signed suffix and actual canonical suffix have exactly the same normalized private journal image, retaining original replies and every live source/P field. -/
theorem source (work : OracleComp TypedSpec A) (before : WholeState) (leading : List (Call TypedSpec WholeState))
    (canonicalBefore : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (ready : RegistrationNativeIdentityCensorCanonicalSource.Ready selected seed canonicalBefore)
    (sameBefore : project canonicalBefore=originalProject before) :
    originalMap placeholder <$>
      (simulateQ (RegistrationNativeStageTrace.handler signed) work).run (before,leading) =
    canonicalMap placeholder leading <$>
      (simulateQ (RegistrationNativeStageTrace.handler canonical) work).run (canonicalBefore,[]) := by
  rw [show originalMap placeholder = Prod.map id (fun current => (originalProject current.1,current.2.map (mapCall originalProject))) from rfl,
    RegistrationNativeIdentityCensorNormalizedJournal.full_source setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve placeholder work before leading]
  rw [←sameBefore]
  have full := RegistrationNativeObservedStageTrace.full_project project canonical work (canonicalBefore,[])
  have observed := congrArg (Functor.map (Prod.map id (Prod.map project id))) full
  simp only [List.map_nil] at observed
  rw [RegistrationNativeIdentityCensorCanonicalSource.observed_source setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder work seed canonicalBefore [] ready] at observed
  have prefixLaw := trace_prefix plain work (project canonicalBefore) (leading.map (mapCall originalProject))
  rw [←prefixLaw,←observed]
  simp only [Functor.map_map]
  rfl

/-- Any event of the original same-run suffix is bounded by its exact canonical journal image. The retained original witness is proof state; no private event or witness chooses an executable stop. -/
theorem bound (work : OracleComp TypedSpec A) (before : WholeState) (leading : List (Call TypedSpec WholeState))
    (canonicalBefore : FullState) (seed : PqxdhJointIdentity.IdentitySeed)
    (ready : RegistrationNativeIdentityCensorCanonicalSource.Ready selected seed canonicalBefore)
    (sameBefore : project canonicalBefore=originalProject before)
    (bad : A × (WholeState × List (Call TypedSpec WholeState)) → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler signed) work).run (before,leading))}[bad result] ≤
    Pr{let result ← ((simulateQ (RegistrationNativeStageTrace.handler canonical) work).run (canonicalBefore,[]))}[
      ∃ original∈support ((simulateQ (RegistrationNativeStageTrace.handler signed) work).run (before,leading)),bad original ∧
        originalMap placeholder original=canonicalMap placeholder leading result] := by
  have image := congrArg (fun distribution => Pr{let result ← distribution}[
    ∃ original∈support ((simulateQ (RegistrationNativeStageTrace.handler signed) work).run (before,leading)),bad original ∧
      originalMap placeholder original=result])
    (source setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder work before leading canonicalBefore seed ready sameBefore)
  simp only [prEvent_map] at image
  refine le_trans ?_ image.le
  apply prEvent_mono_of_support
  intro result reached failed
  exact ⟨result,reached,failed,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability.canonical_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedImageProbability.canonical_source
