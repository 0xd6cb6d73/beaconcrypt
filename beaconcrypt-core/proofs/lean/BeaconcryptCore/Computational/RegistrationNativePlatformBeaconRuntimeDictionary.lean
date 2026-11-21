-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveBeaconSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! The actual terminal owner source uses the same material and effect dictionary after the persistent-platform embedding. This local source-tree identity retains every query and outcome. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeBeaconFinishController (lower)
variable {n : Nat} {I KemSK Runtime Auxiliary : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

/-- Each original local source request keeps the exact dictionary through the new persistent-platform embedding. -/
theorem local_query (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (RegistrationNativePlatformPublicFrontend.localQuery false query)) =
      RegistrationNativePublicFrontend.liftLocal false query := by
  cases query with
  | inl message =>
    simp only [RegistrationNativePlatformPublicFrontend.localQuery,RegistrationNativePlatformPublicFrontend.embedLocal,
      RegistrationNativePlatformPublicCoinEmbedding.embed,RegistrationNativePublicFrontend.liftLocal,simulateQ_spec_query]
  | inr query => cases query with
    | inl common =>
      simp only [RegistrationNativePlatformPublicFrontend.localQuery,RegistrationNativePlatformPublicFrontend.embedLocal,
        RegistrationNativePlatformPublicCoinEmbedding.embed,RegistrationNativePublicFrontend.liftLocal,simulateQ_spec_query]
    | inr kem =>
      simp only [RegistrationNativePlatformPublicFrontend.localQuery,RegistrationNativePublicFrontend.liftLocal,
        ← QueryImpl.simulateQ_compose]
      congr 1

private theorem local_program {A : Type} (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work)) =
      simulateQ (RegistrationNativePublicFrontend.liftLocal false) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,local_query]
    congr 1
    funext reply
    exact ih reply

/-- Optional scalar preparation uses the same full local interpreter after the actual source embedding. -/
theorem interpreter (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformTypedBeaconCut.interpreter
      (implementation ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed) setup scalar =
      RegistrationNativeTypedBeaconAllController.interpreter implementation setup scalar := by
  cases scalar with
  | none =>
    funext query
    simp only [RegistrationNativePlatformTypedBeaconCut.interpreter,RegistrationNativeTypedBeaconAllController.interpreter,
      QueryImpl.apply_compose,QueryImpl.simulateQ_compose,local_query]
  | some scalar =>
    funext query
    simp only [RegistrationNativePlatformTypedBeaconCut.interpreter,RegistrationNativeTypedBeaconAllController.interpreter,
      QueryImpl.apply_compose,QueryImpl.simulateQ_compose,local_program]

/-- The terminal source stage uses the same concrete callback after the new shared-P embedding. -/
theorem complete (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) :
    lower (Auxiliary := Auxiliary)
      (RegistrationNativePlatformTypedBeaconCut.interpreter (implementation ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed) setup none)
      ((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current) =
    lower (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
      ((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current) := by
  apply StateT.ext
  intro before
  unfold lower
  have effects : RegistrationNativePlatformTypedBeaconCut.interpreter
      (implementation ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed) setup none ∘ₛ RegistrationBeaconReferenceCompiler.effect =
      (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false) ∘ₛ RegistrationBeaconReferenceCompiler.effect := by
    funext query
    simp only [RegistrationNativePlatformTypedBeaconCut.interpreter,QueryImpl.apply_compose,
      RegistrationBeaconReferenceCompiler.effect,RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativePlatformPublicFrontend.embedLocal,RegistrationNativePlatformPublicCoinEmbedding.embed,
      RegistrationNativePublicFrontend.liftLocal,simulateQ_spec_query]
  have demand : (fun message => RegistrationNativePlatformTypedBeaconCut.interpreter
      (implementation ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed) setup none (.inr (.inl (.inl message)))) =
      (fun message => (implementation ∘ₛ RegistrationNativePublicFrontend.liftLocal false) (.inr (.inl (.inl message)))) := by
    funext message
    simp only [RegistrationNativePlatformTypedBeaconCut.interpreter,QueryImpl.apply_compose,
      RegistrationNativePlatformPublicFrontend.localQuery,RegistrationNativePlatformPublicFrontend.embedLocal,
      RegistrationNativePlatformPublicCoinEmbedding.embed,RegistrationNativePublicFrontend.liftLocal,simulateQ_spec_query]
  simp only [RegistrationNativePlatformSelectiveBeaconSource.natural,effects,demand]

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary.local_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary.interpreter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary.interpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary.complete
