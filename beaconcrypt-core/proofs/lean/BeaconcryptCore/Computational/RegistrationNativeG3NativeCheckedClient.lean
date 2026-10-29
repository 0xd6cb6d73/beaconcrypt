-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreterTrace
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedRun

/-! The actual two-pass native key compiler agrees with the complete native plain traced execution whenever that same reached execution has no valid unprepared demand. Exact nested source and same-trace audit reconstruction discharge the checked-service comparison internally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClient
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordNativePlain (NativeFrame NativeProvider native)
open RegistrationNativeG3NativeCheckedInterpreter (close observed project)
open RegistrationNativeG3NativeCheckedTrace (read initial)
open RegistrationNativeG3NativeChecked (unchecked)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState)
  (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (providerState : ProviderState)

noncomputable def retained :=
  (simulateQ (close provider)
    ((simulateQ (RegistrationNativeOpenRetained.compiler setup wire route sign)
      (RegistrationNativeG2Trace.program work)).run ordinary)).run providerState

noncomputable def plain :=
  (simulateQ (native setup wire route sign seed scalar target provider)
    (RegistrationNativeG2Trace.program work)).run (ordinary, providerState)

private theorem unchecked_clean
    (clean : ∀ result ∈ support (plain setup wire route sign seed scalar target provider work ordinary providerState),
      (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) result.1.2.events).2 = false)
    (result : (((Value × RegistrationNativeG2Trace.State) × RegistrationNativePublicInterpreter.State n KemSK) × ProviderState) × RegistrationNativeG3NativeChecked.State)
    (supported : result ∈ support ((simulateQ (unchecked setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) (RegistrationNativeKeyFamilyPreparation.inside target))
      (retained setup wire route sign provider work ordinary providerState)).run initial)) :
    result.2.2 = false := by
  have source := RegistrationNativeG3NativeCheckedInterpreter.nested_source setup wire route sign seed scalar target provider
    (RegistrationNativeG2Trace.program work) ordinary providerState initial
  have traced := RegistrationNativeG3NativeCheckedInterpreterTrace.nested_source setup wire route sign seed scalar target provider
    work RegistrationNativeG2Trace.initial (ordinary, providerState)
  have mapped := Set.mem_image_of_mem project supported
  rw [← support_map] at mapped
  change project result ∈ support (project <$> (simulateQ (unchecked setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) (RegistrationNativeKeyFamilyPreparation.inside target))
    ((simulateQ (close provider) ((simulateQ (RegistrationNativeOpenRetained.compiler setup wire route sign)
      (RegistrationNativeG2Trace.program work)).run ordinary)).run providerState)).run initial) at mapped
  rw [source] at mapped
  change project result ∈ support ((simulateQ (observed setup wire route sign seed scalar target provider)
    ((simulateQ RegistrationNativeG2Trace.handler work).run RegistrationNativeG2Trace.initial)).run
      (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) RegistrationNativeG2Trace.initial.events,
        (ordinary, providerState))) at mapped
  rw [traced, support_map] at mapped
  obtain ⟨actual, reached, equal⟩ := mapped
  have same := congrArg (fun value => value.2.1.2) equal
  exact same.symm.trans (clean actual reached)

/-- The original two-pass native key client yields exactly the original result, chronology and full ordinary/provider state of the same clean native execution. -/
theorem client_source
    (clean : ∀ result ∈ support (plain setup wire route sign seed scalar target provider work ordinary providerState),
      (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) result.1.2.events).2 = false) :
    RegistrationNativeKeyCompiler.client setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside target)
      (RegistrationNativeRetainedService.client (retained setup wire route sign provider work ordinary providerState))
      RegistrationNativeKeyPhases.emptyMeta =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        plain setup wire route sign seed scalar target provider work ordinary providerState := by
  rw [RegistrationNativeG3NativeCheckedRun.client_source setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside target)
    (retained setup wire route sign provider work ordinary providerState)
    (unchecked_clean setup wire route sign seed scalar target provider work ordinary providerState clean)]
  have source := RegistrationNativeG3NativeCheckedInterpreter.nested_source setup wire route sign seed scalar target provider
    (RegistrationNativeG2Trace.program work) ordinary providerState initial
  have traced := RegistrationNativeG3NativeCheckedInterpreterTrace.nested_source setup wire route sign seed scalar target provider
    work RegistrationNativeG2Trace.initial (ordinary, providerState)
  let erase : ((Value × RegistrationNativeG2Trace.State) × (RegistrationNativeG3NativeChecked.State × NativeFrame n KemSK ProviderState)) →
      (((Value × RegistrationNativeG2Trace.State) × RegistrationNativePublicInterpreter.State n KemSK) × ProviderState) :=
    fun result => ((result.1, result.2.2.1), result.2.2.2)
  calc
    _ = erase <$> (simulateQ (observed setup wire route sign seed scalar target provider)
        (RegistrationNativeG2Trace.program work)).run (initial, (ordinary, providerState)) := by
      have mapped := congrArg (Functor.map erase) source
      simpa only [retained, Functor.map_map, erase, project, initial, Prod.mk.eta] using mapped
    _ = _ := by
      change erase <$> (simulateQ (observed setup wire route sign seed scalar target provider)
        ((simulateQ RegistrationNativeG2Trace.handler work).run RegistrationNativeG2Trace.initial)).run
          (read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) RegistrationNativeG2Trace.initial.events,
            (ordinary, providerState)) = _
      rw [traced]
      simp only [Functor.map_map, erase, plain, RegistrationNativeG2Trace.program]

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClient.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedClient.client_source
