-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendView
/-! Free local programs and the physical external-coin envelope compose with the individual checked dictionaries. All returned replies and the full mutable platform state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms
open RegistrationNativePlatformSecretWordFrontendView
variable {n : Nat} {KemSK Platform A : Type}

private theorem lifted_program {I : Type} {spec : OracleSpec I} {J : Type} {resultSpec : OracleSpec J}
    (implementation : QueryImpl spec (OracleComp resultSpec)) (work : OracleComp spec A) :
    simulateQ (fun query => (StateT.lift (implementation query) : StateT Platform (OracleComp resultSpec) _)) work =
      StateT.lift (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    funext previous
    simp only [StateT.monad_bind_def, StateT.bind, StateT.lift, bind_assoc, pure_bind]

variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)

/-- Every actual free local source program retains its complete checked interpretation and common platform state. -/
theorem native_program (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) :
    nativeBase (Platform := Platform) source inside candidate input (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler selected) work) =
      StateT.lift (simulateQ (RegistrationNativeSecretWordCheckedFrontend.localLift selected)
        (simulateQ (RegistrationNativeSecretWordChecked.native source inside candidate input) work)) := by
  unfold nativeBase
  rw [RegistrationNativePlatformInterpret.state_simulate]
  change simulateQ (fun query => nativeBase (Platform := Platform) source inside candidate input
    (RegistrationNativePlatformPublicFrontend.localHandler selected query)) work = _
  simp only [native_local]
  rw [QueryImpl.simulateQ_compose]
  unfold target
  rw [lifted_program]

/-- Every symbolic free local program retains that same checked global interpretation. -/
theorem word_program (selected : Bool) (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) :
    wordBase (Platform := Platform) source inside candidate input (simulateQ (wordLocal selected) work) =
      StateT.lift (simulateQ (RegistrationNativeSecretWordCheckedFrontend.localLift selected)
        (simulateQ (RegistrationNativeSecretWordChecked.implementation source inside candidate input) work)) := by
  unfold wordBase
  rw [RegistrationNativePlatformInterpret.state_simulate]
  change simulateQ (fun query => wordBase (Platform := Platform) source inside candidate input (wordLocal selected query)) work = _
  simp only [word_local]
  rw [QueryImpl.simulateQ_compose]
  unfold target
  rw [lifted_program]

/-- A proved local source pair lifts through the literal current global envelope with the same routed replies and persistent platform state. -/
theorem source_program (selected : Bool)
    (nativeWork : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A)
    (wordWork : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A)
    (same : simulateQ (RegistrationNativeSecretWordChecked.native source inside candidate input) nativeWork =
      simulateQ (RegistrationNativeSecretWordChecked.implementation source inside candidate input) wordWork) :
    nativeBase (Platform := Platform) source inside candidate input
      (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler selected) nativeWork) =
      StateT.lift (simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation source inside candidate input)
        (simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected) wordWork)) := by
  rw [native_program, same, ← RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program]

/-- The current build's demand, environment and physical coin branches are the exact existing local requests; no source counter is erased. -/
theorem build_embedding :
    RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ
      (RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ RegistrationNativePlatformPublicFrontend.buildEmbedding (n := n) (KemSK := KemSK)) =
      RegistrationNativePublicFrontend.liftLocal false ∘ₛ RegistrationNativePlatformSecretWordBuild.nativeEmbedding := by
  funext query
  rcases query with message | environment | coin
  · rfl
  · rfl
  · rfl

/-- The complete dynamic build tree has its physical checked local projection with all source writer and platform outcomes. -/
theorem build_program (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) A) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
          (simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK)) work))) =
      simulateQ (RegistrationNativeSecretWordCheckedFrontend.localLift false)
        (simulateQ (RegistrationNativeSecretWordChecked.native source inside candidate input ∘ₛ
          RegistrationNativePlatformSecretWordBuild.nativeEmbedding) work) := by
  rw [← QueryImpl.simulateQ_compose RegistrationNativePlatformPublicFrontend.embedLocal RegistrationNativePlatformPublicFrontend.buildEmbedding,
    ← QueryImpl.simulateQ_compose RegistrationNativePlatformPublicCoinEmbedding.embed
      (RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ RegistrationNativePlatformPublicFrontend.buildEmbedding),
    build_embedding, QueryImpl.simulateQ_compose]
  rw [RegistrationNativeSecretWordCheckedFrontendLift.native_program]
  rw [QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.word_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.word_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.build_embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.build_embedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.build_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.build_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms.source_program
