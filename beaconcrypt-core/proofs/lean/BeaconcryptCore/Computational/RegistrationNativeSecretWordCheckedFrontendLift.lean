-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend

/-! Concrete local-query embeddings commute with the complete routed checked frontend. Selected encapsulation routing changes only its actual getter branch; preparation, material, native common effects and record replies retain their exact interpretations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordCheckedFrontend (Spec localLift implementation realization native)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK Value : Type}

private theorem keys (selected : Bool) (work : OracleComp RegistrationNativeKeyCompiler.KeySpec Value) :
    simulateQ (localLift (n := n) (KemSK := KemSK) selected)
      (simulateQ RegistrationNativeSecretWordChecked.keys work) =
      simulateQ (localLift false) (simulateQ RegistrationNativeSecretWordChecked.keys work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

private theorem material (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (selected : Bool) (message : Message) :
    simulateQ (localLift (n := n) (KemSK := KemSK) selected)
      (RegistrationNativeSecretWordChecked.material source inside candidate input message) =
      simulateQ (localLift false) (RegistrationNativeSecretWordChecked.material source inside candidate input message) := by
  unfold RegistrationNativeSecretWordChecked.material
  simp only [simulateQ_bind, RegistrationNativeSecretWordChecked.audit, simulateQ_spec_query, localLift]
  apply bind_congr
  intro auditReply
  cases input message with
  | none => rfl
  | some key => simp only [simulateQ_map, keys]

/-- Actual symbolic local callbacks retain their same routed interpretation, including the selected getter branch. -/
theorem symbolic (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (selected : Bool) :
    implementation (n := n) (KemSK := KemSK) source inside candidate input ∘ₛ
      RegistrationNativeSecretWordInterface.liftLocal selected =
      localLift selected ∘ₛ RegistrationNativeSecretWordChecked.implementation source inside candidate input := by
  funext query
  rcases query with message | (message | query) | query
  · simp only [QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query,
      implementation, RegistrationNativeSecretWordChecked.implementation,
      RegistrationNativeSecretWordChecked.preparation, RegistrationNativeSecretWordChecked.audit,
      simulateQ_bind, simulateQ_spec_query, localLift, simulateQ_pure]
  · simp only [QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query,
      implementation, RegistrationNativeSecretWordChecked.implementation]
    exact (material source inside candidate input selected message).symm
  · rfl
  · simp only [QueryImpl.compose, RegistrationNativeSecretWordInterface.liftLocal,
      ← QueryImpl.simulateQ_compose, RegistrationNativeSecretWordChecked.implementation,
      localLift, simulateQ_spec_query]
    congr 1

/-- The original local source is lowered through exactly the same opaque-word KEM routing. -/
theorem realization_local (candidate : PqxdhKemIndCca.MlKemSharedSecret) (selected : Bool) :
    realization (n := n) (KemSK := KemSK) candidate ∘ₛ RegistrationNativePublicFrontend.liftLocal selected =
      RegistrationNativeSecretWordInterface.liftLocal selected ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate := by
  funext query
  rcases query with message | (message | query) | query
  · simp only [QueryImpl.compose, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
      realization, RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.prepare,
      simulateQ_map, RegistrationNativeSecretWordInterface.liftLocal]
  · rfl
  · rfl
  · rcases query with other | (pool | key)
    · rfl
    · cases pool <;>
        simp only [QueryImpl.compose, RegistrationNativePublicFrontend.liftLocal,
          RegistrationNativeKemRouting.route, simulateQ_spec_query, RegistrationNativePublicFrontend.liftRoutedKem,
          realization, RegistrationNativeSecretWordKemInterface.realize,
          RegistrationNativeSecretWordInterface.routedKem, RegistrationNativeSecretWordServerSource.realize,
          RegistrationNativeSecretWordInterface.localKem, RegistrationNativeSecretWordInterface.liftLocal,
          RegistrationNativeSecretWordInterface.route, simulateQ_map, simulateQ_spec_query]
    · cases selected <;>
        simp only [QueryImpl.compose, RegistrationNativePublicFrontend.liftLocal,
          RegistrationNativeKemRouting.route, simulateQ_spec_query, RegistrationNativePublicFrontend.liftRoutedKem,
          realization, RegistrationNativeSecretWordKemInterface.realize,
          RegistrationNativeSecretWordInterface.routedKem, RegistrationNativeSecretWordServerSource.realize,
          RegistrationNativeSecretWordInterface.localKem, RegistrationNativeSecretWordInterface.liftLocal,
          RegistrationNativeSecretWordInterface.route, simulateQ_map, simulateQ_spec_query,
          Bool.false_eq_true, ite_false, ite_true]

/-- Every actual symbolic local program retains the complete global checked execution. -/
theorem symbolic_program (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (selected : Bool)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Value) :
    simulateQ (implementation source inside candidate input)
      (simulateQ (RegistrationNativeSecretWordInterface.liftLocal selected) work) =
      simulateQ (localLift selected)
        (simulateQ (RegistrationNativeSecretWordChecked.implementation source inside candidate input) work) := by
  rw [← QueryImpl.simulateQ_compose, symbolic, QueryImpl.simulateQ_compose]

/-- Every original actual local program uses the same routed KEM provider and literal native common callbacks after word realization. -/
theorem native_program (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :
    simulateQ (native source inside candidate input)
      (simulateQ (RegistrationNativePublicFrontend.liftLocal selected) work) =
      simulateQ (localLift selected)
        (simulateQ (RegistrationNativeSecretWordChecked.native source inside candidate input) work) := by
  unfold native RegistrationNativeSecretWordChecked.native
  rw [QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose (realization candidate), realization_local,
    QueryImpl.simulateQ_compose, symbolic_program, QueryImpl.simulateQ_compose]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.symbolic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.symbolic
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.realization_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.realization_local
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.symbolic_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontendLift.native_program
