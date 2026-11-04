-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource
/-! Free Server collector and root preparation correspondence under separate persistent states. The only contracts are individual interpreted queries and evaluated preparation replies; the source agreement and complete private-state relation are derived. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady Message)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {I KemSK NativePrivate WordPrivate A : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate)
    (leaves : RegistrationNativePlatformLorIdealAcceptCore.Leaves candidate native symbolic frame)
    (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
local notation "wordOrdinary" => symbolic ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup scalar
local notation "nativeOrdinary" => native ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar
include leaves

theorem local_program {A : Type} (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : WordPrivate) :
    Prod.map id frame <$>
      (simulateQ wordOrdinary (simulateQ (RegistrationNativeSecretWordServerSource.realize candidate) work)).run before =
      (simulateQ nativeOrdinary work).run (frame before) := by
  have sourceEq := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (symbolic ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate) native frame leaves.native_leaf
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work) before
  simp only [QueryImpl.simulateQ_compose] at sourceEq
  rw [←QueryImpl.simulateQ_compose (RegistrationNativeSecretWordServerSource.realize candidate),
    RegistrationNativeSecretWordCheckedOrdinary.ordinary_realize,QueryImpl.simulateQ_compose] at sourceEq
  simpa only [QueryImpl.simulateQ_compose] using sourceEq

theorem prepare (message : Message) (before : WordPrivate) :
    Prod.map (Option.map (RegistrationNativeSecretWordMessage.eval candidate)) frame <$>
      (simulateQ wordOrdinary (RegistrationNativeSecretWordInterface.prepare message)).run before =
      (simulateQ nativeOrdinary (RegistrationBeaconReferenceCompiler.prepare
        (RegistrationNativeSecretWordMessage.eval candidate message))).run (frame before) := by
  have translated := RegistrationNativeSecretWordLocalMessage.eval_materialize setup.joint setup.dh scalar candidate message
  cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message with
  | none =>
    have original : RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar (RegistrationNativeSecretWordMessage.eval candidate message)=none := by
      simpa only [formed,Option.map_none] using translated.symm
    simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,RegistrationBeaconReferenceCompiler.prepare,
      simulateQ_spec_query,RegistrationNativeSecretWordOwners.ordinary,RegistrationNativePublicOwners.ordinary,formed,original,
      simulateQ_pure,StateT.run_pure,map_pure]
    rfl
  | some supplied =>
    have original : RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar (RegistrationNativeSecretWordMessage.eval candidate message)=some (RegistrationNativeSecretWordMessage.eval candidate supplied) := by
      simpa only [formed,Option.map_some] using translated.symm
    simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,RegistrationBeaconReferenceCompiler.prepare,
      simulateQ_spec_query,RegistrationNativeSecretWordOwners.ordinary,RegistrationNativePublicOwners.ordinary,formed,original]
    simpa only [QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,RegistrationBeaconReferenceCompiler.prepare,
      simulateQ_spec_query] using leaves.prepare supplied before

theorem ordinary_leaves : RegistrationNativePlatformLorIdealAcceptCore.Leaves candidate nativeOrdinary wordOrdinary frame := by
  refine ⟨?_,prepare candidate native symbolic frame leaves setup scalar⟩
  intro query before
  have compared := local_program candidate native symbolic frame leaves setup scalar
    ((RegistrationBeaconReferenceCompiler.Spec n KemSK).query query) before
  simpa only [simulateQ_spec_query,QueryImpl.apply_compose] using compared

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves.local_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves.local_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves.ordinary_leaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryLeaves.ordinary_leaves
