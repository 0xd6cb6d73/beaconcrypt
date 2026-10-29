-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend
import BeaconcryptCore.Computational.RegistrationNativeG3DirectServiceProgress

/-! The actual full direct known108-byte frontend spends selected allocator capacity only at its literal material demand. Ordinary publication, KEM, shared World and record callbacks preserve the entire key-service cursor. These supported-state facts supply the original adaptive prefix room certificate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontendProgress
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State actual)
open RegistrationNativeG3MaterializedDirectFrontend (handler onKeys)
open RegistrationNativeG3LocalMaterialFrame (Ordinary)
variable {n : Nat} {ι KemSK ProviderState Reader Response : Type} {base : OracleSpec ι}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

variable (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

private theorem ordinary_cursor (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (quiet : Ordinary query) (before : State n KemSK ProviderState)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (supported : result ∈ support ((actual setup codec route wire sign seed scalar candidate provider query).run before)) :
    result.2.1.1.keys.next = before.1.1.keys.next := by
  rcases query with (prepare | (demand | common) | kem) | record
  · cases quiet
  · cases quiet
  all_goals try cases common
  all_goals simp only [actual, RegistrationNativeG3LocalKeys.execute,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
    RegistrationNativeHiddenInterpreter.effect, RegistrationNativeHiddenInterpreter.routed,
    StateT.run, simulateQ_map, state_map_apply, state_lift_apply, Functor.map_map, support_map] at supported
  all_goals obtain ⟨inner, _possible, rfl⟩ := supported
  all_goals rfl

/-- Every actual full direct frontend callback advances its selected cursor by at most the original native material-demand bill. -/
theorem query_progress (table : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState)
    (result : (RegistrationNativePublicFrontend.Spec n KemSK).Range query × State n KemSK ProviderState)
    (supported : result ∈ support ((handler table setup codec route wire sign seed scalar candidate provider seeds query).run before)) :
    result.2.1.1.keys.next ≤ before.1.1.keys.next + (if RegistrationNativePublicCaps.IsDemand query then 1 else 0) := by
  rcases query with (prepare | (demand | common) | kem) | record
  · simp only [handler, onKeys, StateT.run, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have progress := RegistrationNativeG3DirectServiceProgress.query_progress setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate table seeds
      (.inr (.prepare prepare)) (RegistrationNativeG3LocalKeys.getKeys before.1) inner reached
    simpa only [RegistrationNativePublicCaps.IsDemand, RegistrationNativeRetainedService.IsDemand,
      ite_false, Nat.add_zero, RegistrationNativeG3LocalKeys.getKeys, RegistrationNativeG3LocalKeys.putKeys] using progress
  · simp only [handler, onKeys, StateT.run, state_map_apply, support_map, Functor.map_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have progress := RegistrationNativeG3DirectServiceProgress.query_progress setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate table seeds
      (.inr (.demand demand)) (RegistrationNativeG3LocalKeys.getKeys before.1) inner reached
    simpa only [RegistrationNativePublicCaps.IsDemand, RegistrationNativeRetainedService.IsDemand,
      ite_true, RegistrationNativeG3LocalKeys.getKeys, RegistrationNativeG3LocalKeys.putKeys, Prod.map_def, id_eq] using progress
  all_goals exact le_of_eq (ordinary_cursor setup codec route wire sign seed scalar candidate provider _ (by trivial) before result supported)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontendProgress
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontendProgress.query_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontendProgress.query_progress
