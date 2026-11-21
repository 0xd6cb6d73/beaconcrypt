-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectService
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
import BeaconcryptCore.Computational.RegistrationNativePublicCaps

/-! Every known108-byte native frontend callback uses the original checked native descriptor service and the same independent ordinary callback. The public World, actual KEM pool/provider, signing receipts and full selective state remain in one execution. The only local capacity certificate is the original remaining demand bill. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State getKeys putKeys actual)
open RegistrationNativeG3LocalMaterialFrame (Ordinary)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

def onKeys (work : StateT (RegistrationNativeSelectiveHiddenService.State n) ProbComp Value) :
    StateT (State n KemSK ProviderState) ProbComp Value := fun before =>
  (fun result => (result.1, (putKeys before.1 result.2, before.2))) <$> work.run (getKeys before.1)

variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (seeds : RegistrationNativeG3AuditedWorld.Seeds n)

noncomputable def handler : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp)
  | .inl (.inl message) => onKeys (RegistrationNativeG3RetainedCallbacks.keys setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate table seeds (.inr (.prepare message)))
  | .inl (.inr (.inl (.inl message))) => Option.map RegistrationNativePairedChoice.Choice.known <$>
      onKeys (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate table seeds (.inr (.demand message)))
  | query => actual setup codec route wire sign seed scalar candidate provider query

private theorem translate_other (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (quiet : Ordinary query) :
    RegistrationNativeG3MaterializedLocal.translate true seeds query = (RegistrationNativePublicFrontend.Spec n KemSK).query query := by
  rcases query with (prepare | (demand | (publication | (coin | capability))) | kem) | record
  · cases quiet
  · cases quiet
  · rfl
  · rfl
  · cases capability <;> try rfl
    case installServer keyId binding ref => cases ref <;> rfl
    case installBeacon owner shell ref => cases ref <;> rfl
  · rfl
  · rfl

private theorem ordinary_source (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (quiet : Ordinary query)
    (before : State n KemSK ProviderState) :
    (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route wire sign seed scalar candidate provider query).run before =
      (actual setup codec route wire sign seed scalar candidate provider query).run before := by
  rw [RegistrationNativeG3MaterializedLocal.handler, QueryImpl.apply_compose,
    translate_other seeds query quiet, simulateQ_spec_query]
  rcases query with (prepare | (demand | common) | kem) | record
  · cases quiet
  · cases quiet
  all_goals change (simulateQ (RegistrationNativeG3CellEager.fixed table)
    (simulateQ RegistrationNativeG3LocalMaterialService.coins
      ((actual setup codec route wire sign seed scalar candidate provider _).run before)) = _)
  all_goals exact RegistrationNativeG3MaterializedDirectService.coins_source table _

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

/-- Every finite known108-byte callback has the exact original direct native service result and complete reached state under its original remaining-demand allowance. -/
theorem query_source (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState)
    (room : before.1.1.keys.next + (if RegistrationNativePublicCaps.IsDemand query then 1 else 0) ≤ n) :
    (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route wire sign seed scalar candidate provider query).run before =
      (handler table setup codec route wire sign seed scalar candidate provider seeds query).run before := by
  rcases query with (prepare | (demand | common) | kem) | record
  · have service := RegistrationNativeG3MaterializedDirectService.prepare_source setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate table seeds prepare (getKeys before.1)
    have lifted := congrArg (Functor.map (fun result => (result.1, (putKeys before.1 result.2, before.2)))) service
    simp only [RegistrationNativeG3MaterializedLocal.handler, QueryImpl.apply_compose,
      RegistrationNativeG3MaterializedLocal.translate, simulateQ_spec_query,
      RegistrationNativeG3LocalMaterialCompletion.fixed, QueryImpl.mapStateTBase,
      RegistrationNativeG3LocalMaterialCompletion.openHandler, RegistrationNativeG3LocalMaterialCompletion.onKeys,
      handler, onKeys, StateT.run, simulateQ_map] at lifted ⊢
    exact lifted.symm
  · have available : before.1.1.keys.next < n := by
      simp only [RegistrationNativePublicCaps.IsDemand, ite_true] at room
      omega
    have service := RegistrationNativeG3MaterializedDirectService.demand_source setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate table seeds demand (getKeys before.1)
      (fun _ _ _ _ => available)
    have lifted := congrArg (Functor.map (fun result => (result.1, (putKeys before.1 result.2, before.2)))) service
    simp only [RegistrationNativeG3MaterializedLocal.handler, QueryImpl.apply_compose,
      RegistrationNativeG3MaterializedLocal.translate, simulateQ_map, simulateQ_spec_query,
      ite_true,
      RegistrationNativeG3LocalMaterialCompletion.fixed, QueryImpl.mapStateTBase,
      RegistrationNativeG3LocalMaterialCompletion.openHandler, RegistrationNativeG3LocalMaterialCompletion.onKeys,
      handler, onKeys, StateT.run, StateT.mk, state_map_apply, Functor.map_map, Prod.map_def, id_eq] at lifted ⊢
    exact lifted.symm
  all_goals exact ordinary_source table setup codec route wire sign seed scalar candidate provider seeds _ (by trivial) before

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectFrontend.query_source
