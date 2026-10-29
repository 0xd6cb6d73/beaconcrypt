-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialService
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFrame

/-! The entire mixed native frontend can open its selected material44 cache while retaining all allocation metadata, nonselected outputs, KEM state, signing receipts and semantic World. The finite-cell completion is applied to that complete adaptive client, including intervening ordinary callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

abbrev Spec (n : Nat) := RegistrationNativeG3LocalMaterialService.Spec n
abbrev Cache (n : Nat) := RegistrationNativeG3LocalMaterialFrame.Cache n
abbrev put := @RegistrationNativeG3LocalMaterialFrame.put

def drop (before : State n KemSK ProviderState) : State n KemSK ProviderState := put before ∅

def onKeys (work : StateT (RegistrationNativeG3LocalMaterialService.State n) (OracleComp (Spec n)) Value) :
    StateT (State n KemSK ProviderState) (OracleComp (Spec n)) Value := fun before =>
  (fun result => (result.1, (RegistrationNativeG3LocalKeys.putKeys before.1 result.2, before.2))) <$>
    work.run (RegistrationNativeG3LocalKeys.getKeys before.1)

noncomputable def openHandler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK ProviderState) (OracleComp (Spec n)))
  | .inl (.inl message) => onKeys (RegistrationNativeG3LocalMaterialService.prepare
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) message)
  | .inl (.inr (.inl (.inl message))) => onKeys (RegistrationNativeG3LocalMaterialService.demand setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message)
  | query => fun before => simulateQ RegistrationNativeG3LocalMaterialService.coins
      ((RegistrationNativeG3LocalKeys.actual setup codec route wire sign seed scalar candidate provider query).run before)

noncomputable def fixed (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :=
  (RegistrationNativeG3CellEager.fixed table).mapStateTBase
    (openHandler (n := n) setup codec route wire sign seed scalar candidate provider)

noncomputable def lazy (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :=
  (RegistrationNativeG3CellEager.lazy.mapStateTBase
    (openHandler (n := n) setup codec route wire sign seed scalar candidate provider)).flattenStateT

/-- Each concrete callback commutes with opening only the material44 cache. Ordinary callbacks retain the reached cache literally. -/
theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) (cache : Cache n) :
    Prod.map id (fun result => put result.1 result.2) <$>
      (lazy setup codec route wire sign seed scalar candidate provider query).run (before, cache) =
      (RegistrationNativeG3LocalKeys.handler setup codec route wire sign seed scalar candidate provider query).run (put before cache) := by
  rw [lazy, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases query with (message | (message | common) | kem) | record
  · have source := RegistrationNativeG3LocalMaterialService.prepare_source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) message
      (RegistrationNativeG3LocalKeys.getKeys before.1) cache
    have lifted := congrArg (fun distribution =>
      (fun result => (result.1, (RegistrationNativeG3LocalKeys.putKeys before.1 result.2, before.2))) <$> distribution) source
    simp only [openHandler, onKeys, RegistrationNativeG3LocalMaterialService.close,
      RegistrationNativeG3LocalKeys.handler, RegistrationNativeG3LocalKeys.localKeys,
      StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq,
      put, RegistrationNativeG3LocalMaterialFrame.put, RegistrationNativeG3LocalMaterialService.put,
      RegistrationNativeG3LocalKeys.getKeys, RegistrationNativeG3LocalKeys.putKeys] at lifted ⊢
    convert lifted using 1 <;> rfl
  · have source := RegistrationNativeG3LocalMaterialService.demand_source setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message
      (RegistrationNativeG3LocalKeys.getKeys before.1) cache
    have lifted := congrArg (fun distribution =>
      (fun result => (result.1, (RegistrationNativeG3LocalKeys.putKeys before.1 result.2, before.2))) <$> distribution) source
    simp only [openHandler, onKeys, RegistrationNativeG3LocalMaterialService.close,
      RegistrationNativeG3LocalKeys.handler, RegistrationNativeG3LocalKeys.localKeys,
      StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq,
      put, RegistrationNativeG3LocalMaterialFrame.put, RegistrationNativeG3LocalMaterialService.put,
      RegistrationNativeG3LocalKeys.getKeys, RegistrationNativeG3LocalKeys.putKeys] at lifted ⊢
    convert lifted using 1 <;> rfl
  · simp only [openHandler, RegistrationNativeG3LocalKeys.handler, StateT.run]
    change _ = _
    have sampled := RegistrationNativeG3LocalMaterialService.coins_source
      ((RegistrationNativeG3LocalKeys.actual setup codec route wire sign seed scalar candidate provider (.inl (.inr (.inl (.inr common))))).run before) cache
    simp only [StateT.run] at sampled
    rw [sampled]
    have framed := (RegistrationNativeG3LocalMaterialFrame.query setup codec route wire sign seed scalar candidate provider
        (.inl (.inr (.inl (.inr common)))) trivial before cache).symm
    simp only [Functor.map_map, Prod.map_def, id_eq] at framed ⊢
    convert framed using 1 <;> rfl
  · simp only [openHandler, RegistrationNativeG3LocalKeys.handler, StateT.run]
    change _ = _
    have sampled := RegistrationNativeG3LocalMaterialService.coins_source
      ((RegistrationNativeG3LocalKeys.actual setup codec route wire sign seed scalar candidate provider (.inl (.inr (.inr kem)))).run before) cache
    simp only [StateT.run] at sampled
    rw [sampled]
    have framed := (RegistrationNativeG3LocalMaterialFrame.query setup codec route wire sign seed scalar candidate provider
        (.inl (.inr (.inr kem))) trivial before cache).symm
    simp only [Functor.map_map, Prod.map_def, id_eq] at framed ⊢
    convert framed using 1 <;> rfl
  · simp only [openHandler, RegistrationNativeG3LocalKeys.handler, StateT.run]
    change _ = _
    have sampled := RegistrationNativeG3LocalMaterialService.coins_source
      ((RegistrationNativeG3LocalKeys.actual setup codec route wire sign seed scalar candidate provider (.inr record)).run before) cache
    simp only [StateT.run] at sampled
    rw [sampled]
    have framed := (RegistrationNativeG3LocalMaterialFrame.query setup codec route wire sign seed scalar candidate provider
        (.inr record) trivial before cache).symm
    simp only [Functor.map_map, Prod.map_def, id_eq] at framed ⊢
    convert framed using 1 <;> rfl

/-- Opening the selected material table preserves the full mixed adaptive execution and all reached private and World state. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) (cache : Cache n) :
    Prod.map id (fun result => put result.1 result.2) <$>
      (simulateQ (lazy setup codec route wire sign seed scalar candidate provider) work).run (before, cache) =
      (simulateQ (RegistrationNativeG3LocalKeys.handler setup codec route wire sign seed scalar candidate provider) work).run (put before cache) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (fun result => put result.1 result.2)
    (fun query current => query_source setup codec route wire sign seed scalar candidate provider query current.1 current.2)
    work (before, cache)

end BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion.program_source
