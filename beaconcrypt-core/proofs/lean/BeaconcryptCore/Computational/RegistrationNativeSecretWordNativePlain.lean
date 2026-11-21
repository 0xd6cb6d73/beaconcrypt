-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasReadiness
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainInterface

/-! The full native unchecked interpreter uses actual full-byte preparation and material requests, unchanged ordinary World callbacks and the literal evaluated KEM provider. The symbolic source differs only in representation of its private KEM words. The entire ledger, chronology, World and provider state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordCheckedClosure (Frame plain)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {ι KemSK Value ProviderState : Type} {base : OracleSpec ι}

private theorem coin_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (work : ProbComp Value) :
    simulateQ (RegistrationNativeSecretWordServiceSource.realize source candidate)
      (simulateQ RegistrationNativeSecretWordService.coins work) =
        simulateQ RegistrationNativeKeyCompiler.coins work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem pure_apply {S A : Type} (value : A) (before : S) :
    (pure value : StateT S (OracleComp KeySpec) A) before = pure (value, before) := rfl

private theorem lift_apply {S A : Type} (work : OracleComp KeySpec A) (before : S) :
    (StateT.lift work : StateT S (OracleComp KeySpec) A) before = (fun value => (value, before)) <$> work := by
  exact bind_pure_comp (fun value => (value, before)) work

/-- Each original native callback is the literal finite symbolic closure, retaining the full current frame and every reply. -/
theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : Provider KemSK) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : Frame n KemSK) :
    (simulateQ (plain setup wire route sign (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside target) provider candidate)
      ((RegistrationNativeSecretWordCheckedFrontend.erase ∘ₛ
        RegistrationNativeSecretWordCheckedFrontend.native setup.source (RegistrationNativeSecretWordProtection.inside target)
          candidate (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar))
        query)).run before =
      (native setup wire route sign seed scalar target (realized candidate provider) query).run before := by
  rcases query with (prepare | (demand | common) | kem) | record
  all_goals simp only [RegistrationNativeSecretWordCheckedFrontend.native, QueryImpl.compose,
    RegistrationNativeSecretWordCheckedFrontend.realization, simulateQ_map, simulateQ_spec_query]
  all_goals try rw [RegistrationNativeSecretWordCheckedClosure.erase_query]
  case inl.inr.inr =>
    rcases kem with (other | key) | pool | key
    all_goals try cases pool
    all_goals simp only [RegistrationNativeSecretWordKemInterface.realize,
      simulateQ_map, simulateQ_spec_query, RegistrationNativeSecretWordInterface.routedKem,
      RegistrationNativeSecretWordCheckedFrontend.implementation,
      RegistrationNativeSecretWordCheckedFrontend.erase, plain, RegistrationNativeSecretWordCheckedClosure.residual,
      RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.routed,
      RegistrationNativeSecretWordCheckedClosure.put, RegistrationNativeSecretWordCheckedClosure.drop,
      native, realized, StateT.run, state_map_apply, simulateQ_map, simulateQ_spec_query,
      RegistrationNativeSecretWordKemProvider.evalReply, RegistrationNativeSecretWordKemPool.reply,
      coin_source, Functor.map_map, Prod.map_def, id_eq]
  all_goals simp only [RegistrationNativeSecretWordCheckedClosure.opened, simulateQ_spec_query,
    plain, RegistrationNativeSecretWordCheckedClosure.residual,
    RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.ordinary,
    RegistrationNativeSecretWordCheckedClosure.put, RegistrationNativeSecretWordCheckedClosure.drop,
    native, ordinary, StateT.run, state_map_apply,
    simulateQ_map, simulateQ_pure, coin_source, Functor.map_map, Prod.map_def, id_eq]
  all_goals try rfl
  case inl.inl =>
    rw [← RegistrationNativeSecretWordNativeMaterial.input_literal setup.joint setup.dh seed scalar candidate prepare]
    simp only [pure_apply, lift_apply, map_pure, Option.map_map,
      Function.comp_def, RegistrationNativeSecretWordMessage.eval_literal]
  case inl.inr.inl.inl =>
    rw [← RegistrationNativeSecretWordNativeMaterial.input_literal setup.joint setup.dh seed scalar candidate demand]
    cases formed : RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
        (RegistrationNativeSecretWordMessage.literal demand)
    all_goals simp only [Option.map_none, Option.map_some, simulateQ_pure, pure_apply, lift_apply, map_pure]
    rename_i key
    rw [RegistrationNativeSecretWordNativeMaterial.material_source]
    cases protectedInput : RegistrationNativeKeyFamilyPreparation.inside target (RegistrationNativeSecretWord.eval candidate key)
    all_goals simp only [RegistrationNativeSecretWordNativeMaterial.material, protectedInput,
      Bool.false_eq_true, ite_false, ite_true, simulateQ_map, simulateQ_pure, simulateQ_spec_query,
      RegistrationNativeSecretWordCheckedClosure.keys, plain, pure_apply, lift_apply,
      state_map_apply, map_pure, Functor.map_map, Prod.map_def, id_eq]
    all_goals rfl

/-- The literal native finite closure agrees for the whole adaptive program, including any retained original ledger and chronological observer in its result. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : Provider KemSK) (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : Frame n KemSK) :
    (simulateQ (plain setup wire route sign (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
        (RegistrationNativeSecretWordProtection.inside target) provider candidate)
      (simulateQ (RegistrationNativeSecretWordCheckedFrontend.erase ∘ₛ
        RegistrationNativeSecretWordCheckedFrontend.native setup.source (RegistrationNativeSecretWordProtection.inside target)
          candidate (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)) work)).run before =
      (simulateQ (native setup wire route sign seed scalar target (realized candidate provider)) work).run before := by
  rw [← QueryImpl.simulateQ_compose]
  have same :
      plain setup wire route sign (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSecretWordProtection.inside target) provider candidate ∘ₛ
        (RegistrationNativeSecretWordCheckedFrontend.erase ∘ₛ
          RegistrationNativeSecretWordCheckedFrontend.native setup.source (RegistrationNativeSecretWordProtection.inside target)
            candidate (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)) =
      native (n := n) setup wire route sign seed scalar target (realized candidate provider) := by
    funext query current
    exact query_source setup wire route sign seed scalar target candidate provider query current
  rw [same]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlain.program_source
