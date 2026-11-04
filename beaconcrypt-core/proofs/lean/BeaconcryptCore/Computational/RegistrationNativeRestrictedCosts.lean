-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialCosts
import BeaconcryptCore.Computational.RegistrationNativePublicationCosts

/-! Literal local bills for the actual restricted selective backend. Root preparation costs no capability; material demand uses only its actual coin sampler; publication retains shared CTX/signing requests; indexed KEM retains the supplied primitive program and private pool state. These are per-request source bills, not a supplied native callback frame. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePrimitiveCosts (coinCost)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def bill (qSign qKem : Nat) : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → EffectKind → Nat
  | .inl (.inl _), _ => 0
  | .inl (.inr (.inl (.inl _))), kind => coinCost 108 kind
  | .inl (.inr (.inl (.inr (.inl query)))), kind => RegistrationNativePublicationCosts.bill qSign query kind
  | .inl (.inr (.inl (.inr (.inr query)))), kind => if effectKind query = kind then 1 else 0
  | .inl (.inr (.inr _)), kind => coinCost qKem kind
  | .inr _, _ => 0

/-- The actual selective local interpreter discharges every leaf bill on its complete local state, including all optional failures and primitive histories. -/
theorem restricted_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (qSign qKem : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (kind : EffectKind) :
    ((RegistrationNativeSelectiveEntropyBackend.restricted setup wire sign seed scalar candidate provider query).run before).IsQueryBoundP
      (fun query => effectKind query = kind) (bill qSign qKem query kind) := by
  rcases query with (message | ((message | (publication | effect)) | query)) | record
  · simp only [RegistrationNativeSelectiveEntropyBackend.restricted,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.onKeys,
      RegistrationNativeHiddenService.prepare, StateT.run, simulateQ_map, simulateQ_pure]
    trivial
  · simp only [RegistrationNativeSelectiveEntropyBackend.restricted,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onKeys,
      StateT.run, simulateQ_map, RegistrationNativeHiddenEnvironmentHandler.effects_project,
      isQueryBoundP_map_iff, bill]
    exact RegistrationNativeSelectiveMaterialCosts.demand_bound setup.source _ _ candidate message _ kind
  · simp only [RegistrationNativeSelectiveEntropyBackend.restricted,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
      StateT.run, simulateQ_map, RegistrationNativeHiddenEnvironmentHandler.effects_project,
      isQueryBoundP_map_iff, bill]
    exact RegistrationNativePublicationCosts.compiler_bound setup.source wire.frameWrite sign qSign signing publication before.1.receipts kind
  · simp only [RegistrationNativeSelectiveEntropyBackend.restricted,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
      StateT.run, StateT.lift, PqxdhRecordLiftInterface.effectLift, bind_pure_comp, bill]
    apply (isQueryBoundP_query_iff (spec := EnvEffects n) (p := fun query => effectKind query = kind) effect _).mpr
    split <;> simp_all
  · simp only [RegistrationNativeSelectiveEntropyBackend.restricted,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.routed,
      StateT.run, simulateQ_map, RegistrationNativeHiddenEnvironmentHandler.coins_project,
      isQueryBoundP_map_iff, bill]
    exact RegistrationNativePrimitiveCosts.coins_bound _ qKem (kem query (before.1.pool, before.1.provider)) kind
  · rcases record with (send | raw) | ⟨index, send | raw⟩
    all_goals simp only [RegistrationNativeSelectiveEntropyBackend.restricted,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, StateT.run, StateT.lift]
    all_goals trivial

/-- Source-derived weighted local bills transport through every shared-state selective backend continuation. -/
theorem program_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (qSign qKem : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (bound : Nat) (kind : EffectKind)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted (fun query => bill (n := n) qSign qKem query kind) work bound)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    ((simulateQ (RegistrationNativeSelectiveEntropyBackend.restricted setup wire sign seed scalar candidate provider) work).run before).IsQueryBoundP
      (fun query => effectKind query = kind) bound :=
  PqxdhRecordLiftCtxBills.run_bound _ _ _
    (fun query current => restricted_bound setup wire sign seed scalar candidate provider qSign qKem signing kem query current kind)
    work bound bounded before

/-- The literal native restricted callback uses its source frontend bill with both frontend and private service state retained. -/
theorem callback_bound (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept qSign qKem : Nat)
    (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
    (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)
    (query : RegistrationNativeEntropyInterface.EnvQuery)
    (before : RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source)
    (bound : Nat) (kind : EffectKind)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted (fun query => bill (n := n) qSign qKem query kind)
      ((RegistrationNativeHiddenEnvironmentRaw.frontend (n := n) setup checks wire source
        (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept
        (setup.dh.publicKey scalar) (.inr query.val)).run before.1) bound) :
    ((RegistrationNativeSelectiveEntropyEnvironment.step setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept query).run before).IsQueryBoundP
        (fun query => effectKind query = kind) bound := by
  simp only [RegistrationNativeSelectiveEntropyEnvironment.step, StateT.run, isQueryBoundP_map_iff]
  exact program_bound setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    qSign qKem (RegistrationNativePrimitiveCosts.signing_bound source qSign signing credential) kem _ bound kind bounded before.2

end BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts.restricted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts.restricted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRestrictedCosts.callback_bound
