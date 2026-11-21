-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerCompiler

/-! The symbolic Server collector is connected to the existing concrete indexed native collector by per-callback equations. Ordinary callback coin programs, actual request logs and complete current environment are retained. The only evaluated reply is the encapsulated shared word; preparation and material calls are absent from this collector. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeSecretWordInterface (LocalSpec effect prepare demand)
open RegistrationNativeSecretWordMessage (Message)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

/-- This extension forwards ordinary reference queries as literal descriptors; only callback queries are reached by the collector. -/
def realize (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (OracleComp (LocalSpec n KemSK))
  | .inl message => Option.map (RegistrationNativeSecretWordMessage.eval candidate) <$>
      prepare (RegistrationNativeSecretWordMessage.literal message)
  | .inr (.inl (.inl message)) => demand (RegistrationNativeSecretWordMessage.literal message)
  | .inr (.inl (.inr query)) => RegistrationNativeSecretWordInterface.common query
  | .inr (.inr (.inl query)) => RegistrationNativeSecretWordInterface.localKem (.inl query)
  | .inr (.inr (.inr (.inl .create))) => RegistrationNativeSecretWordInterface.localKem (.inr (.inl .create))
  | .inr (.inr (.inr (.inl (.decapsulate handle ciphertext)))) =>
      Option.map (RegistrationNativeSecretWord.Word.eval candidate) <$>
        RegistrationNativeSecretWordInterface.localKem (.inr (.inl (.decapsulate handle ciphertext)))
  | .inr (.inr (.inr (.inl (.reveal handle)))) =>
      RegistrationNativeSecretWordInterface.localKem (.inr (.inl (.reveal handle)))
  | .inr (.inr (.inr (.inr key))) => Prod.map id (RegistrationNativeSecretWord.Word.eval candidate) <$>
      RegistrationNativeSecretWordInterface.localKem (.inr (.inr key))

/-- Every actual source environment query is forwarded once with its exact typed reply. -/
theorem effect_query (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ (realize (KemSK := KemSK) candidate) (RegistrationBeaconReferenceCompiler.effect query) = effect query := by
  simp only [RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query, realize,
    RegistrationNativeSecretWordInterface.common, effect]

private theorem environment_program (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ (realize (KemSK := KemSK) candidate)
      (simulateQ RegistrationNativeKemReferenceCompiler.lift
        (simulateQ RegistrationServerReferenceCompiler.effect work)) =
      simulateQ effect work := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have same : (realize candidate ∘ₛ RegistrationNativeKemReferenceCompiler.lift) ∘ₛ
      RegistrationServerReferenceCompiler.effect = (effect :
        QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (LocalSpec n KemSK))) := by
    funext query
    simp only [QueryImpl.compose, RegistrationServerReferenceCompiler.effect,
      RegistrationNativeKemReferenceCompiler.lift, simulateQ_spec_query, realize,
      RegistrationNativeSecretWordInterface.common, effect]
  rw [same]

/-- Every ordinary native local callback keeps its original concrete computation and complete environment. -/
theorem backend_ordinary (setup : Setup base KemSK) (checks : Checks)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (query : RegistrationAgreementExecutor.Request)
    (ordinary : RegistrationNativeKemReferenceCompiler.NonEncapsulation query) (before : Environment) :
    simulateQ (realize candidate) ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks query).run before) =
      (RegistrationNativeSecretWordServerCompiler.backend setup checks query).run before := by
  rw [RegistrationNativeKemReferenceCompiler.backend_ordinary setup checks query ordinary before]
  exact environment_program candidate
    ((RegistrationWorldAgreementCompiler.compiler setup.source
      (RegistrationServerRoleBackend.localBackend setup checks) query).run before)

noncomputable def nativePrefix (setup : Setup base KemSK) (checks : Checks) :=
  PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
    RegistrationNativeKemReferenceCompiler.visit

attribute [local irreducible] RegistrationNativeKemReferenceCompiler.backend
  RegistrationNativeSecretWordServerCompiler.backend

/-- Each original actual indexed callback equals the evaluated symbolic callback on the same complete environment. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    simulateQ (realize candidate) ((nativePrefix (n := n) setup checks query).run before) =
      (simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks)
        (RegistrationNativeSecretWordServerCollect.realize candidate query)).run before := by
  cases query <;>
    simp only [nativePrefix, RegistrationNativeSecretWordServerCompiler.prefixImpl,
      RegistrationNativeSecretWordServerCompiler.ordinaryPrefix, PqxdhServerStaticDhSource.prefixImpl,
      RegistrationAgreementInterpreter.prepImpl, RegistrationAgreementRoot.callbacks,
      RegistrationNativeSecretWordServerCollect.realize, simulateQ_pure, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, StateT.run_pure]
  all_goals try first
    | rfl
    | (rw [show simulateQ (realize candidate)
          ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks _).run before) =
        (RegistrationNativeSecretWordServerCompiler.backend setup checks _).run before from
          backend_ordinary setup checks candidate _ (by trivial) before])
  case encapsulate key =>
    simp only [RegistrationNativeKemReferenceCompiler.backend, RegistrationNativeKemInterface.server,
      RegistrationNativeKemInterface.encapsulate]
    split <;> simp only [simulateQ_pure, map_pure, RegistrationAgreementRoot.option]
    all_goals rfl

/-- The original concrete indexed collector has the exact symbolic evaluated result and complete reached environment, with no source-simulation or candidate-independence premise. -/
theorem collector_source (setup : Setup base KemSK) (checks : Checks)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : Environment) :
    simulateQ (realize candidate)
      ((RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated).run before) =
      Prod.map (Option.map (RegistrationNativeSecretWordServerCollect.eval candidate)) id <$>
        (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated).run before := by
  rw [RegistrationNativeKemReferenceCompiler.collect, QueryImpl.simulateQ_mapStateTBase_run]
  have callbacks : (realize (n := n) candidate).mapStateTBase (nativePrefix (n := n) setup checks) =
      RegistrationNativeSecretWordServerCompiler.prefixImpl (n := n) setup checks ∘ₛ
        RegistrationNativeSecretWordServerCollect.realize candidate := by
    funext query current
    exact query_source (n := n) setup checks candidate query current
  change (simulateQ ((realize candidate).mapStateTBase (nativePrefix setup checks))
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run before = _
  rw [callbacks, RegistrationNativeSecretWordServerCompiler.collect_source, StateT.run_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.effect_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.effect_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.backend_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.backend_ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.collector_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerSource.collector_source
