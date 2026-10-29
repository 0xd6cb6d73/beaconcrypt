-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconCompiler

/-! Per-callback source equations connect the symbolic Beacon collector to the original concrete indexed native preparation. Ordinary local computations, selected-DH visits, all failures and the complete current environment remain literal. Only indexed decapsulation evaluates an opaque shared word. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordServerSource (realize)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

/-- All original primitive coin programs retain their exact computation under either mathematical word realization. -/
theorem sample_source (first second : PqxdhKemIndCca.MlKemSharedSecret) (work : ProbComp Value) :
    simulateQ (realize (n := n) (KemSK := KemSK) first) (RegistrationBeaconReferenceCompiler.sample work) =
      simulateQ (realize (n := n) (KemSK := KemSK) second) (RegistrationBeaconReferenceCompiler.sample work) := by
  unfold RegistrationBeaconReferenceCompiler.sample
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

private theorem other_source (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (first second : PqxdhKemIndCca.MlKemSharedSecret)
    (query : RegistrationNativeKemInterface.OtherSpec.Domain) :
    simulateQ (realize (n := n) first) (RegistrationBeaconReferenceCompiler.other setup owner oneTime query) =
      simulateQ (realize (n := n) second) (RegistrationBeaconReferenceCompiler.other setup owner oneTime query) := by
  unfold RegistrationBeaconReferenceCompiler.other
  exact sample_source first second _

def NonDecapsulation : RegistrationAgreementExecutor.Request → Prop
  | .decapsulate _ => False
  | _ => True

/-- Every original non-KEM-secret callback is independent of the mathematical candidate realization, with its full native request log retained. -/
theorem backend_ordinary (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (first second : PqxdhKemIndCca.MlKemSharedSecret)
    (query : RegistrationAgreementExecutor.Request) (ordinary : NonDecapsulation query) (before : EnvState Auxiliary) :
    simulateQ (realize (n := n) first) ((RegistrationBeaconReferenceCompiler.backend setup owner oneTime query).run before) =
      simulateQ (realize (n := n) second) ((RegistrationBeaconReferenceCompiler.backend setup owner oneTime query).run before) := by
  cases query <;>
    simp only [RegistrationBeaconReferenceCompiler.backend, StateT.run_bind, StateT.run_modify, StateT.run_lift,
      bind_pure_comp, pure_bind, simulateQ_map, RegistrationBeaconReferenceCompiler.backendCore,
      RegistrationBeaconReferenceCompiler.primitive, RegistrationNativeKemInterface.beacon,
      RegistrationNativeKemInterface.other, simulateQ_spec_query, simulateQ_pure]
  all_goals first
    | exact False.elim ordinary
    | rfl
    | (rw [other_source setup owner oneTime first second])

noncomputable def nativePrefix (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :=
  PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
    (RegistrationBeaconRootInterpreter.auxImpl (RegistrationBeaconReferenceCompiler.backend (n := n) (Auxiliary := Auxiliary) setup owner oneTime)
      authenticated) RegistrationBeaconReferenceCompiler.visit

attribute [local irreducible] RegistrationBeaconReferenceCompiler.backend

/-- Every actual native prefix callback equals its symbolic evaluated callback on the same entire environment. -/
theorem query_source (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    simulateQ (realize candidate) ((nativePrefix (n := n) setup owner oneTime authenticated query).run before) =
      (simulateQ (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated)
        (RegistrationNativeSecretWordBeaconCollect.realize candidate query)).run before := by
  cases query <;>
    simp only [nativePrefix, RegistrationNativeSecretWordBeaconCompiler.prefixImpl,
      RegistrationNativeSecretWordBeaconCompiler.ordinaryPrefix, PqxdhPhase2GapDhSource.prefixImpl,
      RegistrationBeaconRootInterpreter.auxImpl, RegistrationBeaconAgreementRoot.callbacks,
      RegistrationNativeSecretWordBeaconCollect.realize, simulateQ_pure, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, StateT.run_pure, RegistrationNativeSecretWordBeaconCollect.ordinary,
      QueryImpl.mapStateTBase, StateT.run_mk]
  all_goals try first
    | rfl
    | (rw [backend_ordinary setup owner oneTime candidate RegistrationNativeSecretWordMessage.zero _ (by trivial) before])
  case decapsulate ciphertext kem =>
    simp only [RegistrationBeaconReferenceCompiler.backend, StateT.run_bind, StateT.run_modify, StateT.run_lift,
      pure_bind, bind_pure_comp, simulateQ_map, RegistrationBeaconReferenceCompiler.backendCore,
      RegistrationBeaconReferenceCompiler.primitive, RegistrationNativeKemInterface.beacon, simulateQ_map,
      simulateQ_spec_query, RegistrationNativeSecretWordServerSource.realize, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationAgreementRoot.option, Functor.map_map]
    simp only [StateT.run, Functor.map_map]
    congr 1
    funext reply
    cases reply <;> rfl

/-- The original concrete indexed Beacon preparation restores exactly from the symbolic prepared record, including every reached environment field. -/
theorem collector_source (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (before : EnvState Auxiliary) :
    simulateQ (realize candidate) ((RegistrationBeaconReferenceCompiler.collect (n := n) setup owner oneTime authenticated).run before) =
      Prod.map (Option.map (RegistrationNativeSecretWordBeaconPrepare.eval candidate)) id <$>
        (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated).run before := by
  rw [RegistrationBeaconReferenceCompiler.collect, QueryImpl.simulateQ_mapStateTBase_run]
  have callbacks : (realize candidate).mapStateTBase (nativePrefix (n := n) (Auxiliary := Auxiliary) setup owner oneTime authenticated) =
      RegistrationNativeSecretWordBeaconCompiler.prefixImpl (Auxiliary := Auxiliary) setup owner oneTime authenticated ∘ₛ
        RegistrationNativeSecretWordBeaconCollect.realize candidate := by
    funext query current
    exact query_source setup owner oneTime authenticated candidate query current
  change (simulateQ ((realize candidate).mapStateTBase (nativePrefix setup owner oneTime authenticated))
    (PqxdhPhase2DhMetadata.prepare authenticated.pending.control () () () [])).run before = _
  rw [callbacks, RegistrationNativeSecretWordBeaconCompiler.collect_source, StateT.run_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.sample_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.backend_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.backend_ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.collector_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource.collector_source
