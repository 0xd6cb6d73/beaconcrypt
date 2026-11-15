-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCompiler

/-! The selected-owner compiler evaluates actual local callbacks rather than an assumed secure backend. Its prekey conversion is derived from the native scalar width. The two unavailable prekey DH callbacks are singled out explicitly for the related-root prefix; all other operands, optional replies and primitive coins agree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationBeaconReferenceCompiler
open RegistrationNativeKemInterface (OtherRequest)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

def Ordinary : OtherRequest → Prop
  | .dh request => request.secret_role ≠ .BeaconPrekey
  | _ => True

theorem other_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (query : OtherRequest) (ordinary : Ordinary query) :
    Prod.fst <$> (RegistrationNativeKemBackend.beaconOther setup scalar query).run
        ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩ =
      Prod.fst <$> (RegistrationBeaconRoleBackend.localBackend setup query.primitive).run
        ⟨owner.identitySeed, some oneTime, none⟩ := by
  cases query with
  | convertPublic key => rfl
  | generate role => rfl
  | convertSecret role =>
      cases role <;> simp only [RegistrationNativeKemBackend.beaconOther, OtherRequest.primitive,
        RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
        RegistrationBeaconRoleBackend.selected_conversion, StateT.run, StateT.monad_pure_def,
        StateT.pure, map_pure]
  | dh request =>
      cases role : request.secret_role <;> simp only [Ordinary, role] at ordinary
      all_goals try { exact False.elim (ordinary rfl) }
      all_goals simp only [RegistrationNativeKemBackend.beaconOther, OtherRequest.primitive,
        RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
        role, StateT.run, map_pure]

theorem sample_lift (work : ProbComp Value) :
    simulateQ (trustedLift (n := n) (KemSK := KemSK)) (trustedSample work) = sample work := by
  rw [trustedSample, sample, ← QueryImpl.simulateQ_compose]
  congr 1

theorem other_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (query : OtherRequest) :
    simulateQ (trustedLift (n := n)) (trustedOther setup owner oneTime query) = other setup owner oneTime query :=
  sample_lift _

theorem primitive_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (query : RegistrationAgreementShared.PrimitiveRequest) :
    simulateQ (trustedLift (n := n)) (trustedPrimitive setup owner oneTime query) = primitive setup owner oneTime query := by
  simp only [trustedPrimitive, primitive, ← QueryImpl.simulateQ_compose]
  congr 1
  funext lower
  cases lower with
  | inl query => exact other_lift setup owner oneTime query
  | inr query => simp only [QueryImpl.compose, simulateQ_spec_query, trustedLift]

theorem sample_native (mlSource : RegistrationNativeMldsa.Source) (work : ProbComp Value) :
    RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary)
      (mldsaSource := mlSource) work =
      StateT.lift (StateT.lift (trustedSample work)) := by
  let core : QueryImpl unifSpec (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) :=
    fun query => (RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl (.inl query))
  have same : (fun query => RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK)
      (mldsaSource := mlSource) (Auxiliary := Auxiliary) (.inl query)) =
      (core.liftTarget (StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
        (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)))).liftTarget
          (RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary) := by rfl
  rw [RegistrationNativeBeaconFrontend.sample, same, simulateQ_liftTarget, simulateQ_liftTarget]
  rfl

theorem other_sample_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (query : OtherRequest) (ordinary : Ordinary query) :
    RegistrationNativeBeaconFrontend.sample (n := n) (Auxiliary := Auxiliary) (mldsaSource := mlSource)
      (Prod.fst <$> (RegistrationNativeKemBackend.beaconOther setup scalar query).run
        ⟨owner.identitySeed, some oneTime, some owner.kemHandle⟩) =
      StateT.lift (StateT.lift (trustedOther setup owner oneTime query)) := by
  rw [other_native setup scalar owner oneTime query ordinary]
  exact sample_native mlSource _

def OrdinaryPrimitive : RegistrationAgreementShared.PrimitiveRequest → Prop
  | .dh request => request.secret_role ≠ .BeaconPrekey
  | _ => True

theorem primitive_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveRequest) (ordinary : OrdinaryPrimitive query) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup
      (restoreOwner scalar owner) oneTime query =
      StateT.lift (StateT.lift (trustedPrimitive setup owner oneTime query)) := by
  cases query with
  | convertPublic key =>
      simp only [RegistrationNativeBeaconFrontend.primitive, trustedPrimitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, restoreOwner]
      exact other_sample_native setup scalar owner oneTime (.convertPublic key) trivial
  | convertSecret role =>
      simp only [RegistrationNativeBeaconFrontend.primitive, trustedPrimitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, restoreOwner]
      exact other_sample_native setup scalar owner oneTime (.convertSecret role) trivial
  | generate role =>
      simp only [RegistrationNativeBeaconFrontend.primitive, trustedPrimitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, restoreOwner]
      exact other_sample_native setup scalar owner oneTime (.generate role) trivial
  | dh request =>
      simp only [RegistrationNativeBeaconFrontend.primitive, trustedPrimitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        simulateQ_spec_query, restoreOwner]
      exact other_sample_native setup scalar owner oneTime (.dh request) ordinary
  | encapsulate key => rfl
  | decapsulate ciphertext =>
      cases ciphertext with
      | none => rfl
      | some ciphertext =>
          funext owners env
          simp only [RegistrationNativeBeaconFrontend.primitive, trustedPrimitive,
            RegistrationNativeKemInterface.beacon, restoreOwner, simulateQ_map,
            simulateQ_spec_query, RegistrationNativeBeaconFrontend.kem]
          rfl

def OrdinaryAgreement : RegistrationAgreementExecutor.Request → Prop
  | .dh request => request.secret_role ≠ .BeaconPrekey
  | .root _ => False
  | _ => True

theorem agreement_core_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) (ordinary : OrdinaryAgreement query) :
    RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := Auxiliary) setup
      (restoreOwner scalar owner) oneTime query =
      StateT.lift (StateT.lift (trustedBackendCore setup owner oneTime query)) := by
  cases query with
  | root request => exact ordinary.elim
  | convertPublic key => exact primitive_native setup scalar owner oneTime (.convertPublic key) trivial
  | convertSecret role => exact primitive_native setup scalar owner oneTime (.convertSecret role) trivial
  | generate role => exact primitive_native setup scalar owner oneTime (.generate role) trivial
  | encapsulate key => exact primitive_native setup scalar owner oneTime (.encapsulate key) trivial
  | decapsulate ciphertext => exact primitive_native setup scalar owner oneTime (.decapsulate ciphertext) trivial
  | dh request => exact primitive_native setup scalar owner oneTime (.dh request) ordinary

theorem agreement_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) (ordinary : OrdinaryAgreement query) :
    RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup
      (restoreOwner scalar owner) oneTime query = StateT.lift (trustedBackend setup owner oneTime query) := by
  simp only [RegistrationNativeBeaconFrontend.agreement, trustedBackend,
    agreement_core_native setup scalar owner oneTime query ordinary]
  rfl

theorem backend_core_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    simulateQ (trustedLift (n := n)) (trustedBackendCore setup owner oneTime query) = backendCore setup owner oneTime query := by
  cases query with
  | root request => rfl
  | convertPublic key => exact primitive_lift setup owner oneTime (.convertPublic key)
  | convertSecret role => exact primitive_lift setup owner oneTime (.convertSecret role)
  | generate role => exact primitive_lift setup owner oneTime (.generate role)
  | encapsulate key => exact primitive_lift setup owner oneTime (.encapsulate key)
  | decapsulate ciphertext => exact primitive_lift setup owner oneTime (.decapsulate ciphertext)
  | dh request => exact primitive_lift setup owner oneTime (.dh request)

theorem backend_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (query : RegistrationAgreementExecutor.Request)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    simulateQ (trustedLift (n := n)) ((trustedBackend setup owner oneTime query).run env) =
      (backend setup owner oneTime query).run env := by
  simp only [trustedBackend, backend, StateT.run_bind, StateT.run_modify, StateT.run_lift,
    pure_bind, bind_pure_comp, simulateQ_map]
  rw [backend_core_lift]

/-- Every ordinary callback reached by the actual Beacon prefix retains its source operands and complete environment, while the selected scalar is absent from the executable handler. -/
theorem aux_native (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (scalar : ScalarBytes) (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain) :
    RegistrationBeaconRootInterpreter.auxImpl
      (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup (restoreOwner scalar owner) oneTime)
      authenticated query =
    StateT.lift (RegistrationBeaconRootInterpreter.auxImpl (trustedBackend setup owner oneTime) authenticated query) := by
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl,
    RegistrationBeaconAgreementRoot.callbacks, simulateQ_pure, simulateQ_map, simulateQ_spec_query]
  all_goals rfl

theorem backend_program_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    simulateQ (trustedLift (n := n)) ((simulateQ (trustedBackend setup owner oneTime) work).run env) =
      (simulateQ (backend setup owner oneTime) work).run env :=
  simulateQ_StateT_compose _ _ _ (backend_lift setup owner oneTime) work env

theorem aux_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    simulateQ (trustedLift (n := n))
      ((RegistrationBeaconRootInterpreter.auxImpl (trustedBackend setup owner oneTime) authenticated query).run env) =
      (RegistrationBeaconRootInterpreter.auxImpl (backend setup owner oneTime) authenticated query).run env := by
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl]
  all_goals exact backend_program_lift setup owner oneTime _ env

theorem prefix_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    simulateQ (trustedLift (n := n))
      ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl (trustedBackend setup owner oneTime) authenticated) trustedVisit query).run env) =
      (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (RegistrationBeaconRootInterpreter.auxImpl (backend setup owner oneTime) authenticated) visit query).run env := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl]
  all_goals try exact aux_lift setup owner oneTime authenticated _ env
  simp only [trustedVisit, visit, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]

/-- The whole selected public prefix retains the exact trusted source effects and every reached environment field. -/
theorem collect_lift (setup : Setup base KemSK) {mlSource : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner mlSource) (oneTime : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    simulateQ (trustedLift (n := n)) ((trustedCollect setup owner oneTime authenticated).run env) =
      (collect setup owner oneTime authenticated).run env :=
  simulateQ_StateT_compose _ _ _ (prefix_lift setup owner oneTime authenticated)
    (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) env

end BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.other_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.other_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.sample_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.sample_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.other_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.other_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.primitive_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.primitive_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.sample_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.sample_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.other_sample_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.other_sample_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.primitive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.primitive_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.agreement_core_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.agreement_core_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.agreement_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.agreement_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.backend_core_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.backend_core_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.backend_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.backend_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.aux_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.aux_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.backend_program_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.backend_program_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.aux_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.aux_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.prefix_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.prefix_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.collect_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCallbacks.collect_lift
