-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceSource
import BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage

/-! The selected native Beacon stage is natural in its concrete ordinary callback interpreter. This algebraic source equation retains the entire caller environment and private interpreter state; no secure-backend or whole-game simulation premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner trustedBackend trustedVisit)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Value Auxiliary Private : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Local (Auxiliary Private : Type) := EnvState Auxiliary × Private

noncomputable def lower (_setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (work : StateT (EnvState Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value) :
    StateT (Local Auxiliary Private) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ trusted
      (work.run before.1)).run before.2

private theorem lower_run (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (work : StateT (EnvState Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value)
    (before : Local Auxiliary Private) :
    (lower (Auxiliary := Auxiliary) setup trusted work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ trusted
          (work.run before.1)).run before.2 := rfl

private theorem lower_pure (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp)) (value : Value) :
    lower (n := n) (Auxiliary := Auxiliary) setup trusted (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure]

/-- The concrete state lens commutes with every adaptive local continuation. -/
theorem lower_program {Query : Type} {spec : OracleSpec Query}
    (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (implementation : QueryImpl spec (StateT (EnvState Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)))) (work : OracleComp spec Value) :
    lower (Auxiliary := Auxiliary) setup trusted (simulateQ implementation work) =
      simulateQ (fun query => lower (Auxiliary := Auxiliary) setup trusted (implementation query)) work := by
  have same : (fun query => lower (Auxiliary := Auxiliary) setup trusted (implementation query)) =
      (trusted.mapStateTBase implementation).flattenStateT := rfl
  rw [same]
  funext before
  change (lower (Auxiliary := Auxiliary) setup trusted (simulateQ implementation work)).run before =
    (simulateQ (trusted.mapStateTBase implementation).flattenStateT work).run before
  rw [lower_run, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change (id <$> (simulateQ (trusted.mapStateTBase implementation).flattenStateT work).run before) = _
  exact id_map _

def liftCache {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Result) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Result := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

noncomputable def primitive (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT (Local Auxiliary Private) ProbComp) := fun query =>
  lower (Auxiliary := Auxiliary) setup trusted (trustedBackend setup owner oneTime query.toRequest)

/-- The concrete lowered callback is exactly the shared-source adapter, with its actual optional replies and full global state. -/
theorem backend_shared (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    liftCache (lower (n := n) (Auxiliary := Auxiliary) setup trusted
      (RegistrationBeaconReferenceSource.backend setup owner oneTime query)) =
      RegistrationAgreementShared.implementation setup.source
        (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime) query := by
  cases query with
  | root request =>
      have raw : RegistrationBeaconReferenceSource.backend (n := n)
          (Auxiliary := Auxiliary) setup owner oneTime (.root request) =
          pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request)) := by
        change (do
          modify fun (env : EnvState Auxiliary) =>
            { env with requests := env.requests ++ [] }
          pure (core.option.Option.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))) = _
        simp only [List.append_nil]
        rfl
      rw [raw, lower_pure]
      rfl
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request => rfl

private theorem cache_project {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Result)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    Prod.map id Prod.fst <$> (liftCache work).run before = work.run before.1 := by
  simp only [liftCache, StateT.run, Functor.map_map, Prod.map, id_eq]
  exact id_map _

private theorem cache_visit_project {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Unit)
    (value : Result) (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    Prod.map id Prod.fst <$>
      ((do let _ ← liftCache work; pure value) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Result).run before =
      ((do let _ ← work; pure value) : StateT Auxiliary ProbComp Result).run before.1 := by
  change Prod.map id Prod.fst <$>
    (((fun result => (result.1, (result.2, before.2))) <$> work.run before.1) >>=
      fun result => pure (value, result.2)) =
    (work.run before.1 >>= fun result => pure (value, result.2))
  simp only [map_bind, bind_map_left, map_pure, Prod.map, id_eq]

noncomputable def native (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (Local Auxiliary Private) ProbComp) :=
  RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
    (fun query => lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.backend setup owner oneTime query))
    (fun point => lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit point))

private theorem native_cache_query (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request)
    (before : RawCtxSharedPrimitive.SharedState (Local Auxiliary Private)) :
    Prod.map id Prod.fst <$> (RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
      (RegistrationAgreementShared.implementation setup.source (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime))
      (fun point => liftCache (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit point))) query).run before =
      (native setup trusted scalar owner oneTime query).run before.1 := by
  have backend : ∀ query, Prod.map id Prod.fst <$>
      (RegistrationAgreementShared.implementation setup.source (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime) query).run before =
      (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.backend setup owner oneTime query)).run before.1 := by
    intro query
    rw [← backend_shared]
    exact cache_project _ before
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | root request => exact backend _
  | dh request =>
      cases role : request.secret_role with
      | LocalIdentity | ServerEphemeral | BeaconOneTime =>
          simpa only [RegistrationBeaconRootInterpreter.sourceImpl, native, role] using backend (.dh request)
      | BeaconPrekey =>
          simpa only [RegistrationBeaconRootInterpreter.sourceImpl, native, role, StateT.run] using
            cache_visit_project (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit request.public_key))
              (RegistrationAgreementRoot.nativeOption ((setup.dh.dh scalar
                (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhPhase2GapDhSource.word)) before

/-- The whole native related-root stage retains the complete concrete ordinary-interpreter state and caller environment. Only private related-input bookkeeping and a redundant cache frame are projected. -/
theorem stage_native (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Private ProbComp)) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (before : RegistrationNativeBeaconRootSource.State (Local Auxiliary Private)) :
    Prod.map id (Prod.fst ∘ Prod.snd) <$>
      (RegistrationNativeBeaconRootStage.stage setup.beaconDomain
        (RegistrationAgreementShared.implementation setup.source (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime))
        (fun point => liftCache (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit point)))
        (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh seed scalar)
        authenticated).run before =
      (simulateQ (native setup trusted scalar owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated)).run before.2.1 := by
  have source := congrArg (fun work => Prod.map id Prod.fst <$> work)
    (RegistrationNativeBeaconRootStage.stage_source setup.source setup.hmac setup.dh setup.beaconDomain seed scalar
      (primitive (Auxiliary := Auxiliary) setup trusted owner oneTime)
      (fun point => liftCache (lower (Auxiliary := Auxiliary) setup trusted (RegistrationBeaconReferenceSource.visit point)))
      authenticated coherent before)
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (native_cache_query setup trusted scalar owner oneTime)
    (RegistrationAgreementExecutor.beacon authenticated) before.2
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using source.trans projected

end BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage.lower_program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage.backend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage.backend_shared
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage.stage_native
