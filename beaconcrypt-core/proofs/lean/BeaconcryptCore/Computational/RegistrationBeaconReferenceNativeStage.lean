-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceSource
import BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! The selected Beacon root phase is lowered through the actual global primitive interpreter. The ordinary role backend has no selected prekey scalar; the private native related-root interpretation restores only its two selected DH values and actual root callback. Local environment logs and the complete reached native World/private KEM pool are threaded explicitly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceCompiler (SelectedOwner trustedBackend trustedVisit)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Local (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  EnvState RegistrationServerRoleBackend.State × RegistrationNativeExperiment.State n KemSK source

noncomputable def lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (EnvState RegistrationServerRoleBackend.State)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value) :
    StateT (Local n KemSK mlSource) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
      (work.run before.1)).run before.2

private theorem lower_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : StateT (EnvState RegistrationServerRoleBackend.State)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value)
    (before : Local n KemSK mlSource) :
    (lower setup checks representation created work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (work.run before.1)).run before.2 := rfl

private theorem lower_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    lower (n := n) (mlSource := mlSource) setup checks representation created (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure]

/-- The concrete state lens commutes with every adaptive local continuation. -/
theorem lower_program {Query : Type} {spec : OracleSpec Query}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl spec (StateT (EnvState RegistrationServerRoleBackend.State)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)))) (work : OracleComp spec Value) :
    lower (mlSource := mlSource) setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  have same : (fun query => lower (mlSource := mlSource) setup checks representation created (implementation query)) =
      ((RegistrationNativeExperiment.trusted setup checks representation created mlSource).mapStateTBase implementation).flattenStateT := rfl
  rw [same]
  funext before
  change (lower setup checks representation created (simulateQ implementation work)).run before =
    (simulateQ ((RegistrationNativeExperiment.trusted setup checks representation created mlSource).mapStateTBase implementation).flattenStateT work).run before
  rw [lower_run, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change (id <$> (simulateQ ((RegistrationNativeExperiment.trusted setup checks representation created mlSource).mapStateTBase implementation).flattenStateT work).run before) = _
  exact id_map _

def liftCache {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Result) :
    StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Result := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

noncomputable def primitive (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT (Local n KemSK mlSource) ProbComp) := fun query =>
  lower setup checks representation created (trustedBackend setup owner oneTime query.toRequest)

/-- The concrete lowered callback is exactly the shared-source adapter, with its actual optional replies and full global state. -/
theorem backend_shared (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    liftCache (lower (n := n) setup checks representation created
      (RegistrationBeaconReferenceSource.backend setup owner oneTime query)) =
      RegistrationAgreementShared.implementation setup.source
        (primitive setup checks representation created owner oneTime) query := by
  cases query with
  | root request =>
      have raw : RegistrationBeaconReferenceSource.backend (n := n)
          (Auxiliary := RegistrationServerRoleBackend.State) setup owner oneTime (.root request) =
          pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request)) := by
        change (do
          modify fun (env : EnvState RegistrationServerRoleBackend.State) =>
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

noncomputable def native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (Local n KemSK mlSource) ProbComp) :=
  RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
    (fun query => lower setup checks representation created (RegistrationBeaconReferenceSource.backend setup owner oneTime query))
    (fun point => lower setup checks representation created (RegistrationBeaconReferenceSource.visit point))

private theorem native_cache_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request)
    (before : RawCtxSharedPrimitive.SharedState (Local n KemSK mlSource)) :
    Prod.map id Prod.fst <$> (RegistrationBeaconRootInterpreter.sourceImpl setup.dh scalar
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks representation created owner oneTime))
      (fun point => liftCache (lower setup checks representation created (RegistrationBeaconReferenceSource.visit point))) query).run before =
      (native setup checks representation created scalar owner oneTime query).run before.1 := by
  have backend : ∀ query, Prod.map id Prod.fst <$>
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks representation created owner oneTime) query).run before =
      (lower setup checks representation created (RegistrationBeaconReferenceSource.backend setup owner oneTime query)).run before.1 := by
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
            cache_visit_project (lower setup checks representation created (RegistrationBeaconReferenceSource.visit request.public_key))
              (RegistrationAgreementRoot.nativeOption ((setup.dh.dh scalar
                (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhPhase2GapDhSource.word)) before

/-- The whole native related-root stage runs on the actual full global World/private pool. Only private related-input bookkeeping and a redundant cache frame are projected. -/
theorem stage_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (before : RegistrationNativeBeaconRootSource.State (Local n KemSK mlSource)) :
    Prod.map id (Prod.fst ∘ Prod.snd) <$>
      (RegistrationNativeBeaconRootStage.stage setup.beaconDomain
        (RegistrationAgreementShared.implementation setup.source (primitive setup checks representation created owner oneTime))
        (fun point => liftCache (lower setup checks representation created (RegistrationBeaconReferenceSource.visit point)))
        (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar)
        authenticated).run before =
      (simulateQ (native setup checks representation created scalar owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated)).run before.2.1 := by
  have source := congrArg (fun work => Prod.map id Prod.fst <$> work)
    (RegistrationNativeBeaconRootStage.stage_source setup.source setup.hmac setup.dh setup.beaconDomain created.seed scalar
      (primitive setup checks representation created owner oneTime)
      (fun point => liftCache (lower setup checks representation created (RegistrationBeaconReferenceSource.visit point)))
      authenticated coherent before)
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (native_cache_query setup checks representation created scalar owner oneTime)
    (RegistrationAgreementExecutor.beacon authenticated) before.2
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using source.trans projected

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage.lower_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage.backend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage.backend_shared

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage.stage_native
