-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerProviderCache

/-! The actual mutable-Env collector is the generic primitive engine collector after dropping only its unused extra cache. The real World cache, reached optional reply and complete pool/provider state remain in the retained auxiliary component. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerProviderCollect
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderLocal (lower backend primitive)
open RegistrationServerProviderCache (Local visit)
open RegistrationBeaconReferenceGenericStage (liftCache)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)

private theorem cache_project {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Result)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    Prod.map id Prod.fst <$> (liftCache work).run before = work.run before.1 := by
  simp only [liftCache, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact id_map _

private theorem backend_program (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (simulateQ
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected)) work).run before =
      (simulateQ (backend (n := n) setup checks wire route sign seed scalar provider selected) work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst _ work before
  intro query current
  rw [← RegistrationServerProviderCache.backend_shared]
  exact cache_project _ current

private theorem prep_query
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain)
    (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (RegistrationAgreementInterpreter.prepImpl
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected)) query).run before =
      (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks wire route sign seed scalar provider selected) query).run before.1 := by
  cases query with
  | decode raw =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.decode raw)) before
  | identity packet =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.identity packet)) before
  | identityPoint key =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.identityPoint key)) before
  | pqField packet =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.pqField packet)) before
  | preField packet =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.preField packet)) before
  | oneField packet =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.oneField packet)) before
  | verify key signed =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.verify key signed)) before
  | registrationStatus rid =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.registrationStatus rid)) before
  | reserveRegistration =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.reserveRegistration)) before
  | parseDh point =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.parseDh point)) before
  | generate =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.generate)) before
  | parseKem key =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.parseKem key)) before
  | encapsulate key =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.encapsulate key)) before
  | publicConversion key =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.publicConversion key)) before
  | privateConversion =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.privateConversion)) before
  | ephemeralDh secret key =>
      exact backend_program setup checks wire route sign seed scalar provider selected
        (RegistrationAgreementRoot.callbacks (.ephemeralDh secret key)) before
  | staticDh point => rfl

private theorem cache_visit_project {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Unit)
    (value : Result) (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    Prod.map id Prod.fst <$>
      ((do let _ ← liftCache work; pure value) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Result).run before =
      ((do let _ ← work; pure value) : StateT Auxiliary ProbComp Result).run before.1 := by
  change Prod.map id Prod.fst <$>
    (((fun result => (result.1, (result.2, before.2))) <$> work.run before.1) >>= fun result => pure (value, result.2)) =
    (work.run before.1 >>= fun result => pure (value, result.2))
  simp only [map_bind, bind_map_left, map_pure, Prod.map_def, id_eq]

private theorem prefix_query
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PeerEncoding).Domain)
    (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl
        (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected)))
      (fun point => liftCache (visit (n := n) setup checks wire route sign seed scalar provider selected point)) query).run before =
      (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
        (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks wire route sign seed scalar provider selected))
        (visit (n := n) setup checks wire route sign seed scalar provider selected) query).run before.1 := by
  cases query with
  | decode raw =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.decode raw) before
  | identity packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.identity packet) before
  | identityPoint key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.identityPoint key) before
  | pqField packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.pqField packet) before
  | preField packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.preField packet) before
  | oneField packet =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.oneField packet) before
  | verify key signed =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.verify key signed) before
  | registrationStatus rid =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.registrationStatus rid) before
  | reserveRegistration =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.reserveRegistration) before
  | parseDh point =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.parseDh point) before
  | generate =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.generate) before
  | parseKem key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.parseKem key) before
  | encapsulate key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.encapsulate key) before
  | publicConversion key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.publicConversion key) before
  | privateConversion =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.privateConversion) before
  | ephemeralDh secret key =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        prep_query setup checks wire route sign seed scalar provider selected (.ephemeralDh secret key) before
  | staticDh point =>
      simpa only [PqxdhServerStaticDhSource.prefixImpl, StateT.run] using
        cache_visit_project (visit (n := n) setup checks wire route sign seed scalar provider selected point)
          (PqxdhServerStaticDhSource.selectedReply setup.serverDomain point) before

private theorem lower_pure {Result : Type}
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
      (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp)) (value : Result) :
    lower (Auxiliary := RegistrationServerRoleBackend.State) implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation ((pure value : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Result).run before.1)).run before.2 = pure (value, before)
  simp only [StateT.run_pure, simulateQ_pure, map_pure]

private theorem lower_bind {Result Next : Type}
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
      (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))
    (work : StateT RegistrationServerReferenceCompiler.Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Result)
    (next : Result → StateT RegistrationServerReferenceCompiler.Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Next) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  funext before
  simp only [lower, StateT.run, StateT.monad_bind_def, StateT.bind, simulateQ_bind, map_bind, bind_map_left]

/-- The generic Server engine's actual prefix is the fully lowered native open collector on the same reached Env and provider World. -/
theorem collect_project (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl
        (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected)))
      (fun point => liftCache (visit (n := n) setup checks wire route sign seed scalar provider selected point)))
      (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run before =
      (lower (n := n) (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)).run before.1 := by
  have source := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (prefix_query setup checks wire route sign seed scalar provider selected)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) before
  rw [RegistrationNativeKemReferenceCompiler.collect, RegistrationNativeProviderLocal.lower_program]
  have same : (fun (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PeerEncoding).Domain) => lower (n := n) (localImpl setup wire route sign seed scalar provider selected)
      (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
        (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend setup checks))
        RegistrationNativeKemReferenceCompiler.visit query)) =
      PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
        (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks wire route sign seed scalar provider selected))
        (visit (n := n) setup checks wire route sign seed scalar provider selected) := by
    funext query
    unfold backend
    cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl,
      RegistrationNativeProviderLocal.lower_program, lower_pure, lower_bind, visit]
  rw [same]
  exact source

end BeaconcryptCore.Computational.RegistrationServerProviderCollect
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderCollect.collect_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderCollect.collect_project
