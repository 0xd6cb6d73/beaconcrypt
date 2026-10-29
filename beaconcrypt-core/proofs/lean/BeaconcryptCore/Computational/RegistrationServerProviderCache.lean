-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderLocal
import BeaconcryptCore.Computational.RegistrationBeaconReferenceGenericStage

/-! The Server agreement engine's extra cache is an unused frame. The actual World and its CTX cache remain inside the full provider interpreter state and are never erased by this lens. Every concrete lower callback, including optional candidate KEM replies, is the same shared-source primitive. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerProviderCache
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider State)
open RegistrationNativeProviderLocal (lower backend primitive)
open RegistrationNativeProviderSource (localImpl)
open RegistrationBeaconReferenceGenericStage (liftCache)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
abbrev Local (n : Nat) (KemSK ProviderState : Type) := RegistrationServerReferenceCompiler.Environment × State n KemSK ProviderState

private theorem lower_run (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (State n KemSK ProviderState) ProbComp))
    (work : StateT RegistrationServerReferenceCompiler.Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Value)
    (before : Local n KemSK ProviderState) :
    (lower implementation work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2 := rfl

private theorem lower_pure (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (State n KemSK ProviderState) ProbComp)) (value : Value) :
    lower (Auxiliary := RegistrationServerRoleBackend.State) implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure]

/-- The actual concrete mutable-Env callback is the generic shared-source adapter, preserving its whole World, pool and provider phase. -/
theorem backend_shared (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : RegistrationAgreementExecutor.Request) :
    liftCache (backend (n := n) setup checks wire route sign seed scalar provider selected query) =
      RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected) query := by
  cases query with
  | root request =>
      have raw : RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks (.root request) =
          pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request)) := by
        apply StateT.ext
        intro before
        simp only [RegistrationNativeKemReferenceCompiler.backend, RegistrationNativeKemReferenceCompiler.ordinary,
          RegistrationServerReferenceCompiler.backend, RegistrationServerReferenceCompiler.liftEnvironment,
          RegistrationWorldAgreementCompiler.compiler, RegistrationAgreementShared.auxiliary, StateT.run,
          RegistrationWorldAgreement.recorded, List.append_nil]
        simp only [StateT.monad_pure_def, StateT.pure, simulateQ_pure, map_pure]
      unfold backend
      rw [raw, lower_pure]
      rfl
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request => rfl

private theorem cache_project {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Result)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    Prod.map id Prod.fst <$> (liftCache work).run before = work.run before.1 := by
  simp only [liftCache, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact id_map _

private theorem cache_visit_project {Auxiliary Result : Type} (work : StateT Auxiliary ProbComp Unit)
    (value : Result) (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    Prod.map id Prod.fst <$>
      ((do let _ ← liftCache work; pure value) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Result).run before =
      ((do let _ ← work; pure value) : StateT Auxiliary ProbComp Result).run before.1 := by
  change Prod.map id Prod.fst <$>
    (((fun result => (result.1, (result.2, before.2))) <$> work.run before.1) >>= fun result => pure (value, result.2)) =
    (work.run before.1 >>= fun result => pure (value, result.2))
  simp only [map_bind, bind_map_left, map_pure, Prod.map_def, id_eq]

noncomputable def visit (setup : Setup base KemSK) (_checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (point : PqxdhBeaconPhase2Preparation.Word32) : StateT (Local n KemSK ProviderState) ProbComp Unit :=
  lower (localImpl setup wire route sign seed scalar provider selected) (RegistrationNativeKemReferenceCompiler.visit point)

noncomputable def native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool) :=
  RegistrationAgreementInterpreter.sourceImpl setup.joint seed
    (backend (n := n) setup checks wire route sign seed scalar provider selected)
    (visit setup checks wire route sign seed scalar provider selected)

/-- Source query projection removes only the unused extra cache, retaining the actual World CTX cache inside the complete provider state. -/
theorem native_query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : RegistrationAgreementExecutor.Request) (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (RegistrationAgreementInterpreter.sourceImpl setup.joint seed
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected))
      (fun point => liftCache (visit setup checks wire route sign seed scalar provider selected point)) query).run before =
      (native setup checks wire route sign seed scalar provider selected query).run before.1 := by
  have direct : ∀ query, Prod.map id Prod.fst <$>
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected) query).run before =
      (backend setup checks wire route sign seed scalar provider selected query).run before.1 := by
    intro query
    rw [← backend_shared]
    exact cache_project _ before
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | root request => exact direct _
  | dh request =>
      cases role : request.secret_role with
      | ServerEphemeral | BeaconPrekey | BeaconOneTime =>
          simpa only [RegistrationAgreementInterpreter.sourceImpl, native, role] using direct (.dh request)
      | LocalIdentity =>
          simpa only [RegistrationAgreementInterpreter.sourceImpl, native, role, StateT.run] using
            cache_visit_project (visit setup checks wire route sign seed scalar provider selected request.public_key)
              (RegistrationAgreementRoot.nativeOption ((setup.joint.staticDh seed
                (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray)) before

/-- Arbitrary actual native Server agreement programs retain their whole Env, World and provider state under the unused cache frame projection. -/
theorem native_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : RawCtxSharedPrimitive.SharedState (Local n KemSK ProviderState)) :
    Prod.map id Prod.fst <$> (simulateQ (RegistrationAgreementInterpreter.sourceImpl setup.joint seed
      (RegistrationAgreementShared.implementation setup.source (primitive setup checks wire route sign seed scalar provider selected))
      (fun point => liftCache (visit setup checks wire route sign seed scalar provider selected point))) work).run before =
      (simulateQ (native setup checks wire route sign seed scalar provider selected) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (native_query setup checks wire route sign seed scalar provider selected) work before

end BeaconcryptCore.Computational.RegistrationServerProviderCache
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderCache.backend_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderCache.backend_shared
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderCache.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderCache.native_query
/-- info: 'BeaconcryptCore.Computational.RegistrationServerProviderCache.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerProviderCache.native_program
