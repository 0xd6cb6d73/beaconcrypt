-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource
import BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter

/-! The entire actual Beacon root phase factors through the native arbitrary-pin related-input primitive. Reached selected references and the extracted 192-byte root builder discharge the source equation. The only removed state is private primitive history/cache; every native World, typed callback and optional failure remains. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame
open RegistrationNativeBeaconRootSource (State lift familyImpl)
open RegistrationBeaconRootInterpreter (auxImpl)
open RegistrationAgreementExecutor
open PqxdhBeaconPhase2Preparation (Word32)

theorem lifted_program {Auxiliary Value : Type}
    (backend : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (work : OracleComp Spec Value) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (simulateQ (fun query => lift (backend query)) work).run before =
      (simulateQ backend work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (fun _ current => RegistrationNativeBeaconRootSource.lift_project _ current) work before

private theorem aux_project {Auxiliary : Type}
    (backend : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (auxImpl (fun query => lift (backend query)) authenticated query).run before =
      (auxImpl backend authenticated query).run before.2 := by
  cases query <;> simp only [auxImpl]
  all_goals exact lifted_program backend _ before

private theorem visit_project {Auxiliary Value : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (value : Value) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> ((do let _ ← lift work; pure value) : StateT (State Auxiliary) ProbComp Value).run before =
      ((do let _ ← work; pure value) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Value).run before.2 := by
  change Prod.map id Prod.snd <$>
    (((fun result => (result.1, (before.1, result.2))) <$> work.run before.2) >>=
      fun result => pure (value, result.2)) =
    (work.run before.2 >>= fun result => pure (value, result.2))
  simp only [map_bind, bind_map_left, map_pure, Prod.map, id_eq]

private theorem native_query_project {Auxiliary : Type} {joint : Primitives}
    (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.SumSpec.Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl (fun query => lift (backend query)) authenticated)
        (fun point => lift (visit point)) query).run before =
      (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit query).run before.2 := by
  cases query with
  | decode raw => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.decode raw) before
  | ciphertext response => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.ciphertext response) before
  | ephemeral response => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.ephemeral response) before
  | serverIdentity response => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.serverIdentity response) before
  | publicConversion key => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.publicConversion key) before
  | privateConversion identity => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.privateConversion identity) before
  | decapsulate ciphertext kem => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.decapsulate ciphertext kem) before
  | dhIdentity identity key => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.dhIdentity identity key) before
  | assignedId response => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.assignedId response) before
  | eraseShared secrets => simpa only [PqxdhPhase2GapDhSource.nativeImpl] using aux_project backend authenticated (.eraseShared secrets) before
  | dhPair pair key =>
      cases pair with
      | inl selected =>
          simpa only [PqxdhPhase2GapDhSource.nativeImpl, StateT.run] using
            visit_project (visit key) (Option.map PqxdhPhase2GapDhSource.word (dh.dh scalar (PqxdhPhase2GapDhSource.peer key))) before
      | inr oneTime =>
          simpa only [PqxdhPhase2GapDhSource.nativeImpl, StateT.run] using aux_project backend authenticated (.dhPair oneTime key) before

private theorem native_program_project {Auxiliary Value : Type} {joint : Primitives}
    (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse)
    (work : OracleComp RegistrationBeaconRootInterpreter.SumSpec Value) (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl (fun query => lift (backend query)) authenticated)
        (fun point => lift (visit point))) work).run before =
      (simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (native_query_project dh scalar backend visit authenticated) work before

noncomputable def stage {Auxiliary : Type} {joint : Primitives} {dh : DhInterface joint}
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (backend : QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (family : QueryImpl RegistrationNativeRelatedRoot.RootSpec (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (authenticated : registration.AuthenticatedResponse) : StateT (State Auxiliary) ProbComp (RustM agreement.AgreementEffect) := do
  let pending ← simulateQ (PqxdhPhase2GapDhSource.prefixImpl domain
    (auxImpl (fun query => lift (backend query)) authenticated) (fun point => lift (visit point)))
      (PqxdhPhase2DhMetadata.prepare (completedBinding := authenticated.binding) authenticated.control () () () [])
  match pending with
  | none => pure (.ok (RegistrationBeaconAgreementRoot.rejected authenticated))
  | some pending => simulateQ (familyImpl family) (RegistrationNativeBeaconRootSource.client authenticated pending)

/-- This whole-phase source equation accepts arbitrary native Server pins and retains every reached callback state. -/
theorem stage_source {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (stage domain (RegistrationAgreementShared.implementation source primitive) visit
        (RegistrationNativeRelatedRoot.sourceImpl source hmac joint dh seed scalar) authenticated).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationAgreementShared.implementation source primitive) visit) (beacon authenticated)).run before.2 := by
  rw [RegistrationBeaconPreparationInterpreter.beacon_source dh scalar
    (RegistrationAgreementShared.implementation source primitive) visit authenticated coherent, StateT.run_bind]
  rw [← native_program_project dh scalar (RegistrationAgreementShared.implementation source primitive) visit authenticated
    (PqxdhBeaconPhase2Preparation.prepare (completedBinding := authenticated.binding) authenticated.control () (.inl ()) (.inr ()) () []) before,
    bind_map_left]
  simp only [stage, PqxdhPhase2DhMetadata.prepare, PqxdhBeaconPhase2Preparation.prepare,
    simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind]
  rw [PqxdhPhase2GapDhSource.collect_realization dh domain scalar
    (auxImpl (fun query => lift (RegistrationAgreementShared.implementation source primitive query)) authenticated)
    (fun point => lift (visit point)) () () () []]
  simp only [StateT.run_map, bind_map_left, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | collected, after⟩ reached
  · simp only [Option.bind_none, Option.map_none, simulateQ_pure, StateT.run_pure,
      RegistrationBeaconRootPreparation.afterPrepared, map_pure, Prod.map_apply, id_eq, pure_bind]
  · have references := PqxdhPhase2GapDhSource.collect_references domain
      (auxImpl (fun query => lift (RegistrationAgreementShared.implementation source primitive query)) authenticated)
      (fun point => lift (visit point)) () () () [] before after collected reached
    simp only [Option.bind_some, Option.map_some, PqxdhBeaconPhase2Preparation.afterInputs,
      simulateQ_bind, simulateQ_spec_query, PqxdhPhase2GapDhSource.nativeImpl, auxImpl,
      RegistrationBeaconAgreementRoot.callbacks, simulateQ_pure, StateT.run_pure, pure_bind]
    have metadataEq := (PqxdhPhase2DhMetadata.admitted_exact (completedBinding := authenticated.binding) dh domain scalar authenticated.control collected references).symm
    cases actual : PqxdhBeaconPhase2Preparation.normalPrepare authenticated.control
        (PqxdhPhase2GapDhSource.concreteInputs dh scalar collected).finishInputs with
    | Err error =>
        simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
        simp only [metadataEq, Option.map_none, simulateQ_pure, StateT.run_pure,
          RegistrationBeaconRootPreparation.afterPrepared, map_pure, Prod.map_apply, id_eq]
    | Ok candidate =>
        simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
        have related := PqxdhPhase2DhMetadata.prepared_related (completedBinding := authenticated.binding) dh scalar authenticated.control collected candidate actual
        have exactRoot := RegistrationNativeBeaconRootSource.client_source source hmac dh domain seed scalar primitive authenticated
          ⟨collected.response, collected.ciphertext, collected.ephemeral, candidate, authenticated.binding⟩
          ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata (completedBinding := authenticated.binding) candidate⟩ references related
        simp only [metadataEq, Option.map_some, Prod.map_apply, id_eq, RegistrationBeaconRootPreparation.afterPrepared]
        rw [exactRoot]
        exact RegistrationNativeBeaconRootSource.instrument_program source hmac primitive
          ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata (completedBinding := authenticated.binding) candidate⟩ _ after

end BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage.lifted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage.lifted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage.stage_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootStage.stage_source
