-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconConversion

/-! The real Beacon related-root stage starts from the actual authenticated response. Its selected-DH references and public conversion are derived from the reached prefix; projection retains the complete native primitive state and shared CTX cache. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconRootStage

open RegistrationAgreementExecutor
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhServerRelatedRootConsumer (State)
open RegistrationRootStage (lifted)
open RegistrationBeaconRootInterpreter (auxImpl)

theorem aux_project {Auxiliary : Type} (backend : QueryImpl Spec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (auxImpl (lifted backend) authenticated query).run before =
      (auxImpl backend authenticated query).run before.2 := by
  cases query <;> simp only [auxImpl]
  all_goals exact RegistrationRootStage.lifted_program backend _ before

theorem visit_project {Auxiliary Value : Type} (work : StateT Auxiliary ProbComp Unit) (value : Value)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$> ((do let _ ← RegistrationRootStage.lift work; pure value) : StateT (State Auxiliary) ProbComp Value).run before =
      ((do let _ ← work; pure value) : StateT Auxiliary ProbComp Value).run before.2 := by
  change Prod.map id Prod.snd <$>
    (((fun result : Unit × Auxiliary => (result.1, (before.1, result.2))) <$> work.run before.2) >>=
      fun result => pure (value, result.2)) =
    (work.run before.2 >>= fun result => pure (value, result.2))
  simp only [map_bind, bind_map_left, map_pure, Prod.map, id_eq]

theorem native_query_project {Auxiliary : Type} {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.SumSpec.Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl (lifted backend) authenticated)
        (fun point => RegistrationRootStage.lift (visit point)) query).run before =
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
          visit_project (visit key) (Option.map PqxdhPhase2GapDhSource.word
            (dh.dh scalar (PqxdhPhase2GapDhSource.peer key))) before
    | inr oneTime =>
        simpa only [PqxdhPhase2GapDhSource.nativeImpl, StateT.run] using
          aux_project backend authenticated (.dhPair oneTime key) before

theorem native_program_project {Auxiliary Result : Type} {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse)
    (work : OracleComp RegistrationBeaconRootInterpreter.SumSpec Result) (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl (lifted backend) authenticated)
        (fun point => RegistrationRootStage.lift (visit point))) work).run before =
      (simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar (auxImpl backend authenticated) visit) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (native_query_project dh scalar backend visit authenticated) work before

noncomputable def stage {Auxiliary : Type} {joint : Primitives} {dh : DhInterface joint}
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (family : QueryImpl PqxdhJointDhExtractRoot.RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (publicValue : PublicChallenge) (authenticated : registration.AuthenticatedResponse) :
    StateT (State Auxiliary) ProbComp (RustM agreement.AgreementEffect) := do
  let pending ← (simulateQ (PqxdhPhase2GapDhSource.prefixImpl domain (auxImpl (lifted backend) authenticated)
    (fun point => RegistrationRootStage.lift (visit point))) (PqxdhPhase2DhMetadata.prepare authenticated.pending.control () () () []))
  match pending with
  | none => pure (.ok (RegistrationBeaconAgreementRoot.rejected authenticated))
  | some pending =>
      simulateQ (PqxdhPhase2DhRootConsumer.familyImpl family) (RegistrationBeaconRelatedRoot.client publicValue authenticated pending)

private theorem lifted_aux_conversion {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse) (key : Word32)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) (converted : Word32)
    (after : State (RawCtxSharedPrimitive.SharedState Auxiliary))
    (supported : (some converted, after) ∈ support
      ((auxImpl (lifted (RegistrationBeaconConversion.backend source primitive)) authenticated
        (.publicConversion key)).run before)) :
    source.crypto.xpkConv (absBytes key) = some (absBytes converted) := by
  apply RegistrationBeaconConversion.aux_conversion source primitive authenticated key converted before.2 after.2
  rw [← aux_project (RegistrationBeaconConversion.backend source primitive) authenticated (.publicConversion key) before,
    support_map]
  exact ⟨_, supported, rfl⟩

theorem stage_source {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
      (stage domain (RegistrationBeaconConversion.backend source primitive) visit
        (PqxdhJointDhExtractRoot.sourceImpl source hmac joint dh seed scalar)
        (challenge joint dh seed scalar) authenticated).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationBeaconConversion.backend source primitive) visit) (beacon authenticated)).run before.2 := by
  rw [RegistrationBeaconPreparationInterpreter.beacon_source dh scalar
    (RegistrationBeaconConversion.backend source primitive) visit authenticated coherent, StateT.run_bind]
  rw [← native_program_project dh scalar (RegistrationBeaconConversion.backend source primitive) visit authenticated
    (PqxdhBeaconPhase2Preparation.prepare authenticated.pending.control () (.inl ()) (.inr ()) () []) before,
    bind_map_left]
  simp only [stage, PqxdhPhase2DhMetadata.prepare, PqxdhBeaconPhase2Preparation.prepare,
    simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind]
  rw [PqxdhPhase2GapDhSource.collect_realization dh domain scalar
    (auxImpl (lifted (RegistrationBeaconConversion.backend source primitive)) authenticated)
    (fun point => RegistrationRootStage.lift (visit point)) () () () []]
  simp only [StateT.run_map, bind_map_left, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | collected, after⟩ reached
  · simp only [Option.bind_none, Option.map_none, simulateQ_pure, StateT.run_pure,
      RegistrationBeaconRootPreparation.afterPrepared, map_pure, Prod.map_apply, id_eq, pure_bind]
  · have references := PqxdhPhase2GapDhSource.collect_references domain
      (auxImpl (lifted (RegistrationBeaconConversion.backend source primitive)) authenticated)
      (fun point => RegistrationRootStage.lift (visit point)) () () () [] before after collected reached
    simp only [Option.bind_some, Option.map_some, PqxdhBeaconPhase2Preparation.afterInputs,
      simulateQ_bind, simulateQ_spec_query, PqxdhPhase2GapDhSource.nativeImpl, auxImpl,
      RegistrationBeaconAgreementRoot.callbacks, simulateQ_pure, StateT.run_pure,
      pure_bind]
    have metadataEq := (PqxdhPhase2DhMetadata.admitted_exact dh domain scalar
      authenticated.pending.control collected references).symm
    cases actual : PqxdhBeaconPhase2Preparation.normalPrepare authenticated.pending.control
        (PqxdhPhase2GapDhSource.concreteInputs dh scalar collected).finishInputs with
    | Err error =>
        simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
        simp only [metadataEq, Option.map_none, simulateQ_pure, StateT.run_pure,
          RegistrationBeaconRootPreparation.afterPrepared, map_pure, Prod.map_apply, id_eq]
    | Ok candidate =>
        simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
        have converted := RegistrationBeaconConversion.collected_conversion source.crypto joint dh domain
          secretOfSeed wiring seed
          (auxImpl (lifted (RegistrationBeaconConversion.backend source primitive)) authenticated)
          (lifted_aux_conversion source primitive authenticated)
          (fun point => RegistrationRootStage.lift (visit point)) authenticated.pending.control pin
          before after collected (PqxdhBeaconPhase2Shared.candidateMetadata candidate) reached metadataEq
        have related := PqxdhPhase2DhMetadata.prepared_related dh scalar authenticated.pending.control collected candidate actual
        have sourceEq := RegistrationBeaconRelatedRoot.client_source source hmac dh domain seed scalar
          (RegistrationPublicConversion.primitive source.crypto primitive) authenticated
          ⟨collected.response, collected.ciphertext, collected.ephemeral, candidate⟩
          ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata candidate⟩ references converted related
        simp only [metadataEq, Option.map_some, Prod.map_apply, id_eq,
          RegistrationBeaconRootPreparation.afterPrepared]
        rw [sourceEq]
        exact RegistrationBeaconRelatedRoot.instrument_program source hmac
          (RegistrationPublicConversion.primitive source.crypto primitive) (challenge joint dh seed scalar)
          ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata candidate⟩ _ after

/-- Per-call source conversion fidelity permits native conversion effects and request instrumentation to remain in the real related-root stage. -/
theorem stage_source_effectful {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (conversion : ∀ key before converted after, (some converted, after) ∈ support
      ((auxImpl (RegistrationAgreementShared.implementation source primitive) authenticated
        (.publicConversion key)).run before) → source.crypto.xpkConv (absBytes key) = some (absBytes converted))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
      (stage domain (RegistrationAgreementShared.implementation source primitive) visit
        (PqxdhJointDhExtractRoot.sourceImpl source hmac joint dh seed scalar)
        (challenge joint dh seed scalar) authenticated).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationAgreementShared.implementation source primitive) visit) (beacon authenticated)).run before.2 := by
  rw [RegistrationBeaconPreparationInterpreter.beacon_source dh scalar
    (RegistrationAgreementShared.implementation source primitive) visit authenticated coherent, StateT.run_bind]
  rw [← native_program_project dh scalar (RegistrationAgreementShared.implementation source primitive) visit authenticated
    (PqxdhBeaconPhase2Preparation.prepare authenticated.pending.control () (.inl ()) (.inr ()) () []) before,
    bind_map_left]
  simp only [stage, PqxdhPhase2DhMetadata.prepare, PqxdhBeaconPhase2Preparation.prepare,
    simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind]
  rw [PqxdhPhase2GapDhSource.collect_realization dh domain scalar
    (auxImpl (lifted (RegistrationAgreementShared.implementation source primitive)) authenticated)
    (fun point => RegistrationRootStage.lift (visit point)) () () () []]
  simp only [StateT.run_map, bind_map_left, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  rintro ⟨_ | collected, after⟩ reached
  · simp only [Option.bind_none, Option.map_none, simulateQ_pure, StateT.run_pure,
      RegistrationBeaconRootPreparation.afterPrepared, map_pure, Prod.map_apply, id_eq, pure_bind]
  · have references := PqxdhPhase2GapDhSource.collect_references domain
      (auxImpl (lifted (RegistrationAgreementShared.implementation source primitive)) authenticated)
      (fun point => RegistrationRootStage.lift (visit point)) () () () [] before after collected reached
    simp only [Option.bind_some, Option.map_some, PqxdhBeaconPhase2Preparation.afterInputs,
      simulateQ_bind, simulateQ_spec_query, PqxdhPhase2GapDhSource.nativeImpl, auxImpl,
      RegistrationBeaconAgreementRoot.callbacks, simulateQ_pure, StateT.run_pure,
      pure_bind]
    have metadataEq := (PqxdhPhase2DhMetadata.admitted_exact dh domain scalar
      authenticated.pending.control collected references).symm
    cases actual : PqxdhBeaconPhase2Preparation.normalPrepare authenticated.pending.control
        (PqxdhPhase2GapDhSource.concreteInputs dh scalar collected).finishInputs with
    | Err error =>
        simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
        simp only [metadataEq, Option.map_none, simulateQ_pure, StateT.run_pure,
          RegistrationBeaconRootPreparation.afterPrepared, map_pure, Prod.map_apply, id_eq]
    | Ok candidate =>
        simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
        have converted := RegistrationBeaconConversion.collected_conversion source.crypto joint dh domain
          secretOfSeed wiring seed
          (auxImpl (lifted (RegistrationAgreementShared.implementation source primitive)) authenticated)
          (fun key before converted after supported => conversion key before.2 converted after.2 (by
            rw [← aux_project (RegistrationAgreementShared.implementation source primitive) authenticated
              (.publicConversion key) before, support_map]
            exact ⟨_, supported, rfl⟩))
          (fun point => RegistrationRootStage.lift (visit point)) authenticated.pending.control pin
          before after collected (PqxdhBeaconPhase2Shared.candidateMetadata candidate) reached metadataEq
        have related := PqxdhPhase2DhMetadata.prepared_related dh scalar authenticated.pending.control collected candidate actual
        have sourceEq := RegistrationBeaconRelatedRoot.client_source source hmac dh domain seed scalar
          primitive authenticated
          ⟨collected.response, collected.ciphertext, collected.ephemeral, candidate⟩
          ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata candidate⟩ references converted related
        simp only [metadataEq, Option.map_some, Prod.map_apply, id_eq,
          RegistrationBeaconRootPreparation.afterPrepared]
        rw [sourceEq]
        exact RegistrationBeaconRelatedRoot.instrument_program source hmac
          primitive (challenge joint dh seed scalar)
          ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata candidate⟩ _ after

theorem stage_real_effectful {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (conversion : ∀ key before converted after, (some converted, after) ∈ support
      ((auxImpl (RegistrationAgreementShared.implementation source primitive) authenticated
        (.publicConversion key)).run before) → source.crypto.xpkConv (absBytes key) = some (absBytes converted))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
      (stage domain (RegistrationAgreementShared.implementation source primitive) visit
        (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
        (challenge joint dh seed scalar) authenticated).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationAgreementShared.implementation source primitive) visit) (beacon authenticated)).run before.2 := by
  rw [PqxdhJointDhExtractRoot.reduction_step source hmac correct]
  exact stage_source_effectful source hmac joint dh domain seed scalar secretOfSeed wiring primitive
    authenticated conversion visit pin coherent before

/-- The actual ordered Beacon preparation and root continuation are the real related-DH family, with the existing source HKDF and public conversion contracts. -/
theorem stage_real {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (authenticated : registration.AuthenticatedResponse)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
      (stage domain (RegistrationBeaconConversion.backend source primitive) visit
        (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
        (challenge joint dh seed scalar) authenticated).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationBeaconConversion.backend source primitive) visit) (beacon authenticated)).run before.2 := by
  rw [PqxdhJointDhExtractRoot.reduction_step source hmac correct]
  exact stage_source source hmac joint dh domain seed scalar secretOfSeed wiring primitive visit authenticated pin coherent before

end BeaconcryptCore.Computational.RegistrationBeaconRootStage

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.aux_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.aux_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.visit_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.visit_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.native_query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.native_query_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.native_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.native_program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_source
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_real

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_source_effectful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_source_effectful

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_real_effectful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootStage.stage_real_effectful
