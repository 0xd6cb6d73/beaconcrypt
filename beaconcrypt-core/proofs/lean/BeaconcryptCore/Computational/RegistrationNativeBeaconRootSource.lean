-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot

/-! Native Beacon descriptors retain their actual converted Server pin. Both selected-prekey DH coordinates are realized by the private native related-input primitive, including arbitrary admitted pins. The exact root-input builder is derived from reached public references; no equality with the selected Server identity or owner ML key is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame
open RegistrationNativeRelatedFamily
open RegistrationNativeRelatedRoot
open PqxdhPhase2GapDhSource
open PqxdhBeaconPhase2Preparation (Word32)

/-- Actual reached prekey operands identify both private coordinates without a pin-to-target identity condition. -/
theorem pinned_coordinates {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {Response : Type} (collected : Inputs Response)
    (references : References domain collected) :
    dh.dh scalar (peer collected.serverConverted) = some (PqxdhPhase2InputBytes.word (materialize dh scalar collected.first)) ∧
      dh.dh scalar (peer collected.ephemeral) = some (PqxdhPhase2InputBytes.word (materialize dh scalar collected.third)) := by
  constructor
  · rw [references.1]
    exact PqxdhPhase2GapDhInput.selected_value dh domain scalar collected.serverConverted references.2.2.1
  · rw [references.2.1]
    exact PqxdhPhase2GapDhInput.selected_value dh domain scalar collected.ephemeral references.2.2.2

/-- The new private descriptor denotes exactly the actual native source's 192-byte root input. -/
theorem pinned_source {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type} (collected : Inputs Response)
    (references : References domain collected) (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (concreteInputs dh scalar collected).finishInputs.shared_secrets = .ok (.Ok root)) :
    input joint dh seed scalar (pinnedBeaconMessage collected) = some (absBytes root.bytes) := by
  obtain ⟨first, third⟩ := pinned_coordinates dh domain scalar collected references
  have bytes := PqxdhPhase2InputBytes.root_input _ root built
  rw [pinned_input]
  simp only [first, third]
  exact congrArg some bytes.symm

def root (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    OracleComp RootSpec (Option Word32) :=
  Option.map PqxdhRootTableInitialization.rootArray <$>
    (RootSpec.query (.inr (.derive (pinnedBeaconMessage pending.collected))) : OracleComp RootSpec _)

def client (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    OracleComp RootSpec (RustM agreement.AgreementEffect) :=
  RegistrationBeaconRelatedRoot.complete authenticated pending <$> root pending

/-- The source root service executes at the actual root callback and retains its full literal-input cache/history. -/
theorem root_source (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (original : PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (references : References domain pending.collected)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending)
    (before : RegistrationNativeRelatedFamily.State) :
    (simulateQ (sourceImpl source hmac joint dh seed scalar) (root pending)).run before =
      pure (some (RawCtxSourceHkdf.rootResponse source.crypto original.candidate.root_key_input),
        rootState hmac (pinnedBeaconMessage pending.collected) (absBytes original.candidate.root_key_input.bytes) before) := by
  have inputEq := pinned_source dh domain seed scalar pending.collected references
    original.candidate.root_key_input related.2.2.2.2
  simp only [root, simulateQ_map, simulateQ_spec_query, sourceImpl]
  rw [StateT.run_map]
  simp only [sourceRoot, StateT.run, inputEq, map_pure, Option.map_some]
  rfl

abbrev State (Auxiliary : Type) := RegistrationNativeRelatedFamily.State × RawCtxSharedPrimitive.SharedState Auxiliary

def lift {Auxiliary Value : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Value) :
    StateT (State Auxiliary) ProbComp Value := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$> work.run before.2

def familyImpl {Auxiliary : Type} (family : QueryImpl RootSpec (StateT RegistrationNativeRelatedFamily.State ProbComp)) :
    QueryImpl RootSpec (StateT (State Auxiliary) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2, before.2))) <$> (family query).run before.1

def instrument {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State Auxiliary) ProbComp)
  | .root request => fun before => pure
      (.Some (RegistrationAgreementShared.rootResponse source.crypto request),
        (rootState hmac (pinnedBeaconMessage pending.collected) (absBytes request.input) before.1, before.2))
  | request => lift (RegistrationAgreementShared.implementation source primitive request)

private theorem response_root (source : FixedHkdfSha512NoSaltSource) (input : pqxdh.RootKeyInput) :
    RegistrationAgreementShared.rootResponse source.crypto ⟨input.bytes, pqxdh.PQXDH_INFO⟩ =
      RawCtxSourceHkdf.rootResponse source.crypto input := by
  apply Subtype.ext
  simp only [RegistrationAgreementShared.rootResponse, RawCtxSourceHkdf.rootResponse, absBytes_PQXDH_INFO]

theorem root_native {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (authenticated : registration.AuthenticatedResponse)
    (original : PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)
    (before : State Auxiliary) :
    (simulateQ (instrument source hmac primitive pending)
      (RegistrationAgreementExecutor.drive 2 (.RootKdf ⟨.Beacon original.candidate authenticated.pending.binding authenticated.packet.application⟩))).run before =
      pure (.ok (.BeaconComplete ⟨PqxdhBeaconPhase2Publication.clearedCandidate original.candidate,
        authenticated.pending.binding, ⟨RawCtxSourceHkdf.rootResponse source.crypto original.candidate.root_key_input⟩,
        authenticated.packet.application⟩),
        (rootState hmac (pinnedBeaconMessage pending.collected)
          (absBytes original.candidate.root_key_input.bytes) before.1, before.2)) := by
  have requested : (⟨.Beacon original.candidate authenticated.pending.binding authenticated.packet.application⟩ : agreement.RootKdfPending).request =
      .ok ⟨original.candidate.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
    simp only [agreement.RootKdfPending.request, pqxdh.BeaconRegistrationCandidate.impl.root_key_input,
      pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
  rw [RegistrationBeaconRelatedRoot.root_step_two _ _ requested]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change (pure
    ((⟨.Beacon original.candidate authenticated.pending.binding authenticated.packet.application⟩ : agreement.RootKdfPending).resume
      (.Some (RegistrationAgreementShared.rootResponse source.crypto
        ⟨original.candidate.root_key_input.bytes, pqxdh.PQXDH_INFO⟩)),
      (rootState hmac (pinnedBeaconMessage pending.collected)
        (absBytes original.candidate.root_key_input.bytes) before.1, before.2)) :
      ProbComp (RustM agreement.AgreementEffect × State Auxiliary)) = _
  rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines, response_root]
  rfl

/-- The pin-free native root client reconstructs the actual reached controller root step on arbitrary admitted Server pins. -/
theorem client_source {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (original : PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (references : References domain pending.collected)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    simulateQ (familyImpl (sourceImpl source hmac joint dh seed scalar)) (client authenticated pending) =
      simulateQ (instrument source hmac primitive pending)
        (RegistrationAgreementExecutor.drive 2 (.RootKdf ⟨.Beacon original.candidate authenticated.pending.binding authenticated.packet.application⟩)) := by
  funext before
  change (simulateQ (familyImpl (sourceImpl source hmac joint dh seed scalar)) (client authenticated pending)).run before =
    (simulateQ (instrument source hmac primitive pending)
      (RegistrationAgreementExecutor.drive 2 (.RootKdf ⟨.Beacon original.candidate authenticated.pending.binding authenticated.packet.application⟩))).run before
  rw [root_native]
  have inputEq := pinned_source dh domain seed scalar pending.collected references
    original.candidate.root_key_input related.2.2.2.2
  simp only [client, root, simulateQ_map, simulateQ_spec_query]
  rw [StateT.run_map, StateT.run_map]
  simp only [familyImpl, sourceImpl, sourceRoot, StateT.run, inputEq, map_pure, Option.map_some]
  rw [PqxdhPhase2DhMetadata.cleared_related dh scalar original pending related]
  rfl

theorem lift_project {Auxiliary Value : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Value) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (lift work).run before = work.run before.2 := by
  simp only [lift, StateT.run, Functor.map_map, Prod.map, id_eq]
  exact id_map _

theorem instrument_query {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (query : RegistrationAgreementExecutor.Request) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (instrument source hmac primitive pending query).run before =
      (RegistrationAgreementShared.implementation source primitive query).run before.2 := by
  cases query with
  | root request => rw [RegistrationAgreementShared.root_exact]; rfl
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request =>
      exact lift_project _ before

/-- Only private related-input history/cache is projected; every native primitive/World coordinate is retained. -/
theorem instrument_program {Auxiliary Value : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (simulateQ (instrument source hmac primitive pending) work).run before =
      (simulateQ (RegistrationAgreementShared.implementation source primitive) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (instrument_query source hmac primitive pending) work before

end BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.pinned_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.pinned_coordinates

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.pinned_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.pinned_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.root_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.root_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.root_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.lift_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.lift_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.instrument_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.instrument_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.instrument_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource.instrument_program
