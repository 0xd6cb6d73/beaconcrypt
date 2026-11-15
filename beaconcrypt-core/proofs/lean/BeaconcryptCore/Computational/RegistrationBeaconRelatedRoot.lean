-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRootPreparation
import BeaconcryptCore.Computational.RegistrationRootStage

/-! The Beacon's related-DH root client returns the actual cleared native agreement capability and retains its authenticated binding and original application slice. The source interpretation uses the existing real-family root address theorem, including both selected prekey coordinates and all primitive state. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot

open RegistrationAgreementExecutor
open PqxdhJointIdentity PqxdhJointGapDh PqxdhJointDhExtractRoot
open PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhServerRelatedRootConsumer (State)

theorem root_step_two (pending : agreement.RootKdfPending) (request : agreement.RootKdfRequest)
    (requested : pending.request = .ok request) :
    drive 2 (.RootKdf pending) = (do
      let reply ← (Spec.query (.root request) : OracleComp Spec _)
      pure (pending.resume reply)) := by
  rw [drive]
  simp only [step, requested, continueWith, bind_assoc, pure_bind]
  congr 1
  funext reply
  cases reply with
  | none =>
      rw [BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines]
      cases pending.candidate <;> rfl
  | some root =>
      rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines]
      cases pending.candidate <;> rfl

def rootReceipt {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (publicValue : PublicChallenge)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (request : agreement.RootKdfRequest) :
    StateT (State (RawCtxSharedPrimitive.SharedState Auxiliary)) ProbComp (core.option.Option Word32) := fun before =>
  pure (.Some (RegistrationAgreementShared.rootResponse source.crypto request),
    (rootState hmac (beaconMessage publicValue pending.collected) (absBytes request.input) before.1, before.2))

def instrument {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (publicValue : PublicChallenge) (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    QueryImpl Spec (StateT (State (RawCtxSharedPrimitive.SharedState Auxiliary)) ProbComp)
  | .root request => rootReceipt source hmac publicValue pending request
  | request => RegistrationRootStage.lift (RegistrationAgreementShared.implementation source primitive request)

theorem instrument_query {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (publicValue : PublicChallenge) (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (query : RegistrationAgreementExecutor.Request) (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$> (instrument source hmac primitive publicValue pending query).run before =
      (RegistrationAgreementShared.implementation source primitive query).run before.2 := by
  cases query with
  | root request =>
      rw [RegistrationAgreementShared.root_exact]
      rfl
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request =>
      exact RegistrationRootStage.lift_project _ before

theorem instrument_program {Auxiliary Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (publicValue : PublicChallenge) (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (work : OracleComp Spec Result) (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$> (simulateQ (instrument source hmac primitive publicValue pending) work).run before =
      (simulateQ (RegistrationAgreementShared.implementation source primitive) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (instrument_query source hmac primitive publicValue pending) work before

def complete (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    Option Word32 → RustM agreement.AgreementEffect
  | none => .ok (RegistrationBeaconAgreementRoot.rejected authenticated)
  | some root => .ok (.BeaconComplete
      ⟨PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata, authenticated.binding,
        ⟨root⟩, authenticated.packet.application⟩)

def client (publicValue : PublicChallenge) (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) :
    OracleComp RootSpec (RustM agreement.AgreementEffect) :=
  complete authenticated pending <$> PqxdhPhase2DhRootConsumer.root publicValue pending

private theorem response_root (source : FixedHkdfSha512NoSaltSource) (input : pqxdh.RootKeyInput) :
    RegistrationAgreementShared.rootResponse source.crypto ⟨input.bytes, pqxdh.PQXDH_INFO⟩ =
      RawCtxSourceHkdf.rootResponse source.crypto input := by
  apply Subtype.ext
  simp only [RegistrationAgreementShared.rootResponse, RawCtxSourceHkdf.rootResponse, absBytes_PQXDH_INFO]

theorem root_native {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (publicValue : PublicChallenge) (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (authenticated : registration.AuthenticatedResponse)
    (original : PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    (simulateQ (instrument source hmac primitive publicValue pending)
      (drive 2 (.RootKdf ⟨.Beacon original.candidate authenticated.binding authenticated.packet.application⟩))).run before =
      pure (.ok (.BeaconComplete ⟨PqxdhBeaconPhase2Publication.clearedCandidate original.candidate,
        authenticated.binding, ⟨RawCtxSourceHkdf.rootResponse source.crypto original.candidate.root_key_input⟩,
        authenticated.packet.application⟩),
        (rootState hmac (beaconMessage publicValue pending.collected)
          (absBytes original.candidate.root_key_input.bytes) before.1, before.2)) := by
  have requested : (⟨.Beacon original.candidate authenticated.binding authenticated.packet.application⟩ : agreement.RootKdfPending).request =
      .ok ⟨original.candidate.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
    simp only [agreement.RootKdfPending.request, pqxdh.BeaconRegistrationCandidate.impl.root_key_input,
      pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
  rw [root_step_two _ _ requested]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change (pure
    ((⟨.Beacon original.candidate authenticated.binding authenticated.packet.application⟩ : agreement.RootKdfPending).resume
      (.Some (RegistrationAgreementShared.rootResponse source.crypto
        ⟨original.candidate.root_key_input.bytes, pqxdh.PQXDH_INFO⟩)),
      (rootState hmac (beaconMessage publicValue pending.collected)
        (absBytes original.candidate.root_key_input.bytes) before.1, before.2)) :
      ProbComp (RustM agreement.AgreementEffect × State (RawCtxSharedPrimitive.SharedState Auxiliary))) = _
  rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines, response_root]
  rfl

theorem client_source {Auxiliary : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (original : PqxdhBeaconPhase2Preparation.Prepared registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (references : PqxdhPhase2GapDhSource.References domain pending.collected)
    (converted : PqxdhPhase2GapDhSource.peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    simulateQ (PqxdhPhase2DhRootConsumer.familyImpl (A := RawCtxSharedPrimitive.SharedState Auxiliary)
        (sourceImpl source hmac joint dh seed scalar))
      (client (challenge joint dh seed scalar) authenticated pending) =
      simulateQ (instrument source hmac primitive (challenge joint dh seed scalar) pending)
        (drive 2 (.RootKdf ⟨.Beacon original.candidate authenticated.binding authenticated.packet.application⟩)) := by
  funext before
  change (simulateQ (PqxdhPhase2DhRootConsumer.familyImpl (A := RawCtxSharedPrimitive.SharedState Auxiliary)
        (sourceImpl source hmac joint dh seed scalar))
      (client (challenge joint dh seed scalar) authenticated pending)).run before =
    (simulateQ (instrument source hmac primitive (challenge joint dh seed scalar) pending)
      (drive 2 (.RootKdf ⟨.Beacon original.candidate authenticated.binding authenticated.packet.application⟩))).run before
  simp only [client, simulateQ_map, StateT.run_map]
  rw [PqxdhPhase2DhRootConsumer.root_complete source hmac dh domain seed scalar original pending references converted related]
  rw [root_native]
  simp only [PqxdhPhase2DhRootConsumer.nativeRootReply, StateT.run, map_pure, complete]
  rw [PqxdhPhase2DhMetadata.cleared_related dh scalar original pending related]

end BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.root_step_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.root_step_two

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.instrument_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.instrument_query

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.instrument_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.instrument_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.root_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.root_native

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot.client_source
