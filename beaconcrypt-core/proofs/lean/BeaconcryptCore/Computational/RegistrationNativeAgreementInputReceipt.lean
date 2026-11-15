-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRelatedRoot

/-! Supported source agreement completion retains an actual ordered private prefix and the exact root candidate before its input is cleared. These are analysis receipts for the existing computation, not public observations or a premise equating peer root inputs. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt

open RegistrationAgreementExecutor
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)

variable {Auxiliary : Type}

/-- Root execution returns the source HKDF result while retaining the complete pre-root native state. -/
theorem root_source (source : FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (pending : agreement.RootKdfPending) (request : agreement.RootKdfRequest)
    (requested : pending.request = .ok request)
    (before : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationAgreementShared.implementation source primitive)
      (drive 1 (.RootKdf pending))).run before =
      pure (pending.resume (.Some (RegistrationAgreementShared.rootResponse source.crypto request)), before) := by
  rw [RegistrationAgreementFinish.root_step pending request requested]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    RegistrationAgreementShared.root_exact, pure_bind, StateT.run_pure]

/-- A successful Server execution contains a genuinely reached private collector result and its source pre-erasure acceptance, rather than reconstructed private inputs. -/
theorem server (source : FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before)) :
    ∃ (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
      (atRoot : RawCtxSharedPrimitive.SharedState Auxiliary)
      (next : pqxdh.ServerState) (original : pqxdh.PendingServerRegistration),
      (some input, atRoot) ∈ support ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (simulateQ RegistrationAgreementRoot.callbacks
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run before) ∧
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ },
        authenticated.binding, ⟨RegistrationAgreementShared.rootResponse source.crypto
          ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩⟩ ∧ after = atRoot := by
  rw [RegistrationAgreementRoot.server_normalized control packet authenticated] at supported
  simp only [RegistrationAgreementRoot.normalized, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨input, atRoot⟩, reachedPrefix, tail⟩ := supported
  cases input with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at tail
      cases tail.1
  | some input =>
      change (.ok (.ServerComplete completed), after) ∈ support
        ((simulateQ (RegistrationAgreementShared.implementation source primitive)
          (RegistrationAgreementRoot.finish control authenticated input)).run atRoot) at tail
      have openPrefix : some input ∈ support
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) := by
        apply OracleComp.support_simulateQ_run'_subset
          ((RegistrationAgreementShared.implementation source primitive) ∘ₛ RegistrationAgreementRoot.callbacks)
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) before
        rw [StateT.run'_eq, support_map]
        refine ⟨(some input, atRoot), ?_, rfl⟩
        simpa only [QueryImpl.simulateQ_compose] using reachedPrefix
      have fields := RegistrationRootInput.collected_verified
        (RegistrationRootInput.verified packet authenticated) input openPrefix
      have credential : PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys =
          authenticated.registration := by
        rw [fields]
        exact RegistrationRootInput.verified_native packet authenticated
      rw [RegistrationAgreementFinish.finish_source control authenticated input credential] at tail
      obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control
        (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) .Fresh
        authenticated.binding.server_pin.binding ⟨input.ephemeral.publicKey, input.ciphertext⟩
        (PqxdhServerRelatedRootInput.secrets input)
      have actual : PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input =
          .ok accepted := acceptedRun
      cases accepted with
      | Err error =>
          simp only [RegistrationAgreementFinish.finishSource, actual, continueWith,
            simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at tail
          cases tail.1
      | Ok result =>
          rcases result with ⟨next, original⟩
          simp only [RegistrationAgreementFinish.finishSource, actual, continueWith] at tail
          have requested : (⟨.Server original authenticated.binding⟩ : agreement.RootKdfPending).request =
              .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
            simp only [agreement.RootKdfPending.request, pqxdh.PendingServerRegistration.impl.root_key_input,
              pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
          rw [root_source source primitive _ _ requested atRoot,
            BeaconcryptCore.Refinement.KeyAgreement.root_success_refines] at tail
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            RustM.ok.injEq, agreement.AgreementEffect.ServerComplete.injEq] at tail
          exact ⟨input, atRoot, next, original, reachedPrefix, fields, actual, tail.1, tail.2⟩

/-- Every accepted Server root input is the result of the original checked builder on the five retained source replies. -/
theorem server_built (control next : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
    (original : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding input = .ok (.Ok (next, original))) :
    next = control ∧ pqxdh.build_root_key_input (PqxdhServerRelatedRootInput.secrets input) =
      .ok (.Ok original.root_key_input) := by
  obtain ⟨rootResult, identifier, built, _identified, shape⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.server_fresh_acceptance_shape control
      (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) binding
      ⟨input.ephemeral.publicKey, input.ciphertext⟩ (PqxdhServerRelatedRootInput.secrets input)
  change pqxdh.server_accept control _ .Fresh binding _ _ = _ at accepted
  rw [shape] at accepted
  cases rootResult with
  | Err error => cases accepted
  | Ok root =>
      cases accepted
      exact ⟨rfl, built⟩

/-- The Server's pre-erasure bytes contain precisely its four ordered actual DH replies and actual encapsulation reply. -/
theorem server_bytes (control next : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
    (original : pqxdh.PendingServerRegistration)
    (accepted : PqxdhServerRelatedRootInput.accept control binding input = .ok (.Ok (next, original))) :
    absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
      (absBytes input.first) (absBytes input.second) (absBytes input.third)
      (absBytes input.fourth) (absBytes input.kem) := by
  simpa only [PqxdhServerRelatedRootInput.secrets, PqxdhHiddenRoot.hiddenRootIKM,
    PqxdhPhase2InputBytes.coordinates, PqxdhPhase2InputBytes.word, List.Vector.toList_mk] using
    PqxdhPhase2InputBytes.root_input (PqxdhServerRelatedRootInput.secrets input)
      original.root_key_input (server_built control next binding input original accepted).2

/-- The successful Beacon has its genuinely reached collector, exact public fields, and pre-erasure root candidate with the source HKDF result. -/
theorem beacon (source : FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (completed : agreement.BeaconAgreement) (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : (.ok (.BeaconComplete completed), after) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (RegistrationAgreementExecutor.beacon authenticated)).run before)) :
    ∃ (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
      (atRoot : RawCtxSharedPrimitive.SharedState Auxiliary) (original : pqxdh.BeaconRegistrationCandidate),
      (some input, atRoot) ∈ support ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
          (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before) ∧
      RegistrationBeaconRootPreparation.Fields authenticated input ∧
      pqxdh.beacon_prepare_finish authenticated.control input.finishInputs = .ok (.Ok original) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ },
        authenticated.binding, ⟨RegistrationAgreementShared.rootResponse source.crypto
          ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩, authenticated.packet.application⟩ ∧ after = atRoot := by
  rw [RegistrationBeaconAgreementRoot.beacon_normalized authenticated coherent] at supported
  simp only [RegistrationBeaconAgreementRoot.normalized, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨input, atRoot⟩, reachedPrefix, tail⟩ := supported
  cases input with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at tail
      cases tail.1
  | some input =>
      change (.ok (.BeaconComplete completed), after) ∈ support
        ((simulateQ (RegistrationAgreementShared.implementation source primitive)
          (RegistrationBeaconAgreementRoot.finish authenticated input)).run atRoot) at tail
      have openPrefix : some input ∈ support
          (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
            (PqxdhBeaconPhase2Preparation.collect () false true () [])) := by
        apply OracleComp.support_simulateQ_run'_subset
          (RegistrationAgreementShared.implementation source primitive)
          (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
            (PqxdhBeaconPhase2Preparation.collect () false true () [])) before
        rw [StateT.run'_eq, support_map]
        exact ⟨(some input, atRoot), reachedPrefix, rfl⟩
      have fields := RegistrationBeaconRootPreparation.collect_fields authenticated input openPrefix
      rw [RegistrationBeaconAgreementRoot.finish,
        RegistrationBeaconRootPreparation.finish_admission authenticated input fields] at tail
      obtain ⟨accepted, actual⟩ := BeaconcryptCore.PanicFreedom.beacon_prepare_finish_ok
        authenticated.control input.finishInputs
      rw [actual] at tail
      cases accepted with
      | Err error =>
          simp only [bind_tc_ok, continueWith, RegistrationBeaconAgreementRoot.rejected,
            drive, step, pure_bind, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
          cases tail.1
      | Ok original =>
          simp only [bind_tc_ok, continueWith] at tail
          have requested : (⟨.Beacon original authenticated.binding authenticated.packet.application⟩ : agreement.RootKdfPending).request =
              .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
            simp only [agreement.RootKdfPending.request, pqxdh.BeaconRegistrationCandidate.impl.root_key_input,
              pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
          rw [RegistrationBeaconRelatedRoot.root_step_two _ _ requested] at tail
          simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
            RegistrationAgreementShared.root_exact, pure_bind, StateT.run_pure,
            BeaconcryptCore.Refinement.KeyAgreement.root_success_refines, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq,
            agreement.AgreementEffect.BeaconComplete.injEq] at tail
          exact ⟨input, atRoot, original, reachedPrefix, fields, actual, tail.1, tail.2⟩

/-- The Beacon's pre-erasure bytes contain precisely its four ordered actual DH replies and actual decapsulation reply. -/
theorem beacon_bytes (control : pqxdh.BeaconInitSent)
    (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
    (original : pqxdh.BeaconRegistrationCandidate)
    (accepted : pqxdh.beacon_prepare_finish control input.finishInputs = .ok (.Ok original)) :
    absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
      (absBytes input.finishInputs.shared_secrets.dh1) (absBytes input.finishInputs.shared_secrets.dh2)
      (absBytes input.finishInputs.shared_secrets.dh3) (absBytes input.finishInputs.shared_secrets.dh4)
      (absBytes input.finishInputs.shared_secrets.kem_shared_secret) := by
  have built := (BeaconcryptCore.Refinement.PqxdhSurface.beacon_prepare_finish_success_shape
    control input.finishInputs original accepted).2.2.2
  simpa only [PqxdhHiddenRoot.hiddenRootIKM, PqxdhPhase2InputBytes.coordinates,
    PqxdhPhase2InputBytes.word, List.Vector.toList_mk] using
    PqxdhPhase2InputBytes.root_input input.finishInputs.shared_secrets original.root_key_input built

end BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.root_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.server_built' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.server_built

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.server_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.server_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.beacon_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt.beacon_bytes
