-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace

/-! Native shared-state completion retains its actual pre-erasure collector and the very same complete higher query/reply journal. This ties source-supported private Root operands to the original operational encapsulation trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTracedServerInput
open RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationServerEncapsulationTrace (Input entries)
variable {Auxiliary : Type}

/-- Successful actual native completion returns one actual collector support cut and its exact preceding query/reply entries. -/
theorem server (source : FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (journal final : Trace) (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : ((.ok (.ServerComplete completed), final), after) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) journal)).run before)) :
    ∃ (input : Input) (atRoot : RawCtxSharedPrimitive.SharedState Auxiliary)
      (next : pqxdh.ServerState) (original : pqxdh.PendingServerRegistration),
      (some input, atRoot) ∈ support ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (simulateQ RegistrationAgreementRoot.callbacks
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run before) ∧
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding,
        ⟨RegistrationAgreementShared.rootResponse source.crypto ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩⟩ ∧
      after = atRoot ∧
      final = journal ++ entries input ++ [⟨.root ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩,
        .Some (RegistrationAgreementShared.rootResponse source.crypto ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩)⟩] ∧
      absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
        (absBytes input.first) (absBytes input.second) (absBytes input.third)
        (absBytes input.fourth) (absBytes input.kem) := by
  rw [RegistrationAgreementRoot.server_normalized control packet authenticated] at supported
  simp only [RegistrationAgreementRoot.normalized, trace_bind, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨⟨optional, prefixJournal⟩, atRoot⟩, reachedPrefix, tail⟩ := supported
  cases optional with
  | none =>
    simp only [trace_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
    cases tail.1.1
  | some input =>
    change ((.ok (.ServerComplete completed), final), after) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (trace (RegistrationAgreementRoot.finish control authenticated input) prefixJournal)).run atRoot) at tail
    have prefixOpen : (some input, prefixJournal) ∈ support
        (trace (simulateQ RegistrationAgreementRoot.callbacks
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))) journal) := by
      apply OracleComp.support_simulateQ_run'_subset (RegistrationAgreementShared.implementation source primitive) _ before
      rw [StateT.run'_eq, support_map]
      exact ⟨_, reachedPrefix, rfl⟩
    rw [RegistrationServerEncapsulationTrace.prefix_exact] at prefixOpen
    obtain ⟨verified, journalEq⟩ := RegistrationServerEncapsulationTrace.collector_success _ input journal prefixJournal prefixOpen
    have collected : (some input, atRoot) ∈ support ((simulateQ (RegistrationAgreementShared.implementation source primitive)
        (simulateQ RegistrationAgreementRoot.callbacks
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run before) := by
      have erased := congrArg (fun work => (simulateQ (RegistrationAgreementShared.implementation source primitive) work).run before)
        (RegistrationAgreementQueryTrace.erasure (simulateQ RegistrationAgreementRoot.callbacks
          (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))) journal)
      simp only [simulateQ_map, StateT.run_map] at erased
      rw [← erased, support_map]
      exact ⟨_, reachedPrefix, rfl⟩
    have credential : PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys = authenticated.registration := by
      rw [verified]
      exact RegistrationRootInput.verified_native packet authenticated
    rw [RegistrationAgreementFinish.finish_source control authenticated input credential] at tail
    obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control
      (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) .Fresh
      authenticated.binding.server_pin.binding ⟨input.ephemeral.publicKey, input.ciphertext⟩ (PqxdhServerRelatedRootInput.secrets input)
    have actual : PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok accepted := acceptedRun
    cases accepted with
    | Err error =>
      simp only [RegistrationAgreementFinish.finishSource, actual, continueWith, trace_pure,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
      cases tail.1.1
    | Ok result =>
      rcases result with ⟨next, original⟩
      simp only [RegistrationAgreementFinish.finishSource, actual, continueWith] at tail
      have requested : (⟨.Server original authenticated.binding⟩ : agreement.RootKdfPending).request =
          .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
        simp only [agreement.RootKdfPending.request, pqxdh.PendingServerRegistration.impl.root_key_input,
          pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
      rw [RegistrationAgreementFinish.root_step _ _ requested] at tail
      simp only [trace_query_bind, simulateQ_bind, simulateQ_spec_query,
        RegistrationAgreementShared.root_exact, StateT.run_bind, pure_bind, trace_pure,
        simulateQ_pure, StateT.run_pure, BeaconcryptCore.Refinement.KeyAgreement.root_success_refines,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq,
        agreement.AgreementEffect.ServerComplete.injEq] at tail
      exact ⟨input, atRoot, next, original, collected, verified, actual, tail.1.1, tail.2,
        by rw [tail.1.2, journalEq],
        RegistrationNativeAgreementInputReceipt.server_bytes control next _ input original actual⟩

end BeaconcryptCore.Computational.RegistrationNativeTracedServerInput

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTracedServerInput.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTracedServerInput.server
