-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace
import BeaconcryptCore.Computational.RegistrationNativeRecipientLog
import BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily

/-! A completed actual Server root uses a recipient-correct same-run encapsulation coordinate unless the actual counted capability marker has fired. The higher trace is derived by lossless instrumentation of the actual lower logged execution; no trace or root association is supplied by the caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedRecipientSample (Draw)
open RegistrationNativeKemServerState (State)
open RegistrationNativeKemCountedRecipientFamily (AnyBad)
variable {n count : Nat} {ι KemSK Service : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK
local notation "Client" => State n source

/-- Every generated family row matching the actual Server recipient key has the correct functional decapsulation coordinate, or the very same lower execution's sticky marker is set. Failed replies and the complete private service state remain in the computation. -/
theorem server (setup : Setup base KemSK) (checks : Checks)
    (functional : FunctionalDecapsulation setup.kem)
    (rows : Fin count → Draw KemSK)
    (implementation : QueryImpl CP (StateT Service ProbComp))
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (before after : Client) (beforeService afterService : Service) (flag : Bool)
    (log : RegistrationNativeKemCountedServerTrace.Log KemSK)
    (supported : (((.ok (.ServerComplete completed), after), log), (afterService, flag)) ∈ support
      ((simulateQ (RegistrationNativeRecipientQueryBound.handler implementation (AnyBad setup functional rows))
        ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
          (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before).withQueryLog).run (beforeService, false))) :
    ∃ (input : RegistrationServerEncapsulationTrace.Input) (next : pqxdh.ServerState)
      (original : pqxdh.PendingServerRegistration) (reply : PqxdhBeaconPhase2Preparation.Word32) (cost : Nat),
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding, ⟨reply⟩⟩ ∧
      absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
        (absBytes input.first) (absBytes input.second) (absBytes input.third)
        (absBytes input.fourth) (absBytes input.kem) ∧
      (⟨.inr (.inr input.verified.keys.pqKey),
        ((PqxdhPhase2InputBytes.ciphertext input.ciphertext, PqxdhPhase2InputBytes.word input.kem), cost)⟩) ∈ log ∧
      ∀ target, (rows target).1.1 = input.verified.keys.pqKey →
        functional.result (rows target).1.2 (PqxdhPhase2InputBytes.ciphertext input.ciphertext) =
          some (PqxdhPhase2InputBytes.word input.kem) ∨ flag = true := by
  let work := (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
    (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before
  have openRun : ((.ok (.ServerComplete completed), after), log) ∈ support work.withQueryLog := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeRecipientQueryBound.handler implementation (AnyBad setup functional rows))
      work.withQueryLog (beforeService, false)
    rw [StateT.run'_eq, support_map]
    exact ⟨_, supported, rfl⟩
  obtain ⟨journal, traced⟩ := RegistrationAgreementMacroTrace.lift_support
    (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
    (RegistrationAgreementExecutor.server control .Fresh authenticated) before after
    (.ok (.ServerComplete completed)) log openRun
  obtain ⟨input, next, original, reply, cost, verified, accepted, complete, _journal, bytes, actual⟩ :=
    RegistrationNativeKemCountedServerTrace.server setup checks representation created control packet authenticated
      completed journal before after log traced
  have marker := RegistrationNativeRecipientLog.sound implementation (AnyBad setup functional rows)
    work (beforeService, false) (.ok (.ServerComplete completed), after) log (afterService, flag) supported
  refine ⟨input, next, original, reply, cost, verified, accepted, complete, bytes, actual, ?_⟩
  intro target key
  by_cases correct : functional.result (rows target).1.2 (PqxdhPhase2InputBytes.ciphertext input.ciphertext) =
      some (PqxdhPhase2InputBytes.word input.kem)
  · exact Or.inl correct
  · apply Or.inr
    apply marker.2 _ actual
    refine ⟨target, ?_⟩
    simp only [RegistrationNativeKemCountedRecipient.Bad, key, true_and]
    exact correct

/-- The actual replay-scheduled Server agreement derives freshness from successful completion and uses the same counted failure marker. -/
theorem agree (setup : Setup base KemSK) (checks : Checks)
    (functional : FunctionalDecapsulation setup.kem)
    (rows : Fin count → Draw KemSK)
    (implementation : QueryImpl CP (StateT Service ProbComp))
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (before after : Client) (beforeService afterService : Service) (flag : Bool)
    (log : RegistrationNativeKemCountedServerTrace.Log KemSK)
    (supported : (((.ok (.ServerComplete completed), after), log), (afterService, flag)) ∈ support
      ((simulateQ (RegistrationNativeRecipientQueryBound.handler implementation (AnyBad setup functional rows))
        ((RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated).run before).withQueryLog).run (beforeService, false))) :
    ∃ (input : RegistrationServerEncapsulationTrace.Input) (next : pqxdh.ServerState)
      (original : pqxdh.PendingServerRegistration) (reply : PqxdhBeaconPhase2Preparation.Word32) (cost : Nat),
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept before.server.control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding, ⟨reply⟩⟩ ∧
      absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
        (absBytes input.first) (absBytes input.second) (absBytes input.third)
        (absBytes input.fourth) (absBytes input.kem) ∧
      (⟨.inr (.inr input.verified.keys.pqKey),
        ((PqxdhPhase2InputBytes.ciphertext input.ciphertext, PqxdhPhase2InputBytes.word input.kem), cost)⟩) ∈ log ∧
      ∀ target, (rows target).1.1 = input.verified.keys.pqKey →
        functional.result (rows target).1.2 (PqxdhPhase2InputBytes.ciphertext input.ciphertext) =
          some (PqxdhPhase2InputBytes.word input.kem) ∨ flag = true := by
  simp only [RegistrationNativeKemCountedServerPrimitive.agree, StateT.run_bind,
    StateT.run_get, pure_bind, RegistrationReplaySchedule.begin_eq] at supported
  cases consumed : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) with
  | false =>
    simp only [consumed, Bool.false_eq_true, ite_false] at supported
    exact server setup checks functional rows implementation representation created before.server.control packet authenticated
      completed before after beforeService afterService flag log supported
  | true =>
    simp only [consumed, ite_true, simulateQ_pure, StateT.run_pure, withQueryLog_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1.1.1

end BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker.agree
