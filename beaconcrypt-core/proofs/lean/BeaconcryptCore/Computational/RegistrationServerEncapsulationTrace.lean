-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
import BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace
open RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace
open PqxdhServerRootPreparation (Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)

abbrev Input := Inputs registration.InitPacket Unit Word32

def collector (verified : Verified registration.InitPacket) : OracleComp Spec (Option Input) := do
  let ephemeral ← Spec.query (.generate .ServerEphemeral)
  match ephemeral with
  | .None => pure none
  | .Some ephemeral =>
    let encapsulated ← Spec.query (.encapsulate (.Some (RegistrationAgreementRoot.pqArray verified.keys.pqKey)))
    match encapsulated with
    | .None => pure none
    | .Some encapsulated =>
      let converted ← Spec.query (.convertPublic (PqxdhRootTableInitialization.rootArray verified.identity))
      match converted with
      | .None => pure none
      | .Some converted =>
        let privateConverted ← Spec.query (.convertSecret .LocalIdentity)
        if !privateConverted then pure none else do
          let first ← Spec.query (.dh ⟨.LocalIdentity, PqxdhRootTableInitialization.rootArray verified.keys.prekey⟩)
          match first with
          | .None => pure none
          | .Some first =>
            let second ← Spec.query (.dh ⟨.ServerEphemeral, converted⟩)
            match second with
            | .None => pure none
            | .Some second =>
              let third ← Spec.query (.dh ⟨.ServerEphemeral, PqxdhRootTableInitialization.rootArray verified.keys.prekey⟩)
              match third with
              | .None => pure none
              | .Some third =>
                let fourth ← Spec.query (.dh ⟨.ServerEphemeral, PqxdhRootTableInitialization.rootArray verified.keys.oneTime⟩)
                match fourth with
                | .None => pure none
                | .Some fourth => pure (some ⟨verified, ⟨(), ephemeral⟩, encapsulated.1,
                    converted, first, second, third, fourth, encapsulated.2⟩)

/-- The collector is the same eight actual primitive queries with every optional exit retained. -/
theorem prefix_exact (verified : Verified registration.InitPacket) :
    simulateQ RegistrationAgreementRoot.callbacks (PqxdhServerRootPreparation.collectVerified verified) = collector verified := by
  simp only [PqxdhServerRootPreparation.collectVerified, OptionT.run_bind, OptionT.run_monadLift,
    OptionT.run_mk, Option.elimM, bind_map_left, simulateQ_bind, simulateQ_spec_query,
    RegistrationAgreementRoot.callbacks, pure_bind, Bool.not_true, Bool.false_eq_true,
    ite_false, Option.elim_some, collector, bind_pure_comp]
  repeat' first
    | rfl
    | (simp only [OptionT.run_bind, OptionT.run_monadLift, OptionT.run_mk, OptionT.run_map,
        Option.elimM, Option.elim_some, simulateQ_bind, simulateQ_map, simulateQ_spec_query,
        RegistrationAgreementRoot.callbacks, bind_map_left, pure_bind,
        RegistrationAgreementRoot.option, Option.map_some, Bool.not_true, Bool.false_eq_true, ite_false])
    | (congr 1; funext reply; cases reply)
    | (rw [Functor.map_map, map_eq_bind_pure_comp]; congr 1; funext reply; cases reply <;> rfl)

/-- The exact successful collector journal, including the actual encapsulation result before its use in the root. -/
def entries (input : Input) : Trace :=
  [⟨.generate .ServerEphemeral, .Some input.ephemeral.publicKey⟩,
   ⟨.encapsulate (.Some (RegistrationAgreementRoot.pqArray input.verified.keys.pqKey)),
     .Some (input.ciphertext, input.kem)⟩,
   ⟨.convertPublic (PqxdhRootTableInitialization.rootArray input.verified.identity), .Some input.convertedIdentity⟩,
   ⟨.convertSecret .LocalIdentity, true⟩,
   ⟨.dh ⟨.LocalIdentity, PqxdhRootTableInitialization.rootArray input.verified.keys.prekey⟩, .Some input.first⟩,
   ⟨.dh ⟨.ServerEphemeral, input.convertedIdentity⟩, .Some input.second⟩,
   ⟨.dh ⟨.ServerEphemeral, PqxdhRootTableInitialization.rootArray input.verified.keys.prekey⟩, .Some input.third⟩,
   ⟨.dh ⟨.ServerEphemeral, PqxdhRootTableInitialization.rootArray input.verified.keys.oneTime⟩, .Some input.fourth⟩]

/-- A successful collector returns its literal ordered primitive query/reply journal. -/
theorem collector_success (verified : Verified registration.InitPacket) (input : Input)
    (journal after : Trace)
    (supported : (some input, after) ∈ support (trace (collector verified) journal)) :
    input.verified = verified ∧ after = journal ++ entries input := by
  simp only [collector, trace_query_bind, mem_support_bind_iff] at supported
  obtain ⟨ephemeral, _, tail⟩ := supported
  cases ephemeral with
  | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
  | some ephemeral =>
    simp only [trace_query_bind, mem_support_bind_iff] at tail
    obtain ⟨encapsulated, _, tail⟩ := tail
    cases encapsulated with
    | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
    | some encapsulated =>
      simp only [trace_query_bind, mem_support_bind_iff] at tail
      obtain ⟨converted, _, tail⟩ := tail
      cases converted with
      | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
      | some converted =>
        simp only [trace_query_bind, mem_support_bind_iff] at tail
        obtain ⟨privateConverted, _, tail⟩ := tail
        cases privateConverted with
        | false => simp only [Bool.not_false, ite_true, trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false, trace_query_bind, mem_support_bind_iff] at tail
          obtain ⟨first, _, tail⟩ := tail
          cases first with
          | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
          | some first =>
            simp only [trace_query_bind, mem_support_bind_iff] at tail
            obtain ⟨second, _, tail⟩ := tail
            cases second with
            | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
            | some second =>
              simp only [trace_query_bind, mem_support_bind_iff] at tail
              obtain ⟨third, _, tail⟩ := tail
              cases third with
              | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
              | some third =>
                simp only [trace_query_bind, mem_support_bind_iff] at tail
                obtain ⟨fourth, _, tail⟩ := tail
                cases fourth with
                | none => simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail; cases tail.1
                | some fourth =>
                  simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at tail
                  rcases tail with ⟨rfl, rfl⟩
                  exact ⟨rfl, by simp only [entries, List.append_assoc, List.cons_append, List.nil_append]⟩

/-- A successful Server completion contains one exact collector prefix followed by the root query using that prefix's actual encapsulation secret. Both replies belong to the same operational tree. -/
theorem server (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (journal after : Trace)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) journal)) :
    ∃ (input : Input) (next : pqxdh.ServerState) (original : pqxdh.PendingServerRegistration)
      (reply : Word32),
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding, ⟨reply⟩⟩ ∧
      after = journal ++ entries input ++
        [⟨.root ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩, .Some reply⟩] ∧
      absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
        (absBytes input.first) (absBytes input.second) (absBytes input.third)
        (absBytes input.fourth) (absBytes input.kem) := by
  rw [RegistrationAgreementRoot.server_normalized control packet authenticated] at supported
  simp only [RegistrationAgreementRoot.normalized, trace_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨optional, atRoot⟩, prefixRun, tail⟩ := supported
  cases optional with
  | none =>
    simp only [trace_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
    cases tail.1
  | some input =>
    change (.ok (.ServerComplete completed), after) ∈ support
      (trace (RegistrationAgreementRoot.finish control authenticated input) atRoot) at tail
    rw [prefix_exact] at prefixRun
    obtain ⟨verified, prefixJournal⟩ := collector_success _ input journal atRoot prefixRun
    have credential : PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys =
        authenticated.registration := by
      rw [verified]
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
      simp only [RegistrationAgreementFinish.finishSource, actual, continueWith, trace_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
      cases tail.1
    | Ok result =>
      rcases result with ⟨next, original⟩
      simp only [RegistrationAgreementFinish.finishSource, actual, continueWith] at tail
      have requested : (⟨.Server original authenticated.binding⟩ : agreement.RootKdfPending).request =
          .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
        simp only [agreement.RootKdfPending.request, pqxdh.PendingServerRegistration.impl.root_key_input,
          pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
      rw [RegistrationAgreementFinish.root_step _ _ requested] at tail
      simp only [trace_query_bind, mem_support_bind_iff] at tail
      obtain ⟨reply, _, tail⟩ := tail
      cases reply with
      | none =>
        simp only [trace_pure, BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
        cases tail.1
      | some reply =>
        simp only [trace_pure, BeaconcryptCore.Refinement.KeyAgreement.root_success_refines,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq,
          agreement.AgreementEffect.ServerComplete.injEq] at tail
        exact ⟨input, next, original, reply, verified, actual, tail.1,
          by rw [tail.2, prefixJournal],
          RegistrationNativeAgreementInputReceipt.server_bytes control next _ input original actual⟩

/-- Any actual stateful interpreter's successful traced run supplies the same literal prefix and root association. The interpreter and every private poststate remain arbitrary. -/
theorem interpreted {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp))
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (journal after : Trace) (before afterState : State)
    (supported : ((.ok (.ServerComplete completed), after), afterState) ∈ support
      ((simulateQ implementation (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) journal)).run before)) :
    ∃ (input : Input) (next : pqxdh.ServerState) (original : pqxdh.PendingServerRegistration)
      (reply : Word32),
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding, ⟨reply⟩⟩ ∧
      after = journal ++ entries input ++
        [⟨.root ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩, .Some reply⟩] ∧
      absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
        (absBytes input.first) (absBytes input.second) (absBytes input.third)
        (absBytes input.fourth) (absBytes input.kem) := by
  apply server control packet authenticated completed journal after
  apply OracleComp.support_simulateQ_run'_subset implementation
    (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) journal) before
  rw [StateT.run'_eq, support_map]
  exact ⟨((.ok (.ServerComplete completed), after), afterState), supported, rfl⟩

end BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.prefix_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.prefix_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.collector_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.collector_success

/-- info: 'BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.server

/-- info: 'BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerEncapsulationTrace.interpreted
