-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementMacroTrace
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource

/-! The actual Server agreement's complete higher request/reply trace is attributed to the literal counted indexed capability log of that same execution. Each successful typed encapsulation reply carries its original private draw-cost receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace (Trace Entry trace)
open RegistrationNativeKemServerState (State)
variable {Value : Type} {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
abbrev Log (KemSK : Type) := (RegistrationNativeKemCountedProgram.Spec KemSK).QueryLog
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK
local notation "Client" => State n source

/-- A successful high-level encapsulation names the exact raw ciphertext, secret and draw count in the lower log. -/
def Receipt (entry : Entry) (log : Log KemSK) : Prop :=
  match entry with
  | ⟨.encapsulate (.Some key), .Some (ciphertext, secret)⟩ =>
    ∃ cost, (⟨.inr (.inr (RegistrationRootInput.pqKey key)),
      ((PqxdhPhase2InputBytes.ciphertext ciphertext, PqxdhPhase2InputBytes.word secret), cost)⟩) ∈ log
  | _ => True

private theorem receipt_left (entry : Entry) (first second : Log KemSK)
    (receipt : Receipt entry first) : Receipt entry (first ++ second) := by
  rcases entry with ⟨query, reply⟩
  cases query <;> try trivial
  rename_i key
  cases key with
  | none => trivial
  | some key =>
    cases reply with
    | none => trivial
    | some pair =>
      obtain ⟨cost, member⟩ := receipt
      exact ⟨cost, List.mem_append_left _ member⟩

private theorem receipt_right (entry : Entry) (first second : Log KemSK)
    (receipt : Receipt entry second) : Receipt entry (first ++ second) := by
  rcases entry with ⟨query, reply⟩
  cases query <;> try trivial
  rename_i key
  cases key with
  | none => trivial
  | some key =>
    cases reply with
    | none => trivial
    | some pair =>
      obtain ⟨cost, member⟩ := receipt
      exact ⟨cost, List.mem_append_right _ member⟩

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- This receipt is derived from the actual macro body, including key admission and the exact indexed KEM call. -/
theorem encapsulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (key : Std.Array U8 1184#usize)
    (before after : Client) (reply : Spec.Range (.encapsulate (.Some key))) (log : Log KemSK)
    (supported : ((reply, after), log) ∈ support
      ((RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created
        (.encapsulate (.Some key))).run before).withQueryLog) :
    Receipt ⟨.encapsulate (.Some key), reply⟩ log := by
  simp only [RegistrationNativeKemCountedServerPrimitive.agreement, StateT.run_bind,
    StateT.run_modify, pure_bind, RegistrationNativeKemCountedServerPrimitive.core] at supported
  rw [RegistrationNativeKemCountedServerPrimitive.encapsulate] at supported
  by_cases valid : checks.kemKey (RegistrationRootInput.pqKey key) = true
  · simp only [valid, ite_true] at supported
    simp only [map_apply, RegistrationNativeKemCountedTrusted.world, StateT.run,
      RegistrationNativeKemCountedProgram.call, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, withQueryLog_bind, withQueryLog_query,
      mem_support_bind_iff] at supported
    simp only [Function.comp_apply, withQueryLog_pure, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨⟨⟨ciphertext, secret⟩, cost⟩, _, _, rfl, _, rfl, _, rfl, returned⟩ := supported
    simp only [Prod.map, id_eq, List.append_nil, Prod.mk.injEq] at returned
    rcases returned with ⟨⟨rfl, rfl⟩, rfl⟩
    change ∃ actualCost, _
    refine ⟨cost, ?_⟩
    rw [PqxdhPhase2InputBytes.word_rootArray,
      (PqxdhPhase2InputBytes.ciphertext_roundtrip (PqxdhAcceptedRegistration.ciphertextArray ciphertext) ciphertext).2]
    exact List.mem_singleton_self _
  · simp only [valid, Bool.false_eq_true, ite_false] at supported
    simp only [StateT.run_pure, withQueryLog_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at supported
    rcases supported with ⟨⟨rfl, rfl⟩, rfl⟩
    trivial

/-- Every higher callback derives its own lower-log receipt; non-encapsulation callbacks impose no such assertion. -/
theorem query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (request : Request)
    (before after : Client) (reply : Spec.Range request) (log : Log KemSK)
    (supported : ((reply, after), log) ∈ support
      ((RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created request).run before).withQueryLog) :
    Receipt ⟨request, reply⟩ log := by
  cases request <;> try trivial
  rename_i key
  cases key with
  | none => trivial
  | some key => exact encapsulate setup checks representation created key before after reply log supported

/-- Arbitrary adaptive higher trees retain the matching lower capability receipt for every newly logged callback. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp Spec Value) (journal final : Trace) (before after : Client)
    (value : Value) (log : Log KemSK)
    (supported : (((value, final), after), log) ∈ support
      ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
        (trace work journal)).run before).withQueryLog) :
    ∀ entry ∈ final, entry ∈ journal ∨ Receipt entry log :=
  RegistrationAgreementMacroTrace.program _ Receipt receipt_left receipt_right
    (fun request before reply after log => query setup checks representation created request before after reply log) work journal final before after value log supported

private theorem pq_roundtrip (value : PqxdhKemIndCca.MlKem768PublicKey) :
    RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray value) = value := by
  apply Subtype.ext
  simp [RegistrationRootInput.pqKey, RegistrationAgreementRoot.pqArray, absBytes, List.map_map, Function.comp_def]

/-- The actual higher Root completion and the lower indexed encapsulation draw occur in one execution, including the original draw cost and complete higher journal. -/
theorem server (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (final : Trace) (before after : Client) (log : Log KemSK)
    (supported : (((.ok (.ServerComplete completed), final), after), log) ∈ support
      ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
        (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) [])).run before).withQueryLog) :
    ∃ (input : RegistrationServerEncapsulationTrace.Input) (next : pqxdh.ServerState)
      (original : pqxdh.PendingServerRegistration) (reply : PqxdhBeaconPhase2Preparation.Word32) (cost : Nat),
      input.verified = RegistrationRootInput.verified packet authenticated ∧
      PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding, ⟨reply⟩⟩ ∧
      final = RegistrationServerEncapsulationTrace.entries input ++
        [⟨.root ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩, .Some reply⟩] ∧
      absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
        (absBytes input.first) (absBytes input.second) (absBytes input.third)
        (absBytes input.fourth) (absBytes input.kem) ∧
      (⟨.inr (.inr input.verified.keys.pqKey),
        ((PqxdhPhase2InputBytes.ciphertext input.ciphertext, PqxdhPhase2InputBytes.word input.kem), cost)⟩) ∈ log := by
  have erased : ((.ok (.ServerComplete completed), final), after) ∈ support
      ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
        (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) [])).run before) := by
    rw [← loggingOracle.fst_map_run_simulateQ
      ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
        (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) [])).run before), support_map]
    exact ⟨_, supported, rfl⟩
  have openRun : (.ok (.ServerComplete completed), final) ∈ support
      (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) []) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
      (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) []) before
    rw [StateT.run'_eq, support_map]
    exact ⟨_, erased, rfl⟩
  obtain ⟨input, next, original, reply, verified, accepted, completedEq, journalEq, bytes⟩ :=
    RegistrationServerEncapsulationTrace.server control packet authenticated completed [] final openRun
  simp only [List.nil_append] at journalEq
  let entry : Entry := ⟨.encapsulate (.Some (RegistrationAgreementRoot.pqArray input.verified.keys.pqKey)),
    .Some (input.ciphertext, input.kem)⟩
  have member : entry ∈ final := by
    rw [journalEq]
    apply List.mem_append_left
    simp only [RegistrationServerEncapsulationTrace.entries, List.mem_cons]
    exact Or.inr (Or.inl rfl)
  have receipt := program setup checks representation created
    (RegistrationAgreementExecutor.server control .Fresh authenticated) [] final before after
    (.ok (.ServerComplete completed)) log supported entry member
  have lower : Receipt entry log := receipt.resolve_left (List.not_mem_nil)
  obtain ⟨cost, actual⟩ := lower
  change (⟨.inr (.inr (RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray input.verified.keys.pqKey))),
    ((PqxdhPhase2InputBytes.ciphertext input.ciphertext, PqxdhPhase2InputBytes.word input.kem), cost)⟩) ∈ log at actual
  rw [pq_roundtrip] at actual
  exact ⟨input, next, original, reply, cost, verified, accepted, completedEq, journalEq, bytes, actual⟩

end BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.encapsulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace.server
