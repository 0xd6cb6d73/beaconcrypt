-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTracedServerInput
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace
import BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt

/-! The actual counted Server block transports one complete higher trace to the native collector while retaining its actual lower capability log and private pool. The resulting source-supported Root input names that same lower encapsulation reply and cost. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationAgreementExecutor
open RegistrationAgreementQueryTrace (Trace trace)
open RegistrationNativeKemServerState (State)
open RegistrationNativeKemCountedServerTrace (Log)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Client" => State n source
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK

def shared (current : Client × Pool KemSK) := RegistrationWorldAgreement.project current.1.server.world

private theorem query_project (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : Request) (before : Client × Pool KemSK) :
    Prod.map id shared <$> (RegistrationNativeKemServerCompiler.nativeAgreement setup checks representation created query).run before =
      (RegistrationAgreementShared.implementation setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed) query).run (shared before) := by
  have law := RegistrationWorldAgreement.agreement_project setup.source
    (RegistrationServerRoleBackend.native setup checks representation created.seed) query before.1.server.world
  simp only [RegistrationNativeKemServerCompiler.nativeAgreement, StateT.run, Functor.map_map,
    Prod.map, id_eq, shared] at ⊢
  simp only [StateT.run] at law ⊢
  exact law

/-- Projecting the full actual counted block to the native collector retains every higher request/reply, including Root. -/
theorem shared_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Value)
    (before : Client) (pool : Pool KemSK) :
    (fun result => (result.1.1, RegistrationWorldAgreement.project result.1.2.server.world)) <$>
      RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem
        (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) work) before pool =
      (simulateQ (RegistrationAgreementShared.implementation setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed)) work).run
          (RegistrationWorldAgreement.project before.server.world) := by
  have sourceLaw := RegistrationNativeKemCountedServerSource.program_source setup checks representation created work before pool
  have projected := OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ shared
    (query_project setup checks representation created) work (before, pool)
  have mapped := congrArg (fun distribution => Prod.map id shared <$> distribution) sourceLaw
  rw [projected] at mapped
  simp only [RegistrationNativeKemCountedTrusted.execute, RegistrationNativeKemCountedTrusted.arrange,
    StateT.run, Functor.map_map, Prod.map, id_eq, shared] at mapped
  exact mapped

/-- A native source-supported Root input tied to the same actual counted encapsulation entry. -/
structure Receipt (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : Client)
    (completed : agreement.ServerAgreement) (log : Log KemSK) where
  nativeInput : RegistrationNativeTokenRootReceipt.Input setup checks representation created packet authenticated before.server after.server completed
  cost : Nat
  encapsulated : (⟨.inr (.inr nativeInput.collected.verified.keys.pqKey),
    ((PqxdhPhase2InputBytes.ciphertext nativeInput.collected.ciphertext, PqxdhPhase2InputBytes.word nativeInput.collected.kem), cost)⟩) ∈ log

private theorem pq_roundtrip (value : PqxdhKemIndCca.MlKem768PublicKey) :
    RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray value) = value := by
  apply Subtype.ext
  simp [RegistrationRootInput.pqKey, RegistrationAgreementRoot.pqArray, absBytes, List.map_map, Function.comp_def]

/-- The actual traced Server source block derives its genuine native collector receipt and exact same-run counted encapsulation reply, without selecting an unrelated supported primitive sample. -/
theorem server (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (before after : Client) (beforePool afterPool : Pool KemSK) (journal : Trace) (log : Log KemSK)
    (supported : ((((.ok (.ServerComplete completed), journal), after), log), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
          (trace (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [])).run before).withQueryLog beforePool)) :
    Nonempty (Receipt setup checks representation created packet authenticated before after completed log) := by
  let work := (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
    (trace (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [])).run before
  have erased : (((.ok (.ServerComplete completed), journal), after), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work beforePool) := by
    have law := congrArg (fun program => RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem program beforePool)
      (loggingOracle.fst_map_run_simulateQ work)
    simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map] at law
    unfold RegistrationNativeKemCountedProgram.evaluate
    rw [← law, support_map]
    exact ⟨_, supported, rfl⟩
  have nativeRun : ((.ok (.ServerComplete completed), journal), RegistrationWorldAgreement.project after.server.world) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed))
          (trace (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [])).run
            (RegistrationWorldAgreement.project before.server.world)) := by
    rw [← shared_program setup checks representation created _ before beforePool, support_map]
    exact ⟨_, erased, rfl⟩
  obtain ⟨input, atRoot, next, original, collected, verified, admitted, complete, sameState, sameJournal, bytes⟩ :=
    RegistrationNativeTracedServerInput.server setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed)
      before.server.control packet authenticated completed [] journal (RegistrationWorldAgreement.project before.server.world)
      (RegistrationWorldAgreement.project after.server.world) nativeRun
  have openRun : (((.ok (.ServerComplete completed), journal), after), log) ∈ support work.withQueryLog := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem) _ beforePool
    rw [StateT.run'_eq, support_map]
    exact ⟨_, supported, rfl⟩
  let entry : RegistrationAgreementQueryTrace.Entry :=
    ⟨.encapsulate (.Some (RegistrationAgreementRoot.pqArray input.verified.keys.pqKey)), .Some (input.ciphertext, input.kem)⟩
  have member : entry ∈ journal := by
    rw [sameJournal]
    apply List.mem_append_left
    simp only [RegistrationServerEncapsulationTrace.entries, List.mem_append, List.not_mem_nil, false_or, List.mem_cons]
    exact Or.inr (Or.inl rfl)
  have lower := RegistrationNativeKemCountedServerTrace.program setup checks representation created
    (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [] journal before after (.ok (.ServerComplete completed)) log openRun entry member
  have lowerReceipt : RegistrationNativeKemCountedServerTrace.Receipt entry log := lower.resolve_left (List.not_mem_nil)
  obtain ⟨cost, actual⟩ := lowerReceipt
  change (⟨.inr (.inr (RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray input.verified.keys.pqKey))),
    ((PqxdhPhase2InputBytes.ciphertext input.ciphertext, PqxdhPhase2InputBytes.word input.kem), cost)⟩) ∈ log at actual
  rw [pq_roundtrip] at actual
  have built := RegistrationNativeAgreementInputReceipt.server_built before.server.control next _ input original admitted
  exact ⟨⟨⟨input, atRoot, next, original, collected, verified, admitted, complete, sameState, built.1, built.2, bytes⟩, cost, actual⟩⟩

private theorem lift_trace (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Value)
    (before after : Client) (beforePool afterPool : Pool KemSK) (value : Value) (log : Log KemSK)
    (supported : (((value, after), log), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) work).run before).withQueryLog beforePool)) :
    ∃ journal, ((((value, journal), after), log), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) (trace work [])).run before).withQueryLog beforePool) := by
  let erase : (Value × Trace) × Client → Value × Client := fun result => (result.1.1, result.2)
  have raw := congrArg (fun program => (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) program).run before)
    (RegistrationAgreementQueryTrace.erasure work [])
  simp only [simulateQ_map, StateT.run_map] at raw
  have erased : erase <$> (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) (trace work [])).run before =
      (simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) work).run before := raw
  have logged : Prod.map erase id <$>
      ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) (trace work [])).run before).withQueryLog =
      ((simulateQ (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created) work).run before).withQueryLog := by
    rw [← RegistrationAgreementMacroTrace.logging_map, erased]
  have law := congrArg (fun program => RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem program beforePool) logged
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map] at law
  unfold RegistrationNativeKemCountedProgram.evaluate at supported
  rw [← law, support_map] at supported
  obtain ⟨⟨⟨⟨⟨returned, journal⟩, finalClient⟩, finalLog⟩, finalPool⟩, reached, same⟩ := supported
  simp only [Prod.map, erase, id_eq, Prod.mk.injEq] at same
  rcases same with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  exact ⟨journal, reached⟩

/-- The literal replay-scheduled actual Server agreement supplies a native source collector receipt tied to its actual encapsulation log entry and private draw cost. -/
theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (before after : Client) (beforePool afterPool : Pool KemSK) (log : Log KemSK)
    (supported : (((.ok (.ServerComplete completed), after), log), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated).run before).withQueryLog beforePool)) :
    Nonempty (Receipt setup checks representation created packet authenticated before after completed log) := by
  simp only [RegistrationNativeKemCountedServerPrimitive.agree, StateT.run_bind,
    StateT.run_get, pure_bind, RegistrationReplaySchedule.begin_eq] at supported
  cases consumed : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) with
  | false =>
    simp only [consumed, Bool.false_eq_true, ite_false] at supported
    obtain ⟨journal, traced⟩ := lift_trace setup checks representation created
      (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) before after beforePool afterPool
      (.ok (.ServerComplete completed)) log supported
    exact server setup checks representation created packet authenticated completed before after beforePool afterPool journal log traced
  | true =>
    simp only [consumed, ite_true, simulateQ_pure, StateT.run_pure, withQueryLog_pure,
      RegistrationNativeKemCountedProgram.evaluate, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1.1.1

end BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource.shared_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource.shared_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource.agree
