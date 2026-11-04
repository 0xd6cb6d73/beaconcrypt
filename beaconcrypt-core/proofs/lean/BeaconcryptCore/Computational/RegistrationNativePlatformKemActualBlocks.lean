-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource

/-! Actual evaluated typed callback blocks retain their reached private KEM pools as well as their matching lower capability logs. This is operational prefix attribution in the same counted source execution, not just open-tree reachability. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call)
open PqxdhServerAuthExperiment (Setup)
open PqxdhLiveKemBirth (Pool)
open RegistrationNativeKemCountedServerTrace (Log)
variable {ι KemSK State Value : Type} {base : OracleSpec ι}
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK

private theorem evaluate_bind {A B : Type} (setup : Setup base KemSK)
    (work : OracleComp CP A) (next : A → OracleComp CP B) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (work >>= next) pool = (do
      let result ← RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next result.1) result.2) := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, StateT.run_bind]

private theorem evaluate_map {A B : Type} (setup : Setup base KemSK)
    (function : A → B) (work : OracleComp CP A) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (function <$> work) pool =
      Prod.map function id <$> RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map]
  rfl

/-- Every callback block has its own actually reached private before/after pools and its own lower log inside this same execution's complete log. -/
theorem continued (setup : Setup base KemSK)
    (implementation : QueryImpl TypedSpec (StateT State (OracleComp CP)))
    (work : OracleComp TypedSpec Value) (before after : State)
    (journal final : List (Call TypedSpec State)) (value : Value) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : (((value, (after, final)), log), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((simulateQ (RegistrationNativeObservedStageTrace.handler id implementation) work).run (before, journal)).withQueryLog beforePool)) :
    ∀ call ∈ final, call ∈ journal ∨
      ∃ block callBeforePool callAfterPool,
        (((call.reply, call.after), block), callAfterPool) ∈ support
          (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
            ((implementation call.query).run call.before).withQueryLog callBeforePool) ∧
        ∀ entry ∈ block, entry ∈ log := by
  induction work using OracleComp.inductionOn generalizing before after journal final value log beforePool afterPool with
  | pure returned =>
    simp only [simulateQ_pure, StateT.run_pure, withQueryLog_pure,
      RegistrationNativeKemCountedProgram.evaluate, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rcases supported with ⟨⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩, rfl⟩
    exact fun _ member => Or.inl member
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, withQueryLog_bind, evaluate_bind] at supported
    simp only [mem_support_bind_iff, evaluate_map, support_map] at supported
    obtain ⟨⟨⟨⟨reply, middle⟩, prefixLog⟩, middlePool⟩, head, ⟨last, lastPool⟩, tail, returned⟩ := supported
    rcases last with ⟨⟨returnedValue, returnedAfter, returnedCalls⟩, suffixLog⟩
    simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
    rcases returned with ⟨⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩, rfl⟩
    simp only [RegistrationNativeObservedStageTrace.handler, StateT.run] at head
    rw [RegistrationAgreementMacroTrace.logging_map, evaluate_map, support_map] at head
    obtain ⟨⟨⟨⟨actualReply, actualAfter⟩, actualLog⟩, actualPool⟩, ran, same⟩ := head
    simp only [Prod.map, id_eq, Prod.mk.injEq] at same
    rcases same with ⟨⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩, rfl⟩
    intro call member
    have receipt := ih actualReply actualAfter returnedAfter
      (journal ++ [⟨query, before, actualReply, actualAfter⟩]) returnedCalls returnedValue suffixLog actualPool lastPool tail call member
    rcases receipt with old | captured
    · rcases List.mem_append.mp old with initial | current
      · exact Or.inl initial
      · have named : call = ⟨query, before, actualReply, actualAfter⟩ := List.mem_singleton.mp current
        subst call
        exact Or.inr ⟨actualLog, beforePool, actualPool, ran, fun entry member => List.mem_append_left _ member⟩
    · obtain ⟨block, blockBefore, blockAfter, ran, included⟩ := captured
      exact Or.inr ⟨block, blockBefore, blockAfter, ran, fun entry member => List.mem_append_right _ (included entry member)⟩

open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {Platform E : Type}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


/-- Complete initialized callback blocks have actually reached private pools in the same literal counted source execution. -/
theorem initialized (history : History n source Value Platform) (finalPlatform : Platform) (log : Log KemSK) (pool : Pool KemSK)
    (supported : (((some history, finalPlatform), log), pool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((RegistrationNativePlatformKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
          reserveRegistration reservePeer erased helper writer bounds mode adversary).run previous).withQueryLog PqxdhLiveKemBirth.empty)) :
    ∀ call ∈ history.calls, ∃ block beforePool afterPool,
      (((call.reply, call.after), block), afterPool) ∈ support
        (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
          ((RegistrationNativePlatformKemClientJournal.free setup checks wire route representation history.initial.created history.initial.credential
            view failure allocation reserveRegistration reservePeer erased helper writer call.query).run call.before).withQueryLog beforePool) ∧
      ∀ entry ∈ block, entry ∈ log := by
  unfold RegistrationNativePlatformKemInitializedJournal.program at supported
  dsimp only [StateT.run] at supported
  simp only [bind_pure_comp, withQueryLog_bind, evaluate_bind, evaluate_map,
    mem_support_bind_iff, support_map] at supported
  obtain ⟨⟨⟨initialized, initialLog⟩, initialPool⟩, startup, ⟨returned, lastPool⟩, tail, same⟩ := supported
  rcases returned with ⟨returnedValue, bodyLog⟩
  simp only [Prod.map, id_eq, Prod.mk.injEq] at same
  rcases same with ⟨⟨rfl, logEq⟩, rfl⟩
  cases initialized with
  | none =>
    simp only [withQueryLog_pure, RegistrationNativeKemCountedProgram.evaluate, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
    cases tail.1.1.1
  | some initial =>
    dsimp only at tail
    rw [RegistrationAgreementMacroTrace.logging_map, evaluate_map, support_map] at tail
    obtain ⟨⟨⟨⟨value, ⟨⟨state, actualPlatform⟩, calls⟩⟩, actualLog⟩, actualPool⟩, reached, returned⟩ := tail
    simp only [Prod.map, id_eq, Prod.mk.injEq, Option.some.injEq] at returned
    rcases returned with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    intro call member
    have captured := continued setup
      (RegistrationNativePlatformKemClientJournal.free setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) (initial.state, previous) (state, actualPlatform) [] calls value actualLog initialPool actualPool reached call member
    rcases captured with old | ⟨block, beforePool, afterPool, ran, included⟩
    · exact False.elim (List.not_mem_nil old)
    · refine ⟨block, beforePool, afterPool, ran, ?_⟩
      intro entry member
      rw [← logEq]
      exact List.mem_append_right _ (included entry member)

/-- Every callback in the finite recipient analysis has an actual source block with its own reached private pools and the same global capability-log entries. -/
theorem experiment (budget : Budget) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget functional))
    (history : History n source Value Platform) (returned : result.2.1.1.1.1 = some history) :
    ∀ call ∈ history.calls, ∃ block beforePool afterPool,
      (((call.reply, call.after), block), afterPool) ∈ support
        (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
          ((RegistrationNativePlatformKemClientJournal.free setup checks wire route representation history.initial.created history.initial.credential
            view failure allocation reserveRegistration reservePeer erased helper writer call.query).run call.before).withQueryLog beforePool) ∧
      ∀ entry ∈ block, entry ∈ result.2.1.1.2 := by
  have actual := RegistrationNativeKemReservedSupport.logged setup functional
    ((RegistrationNativePlatformKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary).run previous) budget.create result supported
  change (((result.2.1.1.1.1, result.2.1.1.1.2), result.2.1.1.2), result.2.1.2) ∈ _ at actual
  rw [returned] at actual
  exact initialized setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary previous history result.2.1.1.1.2 result.2.1.1.2 result.2.1.2 actual

end BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks.continued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks.continued

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks.experiment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemActualBlocks.experiment
