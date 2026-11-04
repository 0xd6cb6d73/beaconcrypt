-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut
import BeaconcryptCore.Computational.RegistrationNativeKemReservedSupport

/-! The complete initialized counted Platform retains its actual typed callback history in addition to the lower capability log. Erasing only that history recovers the unchanged compiled source tree, so resource caps and the original recipient experiment apply to the same execution. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

omit primitives in
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
omit primitives in
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
omit primitives in
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

omit primitives in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (function : S → S) (before : S) :
    (modify function : StateT S m Unit) before = pure ((), function before) := rfl

omit primitives in
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private def Captured {S : Type}
    (implementation : QueryImpl TypedSpec (StateT S (OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK))))
    (call : Call TypedSpec S) (log : RegistrationNativeKemCountedServerTrace.Log KemSK) : Prop :=
  ∃ block, ((call.reply, call.after), block) ∈ support ((implementation call.query).run call.before).withQueryLog ∧
    ∀ entry ∈ block, entry ∈ log

omit primitives in
private theorem captures {S Out : Type}
    (implementation : QueryImpl TypedSpec (StateT S (OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK))))
    (work : OracleComp TypedSpec Out) (before after : S) (journal final : List (Call TypedSpec S))
    (value : Out) (log : RegistrationNativeKemCountedServerTrace.Log KemSK)
    (supported : (((value, (after, final)), log)) ∈ support
      ((simulateQ (RegistrationNativeObservedStageTrace.handler id implementation) work).run (before, journal)).withQueryLog) :
    ∀ call ∈ final, call ∈ journal ∨ Captured implementation call log := by
  induction work using OracleComp.inductionOn generalizing before after journal final value log with
  | pure returned =>
    simp only [simulateQ_pure, StateT.run_pure, withQueryLog_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rcases supported with ⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩
    exact fun _ member => Or.inl member
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, withQueryLog_bind] at supported
    simp only [mem_support_bind_iff, support_map] at supported
    obtain ⟨⟨⟨reply, middle⟩, prefixLog⟩, head, ⟨last, suffixLog⟩, tail, returned⟩ := supported
    simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
    rcases returned with ⟨rfl, rfl⟩
    simp only [RegistrationNativeObservedStageTrace.handler, StateT.run] at head
    rw [RegistrationAgreementMacroTrace.logging_map, support_map] at head
    obtain ⟨⟨⟨actualReply, actualAfter⟩, actualLog⟩, ran, same⟩ := head
    simp only [Prod.map, id_eq, Prod.mk.injEq] at same
    rcases same with ⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩
    intro call member
    have receipt := ih actualReply actualAfter after
      (journal ++ [⟨query, before, actualReply, actualAfter⟩]) final value suffixLog tail call member
    rcases receipt with old | captured
    · rcases List.mem_append.mp old with initial | current
      · exact Or.inl initial
      · have named : call = ⟨query, before, actualReply, actualAfter⟩ := List.mem_singleton.mp current
        subst call
        exact Or.inr ⟨actualLog, ran, fun entry member => List.mem_append_left _ member⟩
    · obtain ⟨block, ran, included⟩ := captured
      exact Or.inr ⟨block, ran, fun entry member => List.mem_append_right _ (included entry member)⟩

open RegistrationNativePlatformKemInitializedJournal (History erase)

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


noncomputable def program : StateT Platform (OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK))
    (Option (History n source Value Platform)) := fun previous => do
  let initialized ← RegistrationNativeKemCountedProgram.lift
    (RegistrationNativePlatformKemCountedProfile.start (n := n) setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure (none, previous)
  | some initial =>
    let result ← (simulateQ (RegistrationNativeObservedStageTrace.handler id
      (RegistrationNativePlatformOrdinaryKemClientJournal.free setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer))
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public))).run ((initial.state, previous), [])
    pure (some ⟨initial, result.1, result.2.1.1, result.2.2⟩, result.2.1.2)

/-- Typed-history instrumentation preserves the exact initialized free source tree and actual final platform state. -/
theorem erasure :
    erase <$> (program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous =
    (RegistrationNativePlatformOrdinaryKemProfile.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous := by
  unfold program
  simp only [StateT.run, RegistrationNativePlatformOrdinaryKemProfile.program, bind_apply, lift_apply,
    bind_pure_comp, map_bind, bind_map_left]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial =>
    have stripped := RegistrationNativeObservedStageTrace.erase id
      (RegistrationNativePlatformOrdinaryKemClientJournal.free setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) ((initial.state, previous), [])
    unfold RegistrationNativePlatformOrdinaryKemClientJournal.free at stripped
    rw [← RegistrationNativePlatformPackedState.simulate_pack] at stripped
    have joined := congrArg (fun work =>
      (fun result : (Value × RegistrationNativeLedger.State) × (RegistrationNativeKemServerState.State n source × Platform) =>
        (some (result.1, result.2.1), result.2.2)) <$> work) stripped
    simp only [RegistrationNativePlatformPackedState.pack, StateT.run, Functor.map_map] at joined
    simp only [erase, Option.map_some, Functor.map_map, map_apply, Prod.map, id_eq] at joined ⊢
    exact joined

/-- Every actual typed callback in the complete initialized history has its own same-state lower capability block inside this very run's complete log. -/
theorem blocks (history : History n source Value Platform) (finalPlatform : Platform)
    (log : RegistrationNativeKemCountedServerTrace.Log KemSK)
    (supported : ((some history, finalPlatform), log) ∈ support
      ((program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous).withQueryLog) :
    ∀ call ∈ history.calls, ∃ block,
      ((call.reply, call.after), block) ∈ support
        ((RegistrationNativePlatformOrdinaryKemClientJournal.free setup checks wire route representation history.initial.created history.initial.credential
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer call.query).run call.before).withQueryLog ∧
      ∀ entry ∈ block, entry ∈ log := by
  unfold program at supported
  simp only [StateT.run, bind_pure_comp, withQueryLog_bind, mem_support_bind_iff, support_map] at supported
  obtain ⟨⟨initialized, initialLog⟩, startup, ⟨returned, bodyLog⟩, continued, same⟩ := supported
  simp only [Prod.map, id_eq, Prod.mk.injEq] at same
  rcases same with ⟨rfl, logEq⟩
  cases initialized with
  | none =>
    simp only [withQueryLog_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued
    cases continued.1.1
  | some initial =>
    dsimp only at continued
    rw [RegistrationAgreementMacroTrace.logging_map, support_map] at continued
    obtain ⟨⟨⟨value, ⟨⟨state, actualPlatform⟩, calls⟩⟩, actualLog⟩, reached, returned⟩ := continued
    simp only [Prod.map, id_eq, Prod.mk.injEq, Option.some.injEq] at returned
    rcases returned with ⟨⟨rfl, rfl⟩, rfl⟩
    intro call member
    have covered := captures
      (RegistrationNativePlatformOrdinaryKemClientJournal.free setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) (initial.state, previous) (state, actualPlatform) [] calls value actualLog reached call member
    rcases covered with old | captured
    · exact False.elim (List.not_mem_nil old)
    · obtain ⟨block, ran, included⟩ := captured
      refine ⟨block, ran, ?_⟩
      intro entry member
      rw [← logEq]
      exact List.mem_append_right _ (included entry member)

private theorem accept_macro
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (packet : registration.InitPacket) (before : RegistrationNativeKemServerState.State n source × Platform) :
    (RegistrationNativePlatformOrdinaryKemClientJournal.free setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet))).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (((RegistrationNativePlatformKemCountedAccept.accept setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks
          (StateT.lift reserveRegistration) route representation created packet).run
            { before.1 with parsedAccepts := before.1.parsedAccepts + 1 }).run before.2) := by
  simp only [RegistrationNativePlatformOrdinaryKemClientJournal.free, RegistrationNativePlatformOrdinaryKemHandler.handler,
    RegistrationNativePlatformKemCountedHandler.handler]
  unfold RegistrationNativePlatformPackedState.pack
  dsimp only [StateT.run]
  simp only [bind_apply, modify_apply, pure_apply, pure_bind]
  rfl

/-- Every successful typed accept in the complete initialized history has a mandatory-authenticated, actually retained token and exact Root/encapsulation receipt in the complete run's lower log. -/
theorem accept_receipt (history : History n source Value Platform) (finalPlatform : Platform)
    (log : RegistrationNativeKemCountedServerTrace.Log KemSK)
    (supported : ((some history, finalPlatform), log) ∈ support
      ((program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous).withQueryLog)
    (packet : registration.InitPacket) (handle : Nat)
    (before after : RegistrationNativeKemServerState.State n source × Platform)
    (member : (⟨.inr (.accept packet), before, .ok (some handle), after⟩ : Call TypedSpec _) ∈ history.calls) :
    ∃ pin current currentPlatform,
      Nonempty (RegistrationNativePlatformAcceptRecipientCut.CheckedCut setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks route representation
        history.initial.created packet pin current currentPlatform handle after.1 after.2 log) := by
  obtain ⟨block, ran, included⟩ := blocks setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary previous history finalPlatform log supported _ member
  rw [accept_macro, RegistrationAgreementMacroTrace.logging_map, support_map] at ran
  obtain ⟨⟨⟨⟨reply, finalClient⟩, finalP⟩, actualLog⟩, accepted, returned⟩ := ran
  simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
  rcases returned with ⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩
  obtain ⟨pin, current, currentPlatform, _pinLog, _laterLog, _pinned, _split, ⟨checked⟩⟩ :=
    RegistrationNativePlatformAcceptRecipientCut.accept setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks (StateT.lift reserveRegistration)
      route representation history.initial.created packet { before.1 with parsedAccepts := before.1.parsedAccepts + 1 } finalClient before.2 finalP handle actualLog accepted
  refine ⟨pin, current, currentPlatform, ⟨{ checked with root := { checked.root with root :=
    { checked.root.root with encapsulated := included _ checked.root.root.encapsulated } } }⟩⟩



noncomputable def experiment (budget : Budget) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :=
  RegistrationNativeKemRecipientLogSource.experiment setup functional
    ((program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary).run previous) budget.create

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal.erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal.blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal.blocks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal.accept_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemInitializedJournal.accept_receipt
