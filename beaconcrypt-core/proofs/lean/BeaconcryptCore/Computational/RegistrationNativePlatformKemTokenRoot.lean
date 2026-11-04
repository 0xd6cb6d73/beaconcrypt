-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformKemHistoryPath

/-! A token consumed from the actual same-run source table is tied to its first successful accept, its genuine native Root collector and that very execution's lower encapsulation reply/cost. The chronological call and lower block are both derived from the initialized execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemTokenRoot
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {Platform E : Type}
variable {ι KemSK Value : Type} {base : OracleSpec ι}
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


open RegistrationNativeStageTrace (Call)
open RegistrationNativeKemCountedServerTrace (Log)
open PqxdhLiveKemBirth (Pool)
local notation "Client" => RegistrationNativeKemServerState.State n source
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK

omit primitives in
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
omit primitives in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (function : S → S) (before : S) :
    (modify function : StateT S m Unit) before = pure ((), function before) := rfl
omit primitives in
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
omit primitives in
private theorem evaluate_map {A B : Type} (setup : Setup base KemSK)
    (function : A → B) (work : OracleComp CP A) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (function <$> work) pool =
      Prod.map function id <$> RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map]
  rfl

private theorem accept_macro
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (packet : registration.InitPacket) (before : RegistrationNativeKemServerState.State n source × Platform) :
    (RegistrationNativePlatformKemClientJournal.free setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer (.inr (.accept packet))).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (((RegistrationNativePlatformKemCountedAccept.accept setup (RegistrationNativeWire.ledgerCodec wire) checks
          (StateT.lift reserveRegistration) route representation created packet).run
            { before.1 with parsedAccepts := before.1.parsedAccepts + 1 }).run before.2) := by
  simp only [RegistrationNativePlatformKemClientJournal.free, RegistrationNativePlatformKemCountedHandler.handler]
  unfold RegistrationNativePlatformPackedState.pack
  dsimp only [StateT.run]
  simp only [bind_apply, modify_apply, pure_apply, pure_bind]
  rfl

/-- A newly inserted token in an actually evaluated typed accept is attached to its same native collector and actual global lower log. -/
theorem callback_new (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (packet : registration.InitPacket) (handle : Nat) (before after : Client × Platform)
    (block log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : (((.ok (some handle), after), block), afterPool) ∈ support
      (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
        ((RegistrationNativePlatformKemClientJournal.free setup checks wire route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper writer (.inr (.accept packet))).run before).withQueryLog beforePool))
    (included : ∀ entry ∈ block, entry ∈ log)
    (token : peer.ConsumedRegistration) (present : RegistrationNativeTokenSource.Present token after.1.server)
    (newToken : ¬ RegistrationNativeTokenSource.Present token before.1.server) :
    ∃ pin current currentPlatform,
      ∃ receipt : RegistrationNativePlatformAcceptActualRoot.CheckedCut setup (RegistrationNativeWire.ledgerCodec wire) checks route representation
        created packet pin current currentPlatform handle after.1 after.2 log,
      receipt.root.beforeAgreement = receipt.afterCheck ∧ token.agreement = receipt.root.accepted := by
  rw [accept_macro, RegistrationAgreementMacroTrace.logging_map, evaluate_map, support_map] at supported
  obtain ⟨⟨⟨⟨⟨reply, finalClient⟩, finalP⟩, actualLog⟩, finalPool⟩, accepted, returned⟩ := supported
  simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
  rcases returned with ⟨⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩, rfl⟩
  obtain ⟨pin, current, currentPlatform, checked, sameBefore, sameToken⟩ :=
    RegistrationNativePlatformAcceptActualToken.accept_new_full setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration
      route representation created packet { before.1 with parsedAccepts := before.1.parsedAccepts + 1 } finalClient before.2 finalP handle actualLog beforePool finalPool accepted token present newToken
  exact ⟨pin, current, currentPlatform, { checked with root := { checked.root with root :=
    { checked.root.root with encapsulated := included _ checked.root.root.encapsulated } } }, sameBefore, sameToken⟩


/-- A token moved by an actual build has one earlier same-execution successful accept whose actual native Root operands name this exact analysis log's encapsulation reply. -/
theorem taken (budget : Budget) (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK (Option (History n source Value Platform) × Platform) budget.create)
    (supported : result ∈ support (RegistrationNativePlatformKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget functional))
    (history : History n source Value Platform) (returned : result.2.1.1.1.1 = some history)
    (path : RegistrationNativePlatformKemHistoryPath.Receipt setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer previous history result.2.1.1.1.2 result.2.1.2)
    (buildCall : Call RegistrationNativeRawAdapter.TypedSpec (Native × Platform)) (member : buildCall ∈ path.calls)
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (moved : RegistrationServerSdkSource.take index buildCall.before.1.server = (some token, current)) :
    ∃ packet handle first last,
      (⟨.inr (.accept packet), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec (Native × Platform)) ∈ path.calls ∧
      ∃ pin checkedAt checkedPlatform,
        ∃ receipt : RegistrationNativePlatformAcceptActualRoot.CheckedCut setup (RegistrationNativeWire.ledgerCodec wire) checks route representation
          path.initial.created packet pin checkedAt checkedPlatform handle (RegistrationNativeKemServerState.ofNative last.1) last.2 result.2.1.1.2,
        receipt.root.beforeAgreement = receipt.afterCheck ∧ token.agreement = receipt.root.accepted := by
  obtain ⟨leading, trailing, split, beforeBuild, _built, _afterBuild⟩ := path.reached.member buildCall member
  have initialEmpty := RegistrationNativeTokenTrace.start_empty setup ensureInit identityIndex serverKeyId path.initial path.startup
  have absent : ¬ RegistrationNativeTokenSource.Present token path.initial.state.server := by
    simp only [RegistrationNativeTokenSource.Present, initialEmpty, List.not_mem_nil, not_false_eq_true]
  have present : RegistrationNativeTokenSource.Present token buildCall.before.1.server :=
    List.mem_of_getElem? (RegistrationNativeTokenSource.take_origin index buildCall.before.1.server current token moved).1
  obtain ⟨packet, handle, first, last, accepted, old, added⟩ := RegistrationNativePlatformTokenNewTrace.path RegistrationNativePlatformMldsaProgram.coins
    setup checks wire route representation path.initial.created path.initial.credential view failure allocation reserveRegistration reservePeer erased helper writer
      beforeBuild token absent present
  have fullMember : (⟨.inr (.accept packet), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec (Native × Platform)) ∈ path.calls := by
    rw [split]
    exact List.mem_append_left _ accepted
  have projected : (⟨.inr (.accept packet), (RegistrationNativeKemServerState.ofNative first.1, first.2), .ok (some handle),
      (RegistrationNativeKemServerState.ofNative last.1, last.2)⟩ : Call RegistrationNativeRawAdapter.TypedSpec (Client × Platform)) ∈ history.calls := by
    rw [path.callsEq]
    exact List.mem_map.mpr ⟨_, fullMember, rfl⟩
  obtain ⟨block, beforePool, afterPool, ran, included⟩ := RegistrationNativePlatformKemActualBlocks.experiment setup checks wire route representation source
    ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget functional
      result supported history returned _ projected
  have createdEq : history.initial.created = path.initial.created := congrArg RegistrationNativePlatformKemCountedProfile.Initial.created path.initialEq
  have credentialEq : history.initial.credential = path.initial.credential := congrArg RegistrationNativePlatformKemCountedProfile.Initial.credential path.initialEq
  rw [createdEq, credentialEq] at ran
  obtain ⟨pin, checkedAt, checkedPlatform, receipt, beforeEq, tokenEq⟩ := callback_new setup checks wire route representation source
    view failure allocation reserveRegistration reservePeer erased helper writer path.initial.created path.initial.credential
      packet handle (RegistrationNativeKemServerState.ofNative first.1, first.2) (RegistrationNativeKemServerState.ofNative last.1, last.2)
        block result.2.1.1.2 beforePool afterPool ran included token added old
  exact ⟨packet, handle, first, last, fullMember, pin, checkedAt, checkedPlatform, receipt, beforeEq, tokenEq⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformKemTokenRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemTokenRoot.callback_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemTokenRoot.callback_new

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemTokenRoot.taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemTokenRoot.taken
