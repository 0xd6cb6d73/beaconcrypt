-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemInitializedJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOriginJournal

/-! The initialized counted typed history is the same actual corrected Native source history, with complete final private pool and platform state. The protected-origin/cache observation uses the existing proved chronological projection rather than a final-state marginal. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

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


noncomputable def native : ProbComp ((Option (History n source Value Platform) × Platform) × PqxdhLiveKemBirth.Pool KemSK) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure ((none, previous), PqxdhLiveKemBirth.empty)
  | some initial =>
    let result ← (simulateQ (RegistrationNativeObservedStageTrace.handler RegistrationNativePlatformKemClientJournal.observe
      (RegistrationNativePlatformKemClientJournal.actual setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer erased helper writer))
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public))).run ((initial.state, previous), [])
    pure ((some ⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial, result.1,
      RegistrationNativeKemServerState.ofNative result.2.1.1, result.2.2⟩, result.2.1.2), result.2.1.1.pool)

omit primitives in
private theorem evaluate_bind {A B : Type} (setup : Setup base KemSK)
    (work : OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) A)
    (next : A → OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) B) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (work >>= next) pool = (do
      let result ← RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next result.1) result.2) := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, StateT.run_bind]

/-- Complete startup and the unchanged raw adaptive compilation have the same actual Native/client journal, final private recipient pool and platform state. -/
theorem source_history :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
      ((RegistrationNativePlatformKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode adversary).run previous) PqxdhLiveKemBirth.empty =
      native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode adversary previous := by
  unfold RegistrationNativePlatformKemInitializedJournal.program
  dsimp only [StateT.run]
  rw [evaluate_bind, RegistrationNativeKemCountedProgram.ordinary_source]
  simp only [native, RegistrationNativePlatformKemCountedProfile.start, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro initialized supported
  cases initialized with
  | none => rfl
  | some initial =>
    have empty := RegistrationNativePlatformKemCountedProfile.start_empty setup source ensureInit identityIndex serverKeyId initial supported
    have sourceLaw := RegistrationNativePlatformKemClientJournal.source_program setup checks wire route representation initial.created initial.credential
      view failure allocation reserveRegistration reservePeer erased helper writer
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) ((initial.state, previous), [])
    simp only [RegistrationNativeStateInterpreter.interpret, RegistrationNativePlatformPackedState.pack,
      RegistrationNativePlatformInterpret.state, StateT.run, RegistrationNativePlatformKemClientJournal.projected] at sourceLaw
    rw [empty] at sourceLaw
    have packed := congrArg (fun distribution =>
      (fun result : (Value × RegistrationNativeLedger.State) ×
          (((RegistrationNativeKemServerState.State n source × Platform) ×
            List (Call TypedSpec (RegistrationNativeKemServerState.State n source × Platform))) × PqxdhLiveKemBirth.Pool KemSK) =>
        ((some (⟨RegistrationNativePlatformKemCountedProfile.ofInitial initial, result.1, result.2.1.1.1, result.2.1.2⟩ : History n source Value Platform),
          result.2.1.1.2), result.2.2)) <$> distribution) sourceLaw
    simp only [Functor.map_map] at packed
    simp only [Option.map_some, bind_pure_comp, RegistrationNativeKemCountedProgram.evaluate,
      simulateQ_map, StateT.run_map] at ⊢
    simp only [RegistrationNativePlatformKemCountedProfile.ofInitial, RegistrationNativePlatformKemClientJournal.projected,
      RegistrationNativeKemServerState.ofNative, Prod.map, id_eq] at packed ⊢
    exact packed

def OriginCollision
    (result : ((Option (History n source Value Platform) × Platform) × PqxdhLiveKemBirth.Pool KemSK)) : Prop :=
  match result.1.1 with
  | none => False
  | some history => RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) history.initial.credential history.calls ∨
      CacheHasCollision (RegistrationNativeWorldCache.cache (RegistrationNativeKemServerState.toNative history.state result.2))

/-- The initialized projected history's one origin-or-final-cache exception is exactly the existing original Native union game, retaining the unchanged adaptive raw compilation. -/
theorem origin_native :
    Pr{let result ← (native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous)}[OriginCollision source result] =
    Pr{let failed ← (RegistrationNativePlatformMldsaOriginJournal.game (n := n) source setup checks wire route representation view failure allocation
      reserveRegistration reservePeer erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[failed = true] := by
  classical
  unfold native RegistrationNativePlatformMldsaOriginJournal.game
  simp only [prEvent_bind_eq_tsum]
  apply tsum_congr
  intro initialized
  cases initialized with
  | none => simp only [prEvent_pure, OriginCollision, ite_false, Bool.false_eq_true]
  | some initial =>
    apply congrArg (fun probability => _ * probability)
    have projected := RegistrationNativeObservedStageTrace.full_project RegistrationNativePlatformKemClientJournal.observe
      (RegistrationNativePlatformKemClientJournal.actual setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode
        (adversary initial.public)) ((initial.state, previous), [])
    have law := congrArg (fun distribution => Pr{let result ← distribution}[
      RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) initial.credential result.2.2 ∨
        CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1)]) projected
    have callBad (calls : List (Call TypedSpec (RegistrationNativeExperiment.State n KemSK source × Platform))) :
        RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) initial.credential
          (calls.map (RegistrationNativeObservedStageTrace.mapCall RegistrationNativePlatformKemClientJournal.observe)) ↔
          RegistrationNativePlatformMldsaOriginJournal.BadCalls initial.credential calls :=
      RegistrationNativeKemClientObservation.bad_calls initial.credential calls
    simp only [prEvent_map, Prod.map, id_eq, callBad, List.map_nil] at law
    simp only [bind_pure_comp, prEvent_map, OriginCollision, RegistrationNativePlatformKemCountedProfile.ofInitial,
      RegistrationNativeKemServerState.native_roundtrip, decide_eq_true_eq,
      RegistrationNativePlatformMldsaOriginJournal.flagged_iff] at ⊢
    exact law.symm

variable (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
variable (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)

include bounded in
/-- The private finite recipient family's initialized origin/cache observation has exactly the original Native chronological union-game probability. -/
theorem origin_probability :
    Pr{let result ← (RegistrationNativePlatformKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget functional)}[
      OriginCollision source (result.2.1.1.1, result.2.1.2)] =
    Pr{let failed ← (RegistrationNativePlatformMldsaOriginJournal.game (n := n) source setup checks wire route representation view failure allocation
      reserveRegistration reservePeer erased helper writer
      (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
      previous ensureInit identityIndex serverKeyId)}[failed = true] := by
  let work := (RegistrationNativePlatformKemInitializedJournal.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary).run previous
  have births := RegistrationNativePlatformKemInitializedJournal.resource (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget bounded .birth
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at births
  have birthBound : work.IsQueryBoundP RegistrationNativeKemCountedReservation.IsCreate budget.create := by
    convert births using 1
    rfl
  have law := (RegistrationNativeKemCountedRecipientSource.source setup functional work budget.create birthBound).prEvent_eq (OriginCollision source)
  have logged := RegistrationNativeKemRecipientLogSource.erasure setup functional work budget.create
  rw [← logged, prEvent_map] at law
  dsimp only [work] at law
  rw [source_history, origin_native] at law
  simpa only [prEvent_map, RegistrationNativeKemRecipientLogSource.erase,
    RegistrationNativePlatformKemInitializedJournal.experiment] using law.symm

include bounded in
/-- The same initialized recipient execution pays the single original Native cache charge and actual ordinary generated-key EUF family for its origin/cache exception. -/
theorem origin_bound :
    Pr{let result ← (RegistrationNativePlatformKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget functional)}[OriginCollision source (result.2.1.1.1, result.2.1.2)] ≤
      Pr{let collision ← (RegistrationNativePlatformMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId)) := by
  rw [origin_probability (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget bounded functional]
  exact RegistrationNativePlatformMldsaOriginJournal.compiled source setup checks wire route representation view failure allocation
    reserveRegistration reservePeer erased helper writer previous bounds mode adversary budget bounded ensureInit identityIndex serverKeyId

include bounded in
/-- Origin/cache failure and absence of correct same-run token Root recipient receipts share one initialized execution and one cache term; the only extra term is the actual finite honest-recipient failure bill. -/
theorem exceptions_bound :
    Pr{let result ← (RegistrationNativePlatformKemInitializedJournal.experiment (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget functional)}[
      OriginCollision source (result.2.1.1.1, result.2.1.2) ∨
      ¬ RegistrationNativePlatformKemInitializedJournal.AcceptReceipts (n := n) setup checks wire route representation source budget functional result] ≤
      (Pr{let collision ← (RegistrationNativePlatformMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer erased helper writer
        (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
        previous ensureInit identityIndex serverKeyId)}[collision = true] +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto wire publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId))) + budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  apply (prEvent_or_le _ _ _).trans
  apply add_le_add
  · exact origin_bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget bounded functional
  · exact RegistrationNativePlatformKemInitializedJournal.recipient_receipts_bound (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary previous budget bounded functional

end BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.source_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.source_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.origin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.origin_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.origin_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.origin_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.origin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.origin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.exceptions_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHistorySource.exceptions_bound
