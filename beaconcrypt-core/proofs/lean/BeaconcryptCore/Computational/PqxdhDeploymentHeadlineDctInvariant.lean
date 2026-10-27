-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctStep

/-!
# CE-12 D-ct: the commitment invariant of the split game

The invariant `DctInv` (design section 4.4) between the secrecy ledger's transcript and the extended state of the final split game of a target (`PqxdhDeploymentBackend.gameWith … splitInit (PqxdhDeploymentIdealDefer.idealSplit t p)`):

- `early`: up to the selected ordinal there is no mark, the selected accept is inactive, and every pending token and every successful build is below the session counter (design risk 3: the fields are needed only at the marking step, which is the selected accept, so they are stated only up to it, as `PqxdhDeploymentIdealProvenance.Prov.early` does).
- `markedCommit`: every successful build of the marked session either found the allocator full with the marked coordinates holding no slot, or the marked coordinates hold a slot whose cached material `m` keys the commitment of the response's frame (`CommitAt … m.1`); the first alternative is excluded on the World by `Prov.marked` (the marked coordinates hold slot 0).
- `finishRoot`: every successful finish on an input that is not `ChallengeRead` left an R1 entry `v` and its input committed under `seqKey setup v`.

It holds initially (`dctInv_initial`) and is kept by every command query (`dctInv_command`, from `PqxdhDeploymentHeadlineDctStep.step_facts`, `PqxdhDeploymentHeadlineDctCommit.markedBuild_commit`, `finish_root` and `build_pending`: a new mark is at the old session counter, below which no build exists) and every secrecy query (`coinSend_quiet`, `dctInv_quiet`), so by every query of the ledger handler (`splitLedgerHandler`, `dctInv_step`), on every outcome of the split game (`split_dctInv`), and on every outcome of the record world with `envGD` at the drawn parameters (`world_dctInv`, through the support of `PqxdhDeploymentIdealEnv.c1_split`). The premises are the approved codec contracts `Phase2ReadBack` and `FrameReadBack`; no assumption is used.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealSteps (SplitBk IdealCore)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentIdealProvenance (BuiltIn)
open PqxdhDeploymentHeadlineDctReceive (seqKey)
open PqxdhDeploymentHeadlineDctCommit (r1 ctxCache CommitAt)
open PqxdhDeploymentHeadlineDctStep (StepFacts step_facts NGrows SlotGrows)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

section Invariant
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : ℕ} (t : Target count)
  (p : Params KemSK count)

/-- The D-ct invariant between the ledger's transcript and the split state (design section 4.4, with the amendments of this build): up to the selected ordinal there is no mark, the selected accept is inactive, and every pending token and every successful build is below the session counter; every successful build of the marked session found the allocator full with the marked coordinates holding no slot, or the marked coordinates hold a slot whose cached material keys the commitment of the response's frame; and every successful finish on an input that is not `ChallengeRead` left an R1 entry `v` and its input committed under `seqKey setup v`. -/
structure DctInv (transcript : List Entry) (x : XState KemSK SplitBk 2) : Prop where
  early : x.backend.2.2.accepts ≤ t.accept → x.backend.2.2.marks = none ∧ x.backend.2.2.active = false ∧
    (∀ s, (x.base.native.shared.2.pending s).isSome = true → s < x.base.native.shared.2.sessions) ∧
    ∀ s response, BuiltIn transcript s response → s < x.base.native.shared.2.sessions
  markedCommit : ∀ s c response, x.backend.2.2.marks = some (s, c) → BuiltIn transcript s response →
    (x.backend.2.1.1 c = none ∧ 2 ≤ x.backend.2.1.2) ∨
      ∃ j m, x.backend.2.1.1 c = some j ∧ x.backend.1 j = some m ∧
        CommitAt codec (ctxCache x) response.serialized m.1.toList
  finishRoot : ∀ owner raw reply, (⟨.inl (.inr (.finish owner raw)), some reply⟩ : Entry) ∈ transcript →
    ¬ PqxdhDeploymentIdealBeacon.ChallengeRead codec p.challenge raw →
    ∃ u v, r1 x u = some v ∧ CommitAt codec (ctxCache x) raw (seqKey setup v).toList

/-- The invariant holds at the start: empty transcript, the constructed Server's initial state and the initial split backend. -/
theorem dctInv_initial (created : PqxdhLiveServerConstruction.Created Unit) :
    DctInv setup codec t p [] (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)) := by
  refine ⟨fun _ => ⟨rfl, rfl, fun s found => ?_, fun s response built => ?_⟩, fun s c response marked _ => ?_,
    fun owner raw reply member => ?_⟩
  · simp [PqxdhDeploymentBackend.xinitial, PqxdhDeploymentNative.initial, PqxdhRegistrationSchedule.initial] at found
  · obtain ⟨_, member⟩ := built
    cases member
  · cases marked
  · cases member

end Invariant

/-! ### Preservation by the split handler -/

section Step
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A successful build of the split handler answers only from a pending token of its session. -/
theorem build_pending (session : ℕ) (payload : Option Pqxdh.Bytes) (x : XState KemSK SplitBk 2)
    (result : Option PqxdhServerRegistrationPublication.Response × XState KemSK SplitBk 2)
    (member : result ∈ support ((PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) (.inr (.build session payload))).run x))
    (response : PqxdhServerRegistrationPublication.Response) (replied : result.1 = some response) :
    (x.base.native.shared.2.pending session).isSome = true := by
  change result ∈ support ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
    PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
      (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload)).run x >>=
        PqxdhDeploymentIdealDefer.serverInstall)) at member
  rw [support_map] at member
  obtain ⟨installed, installedMember, rfl⟩ := member
  rw [mem_support_bind_iff] at installedMember
  obtain ⟨mid, midMember, installMember⟩ := installedMember
  obtain ⟨replyEq, -⟩ := PqxdhDeploymentHeadlineDctCommit.serverInstall_keeps mid installed installMember
  obtain ⟨inner, innerMember, innerReply, -⟩ := PqxdhDeploymentHeadlineDctCommit.slotRunX_support _ _ x mid midMember
  exact PqxdhDeploymentHeadlineDctCommit.buildStepC_pending setup codec checks route created _ session payload _ inner
    innerMember response (by rw [← innerReply, ← replyEq]; exact replied)

/-- Every command query of the split handler keeps the invariant, with its entry appended to the transcript. -/
theorem dctInv_command (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (query : PqxdhDeploymentInterface.Spec.Domain)
    (transcript : List Entry) (x : XState KemSK SplitBk 2) (inv : DctInv setup codec t p transcript x)
    (result : PqxdhDeploymentInterface.Spec.Range query × XState KemSK SplitBk 2)
    (member : result ∈ support ((PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query).run x)) :
    DctInv setup codec t p (transcript ++ [⟨.inl query, result.1⟩]) result.2 := by
  have facts := step_facts setup codec checks route t p created query x result member
  have newBuild : ∀ s response, BuiltIn (transcript ++ [⟨.inl query, result.1⟩]) s response →
      BuiltIn transcript s response ∨ ((x.base.native.shared.2.pending s).isSome = true ∧
        ∀ c, x.backend.2.2.marks = some (s, c) →
          (result.2.backend.2.1.1 c = none ∧ 2 ≤ result.2.backend.2.1.2) ∨
            ∃ j m, result.2.backend.2.1.1 c = some j ∧ result.2.backend.1 j = some m ∧
              CommitAt codec (ctxCache result.2) response.serialized m.1.toList) := by
    intro s response built
    rcases PqxdhDeploymentIdealProvenance.builtIn_append transcript _ s response built with old | ⟨payload, same⟩
    · exact Or.inl old
    · right
      have queryEq : query = .inr (.build s payload) := Sum.inl.inj (congrArg Entry.query same)
      subst queryEq
      have replied : result.1 = some response := by
        simp only [Entry.mk.injEq, true_and] at same
        exact eq_of_heq same
      exact ⟨build_pending setup codec checks route t p created s payload x result member response replied,
        fun c marked => PqxdhDeploymentHeadlineDctCommit.markedBuild_commit setup codec checks route t p created phase2
          frameBack s payload x c marked result member response replied⟩
  have newFinish : ∀ owner raw reply, (⟨.inl (.inr (.finish owner raw)), some reply⟩ : Entry) ∈
      transcript ++ [⟨.inl query, result.1⟩] →
      (⟨.inl (.inr (.finish owner raw)), some reply⟩ : Entry) ∈ transcript ∨
        (¬ PqxdhDeploymentIdealBeacon.ChallengeRead codec p.challenge raw →
          ∃ u v, r1 result.2 u = some v ∧ CommitAt codec (ctxCache result.2) raw (seqKey setup v).toList) := by
    intro owner raw reply found
    rcases List.mem_append.mp found with old | new
    · exact Or.inl old
    · right
      have same := (List.mem_singleton.mp new)
      have queryEq : query = .inr (.finish owner raw) := (Sum.inl.inj (congrArg Entry.query same)).symm
      subst queryEq
      have replied : result.1 = some reply := by
        simp only [Entry.mk.injEq, true_and] at same
        exact eq_of_heq same.symm
      exact PqxdhDeploymentHeadlineDctCommit.finish_root setup codec checks route t p created owner raw x result member
        reply replied
  refine ⟨fun late => ?_, fun s c response marked built => ?_, fun owner raw reply found other => ?_⟩
  · have before : x.backend.2.2.accepts ≤ t.accept := le_trans facts.accepts late
    obtain ⟨marks, active, pendingBelow, builtBelow⟩ := inv.early before
    obtain ⟨marks', active', sessions, pending⟩ := facts.early before marks active late
    refine ⟨marks', active', fun s found => ?_, fun s response built => ?_⟩
    · rcases pending s found with old | new
      · exact lt_of_lt_of_le (pendingBelow s old) sessions
      · exact new
    · rcases newBuild s response built with old | ⟨pend, -⟩
      · exact lt_of_lt_of_le (builtBelow s response old) sessions
      · exact lt_of_lt_of_le (pendingBelow s pend) sessions
  · by_cases same : x.backend.2.2.marks = some (s, c)
    · rcases newBuild s response built with old | ⟨-, commit⟩
      · rcases inv.markedCommit s c response same old with ⟨unslotted, full⟩ | ⟨j, m, slotted, cached, committed⟩
        · left
          have fixed := facts.slots.2.2.1 full
          exact ⟨by rw [fixed]; exact unslotted, le_trans full facts.slots.2.1⟩
        · right
          exact ⟨j, m, facts.slots.1 c j slotted, facts.slots.2.2.2 j m cached,
            PqxdhDeploymentHeadlineDctCommit.commitAt_mono codec _ _ _ _ committed facts.grows.2⟩
      · exact commit c same
    · exfalso
      rcases facts.fresh s c marked with old | fresh
      · exact same old
      · by_cases before : x.backend.2.2.accepts ≤ t.accept
        · obtain ⟨_, _, pendingBelow, builtBelow⟩ := inv.early before
          rcases newBuild s response built with old | ⟨pend, -⟩
          · have below := builtBelow s response old
            omega
          · have below := pendingBelow s pend
            omega
        · have kept := facts.marks (by omega)
          rw [kept] at marked
          exact same marked
  · rcases newFinish owner raw reply found with old | new
    · obtain ⟨u, v, entry, committed⟩ := inv.finishRoot owner raw reply old other
      exact ⟨u, v, facts.grows.1 u v entry,
        PqxdhDeploymentHeadlineDctCommit.commitAt_mono codec _ _ _ _ committed facts.grows.2⟩
    · exact new other

end Step

/-! ### The secrecy commands and the whole game -/

section Game
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- A native-interface program that issues only coins and sends, under the handler with any registration handler, keeps the backend, the session counter and the pending tokens, and grows the native shared state. -/
theorem coinSend_quiet {Bk : Type} {n : ℕ} {Value : Type} (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n)
    (program : OracleComp PqxdhDeploymentInterface.Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (x : XState KemSK Bk n) (result : Value × XState KemSK Bk n)
    (member : result ∈ support ((simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route reg) program).run x)) :
    result.2.backend = x.backend ∧ NGrows x.base.native.shared result.2.base.native.shared ∧
      result.2.base.native.shared.2.sessions = x.base.native.shared.2.sessions ∧
      result.2.base.native.shared.2.pending = x.base.native.shared.2.pending := by
  induction program using OracleComp.inductionOn generalizing x with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, PqxdhDeploymentHeadlineDctStep.nGrows_refl _, rfl, rfl⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨⟨reply, middle⟩, first, second⟩ := member
      have firstKept : middle.backend = x.backend ∧ NGrows x.base.native.shared middle.base.native.shared ∧
          middle.base.native.shared.2.sessions = x.base.native.shared.2.sessions ∧
          middle.base.native.shared.2.pending = x.base.native.shared.2.pending := by
        rcases query with coin | command
        · simp only [PqxdhDeploymentBackend.handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at first
          obtain ⟨_, _, same⟩ := first
          cases same
          exact ⟨rfl, PqxdhDeploymentHeadlineDctStep.nGrows_refl _, rfl, rfl⟩
        · cases command with
          | serverSend kid plaintext =>
              obtain ⟨backend, native⟩ := PqxdhDeploymentIdealKeymatch.onBase_support _ x _ first
              have fields := PqxdhDeploymentNative.serverStep_fields setup codec route _ x.base _ native
              exact ⟨backend, PqxdhDeploymentHeadlineDctStep.serverStep_grows setup codec route _ x.base _ native,
                fields.2.2.2.2.1, fields.2.2.2.1⟩
          | beaconSend index plaintext =>
              obtain ⟨backend, native⟩ := PqxdhDeploymentIdealKeymatch.onBase_support _ x _ first
              have fields := PqxdhDeploymentNative.beaconStep_fields setup codec index _ x.base _ native
              exact ⟨backend, PqxdhDeploymentHeadlineDctStep.beaconStep_grows setup codec index _ x.base _ native,
                fields.2.2.2.2.1, fields.2.2.2.1⟩
          | _ => simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      have restBound := rest reply
      simp only [kind, Bool.true_eq_false, ite_false] at restBound
      obtain ⟨backend, grows, sessions, pending⟩ := ih reply restBound middle second
      exact ⟨backend.trans firstKept.1, PqxdhDeploymentHeadlineDctStep.nGrows_trans firstKept.2.1 grows,
        sessions.trans firstKept.2.2.1, pending.trans firstKept.2.2.2⟩

/-- A step that keeps the backend, the session counter and the pending tokens, grows the native shared state and appends a secrecy entry keeps the invariant. -/
theorem dctInv_quiet (transcript : List Entry) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (reply : PqxdhDeploymentInterface.FullSpec.Range (.inr secrecy)) (x y : XState KemSK SplitBk 2)
    (inv : DctInv setup codec t p transcript x) (backend : y.backend = x.backend)
    (grows : NGrows x.base.native.shared y.base.native.shared)
    (sessions : y.base.native.shared.2.sessions = x.base.native.shared.2.sessions)
    (pending : y.base.native.shared.2.pending = x.base.native.shared.2.pending) :
    DctInv setup codec t p (transcript ++ [⟨.inr secrecy, reply⟩]) y := by
  have oldBuild : ∀ s response, BuiltIn (transcript ++ [⟨.inr secrecy, reply⟩]) s response →
      BuiltIn transcript s response := by
    intro s response built
    rcases PqxdhDeploymentIdealProvenance.builtIn_append transcript _ s response built with old | ⟨payload, same⟩
    · exact old
    · cases congrArg Entry.query same
  have oldFinish : ∀ owner raw finished, (⟨.inl (.inr (.finish owner raw)), some finished⟩ : Entry) ∈
      transcript ++ [⟨.inr secrecy, reply⟩] → (⟨.inl (.inr (.finish owner raw)), some finished⟩ : Entry) ∈ transcript := by
    intro owner raw finished found
    rcases List.mem_append.mp found with old | new
    · exact old
    · cases congrArg Entry.query (List.mem_singleton.mp new)
  refine ⟨fun late => ?_, fun s c response marked built => ?_, fun owner raw finished found other => ?_⟩
  · rw [backend] at late ⊢
    obtain ⟨marks, active, pendingBelow, builtBelow⟩ := inv.early late
    refine ⟨marks, active, fun s found => ?_, fun s response built => ?_⟩
    · rw [pending] at found
      rw [sessions]
      exact pendingBelow s found
    · rw [sessions]
      exact builtBelow s response (oldBuild s response built)
  · rw [backend] at marked ⊢
    rcases inv.markedCommit s c response marked (oldBuild s response built) with old | ⟨j, m, slotted, cached, committed⟩
    · exact Or.inl old
    · exact Or.inr ⟨j, m, slotted, cached, PqxdhDeploymentHeadlineDctCommit.commitAt_mono codec _ _ _ _ committed grows.2⟩
  · obtain ⟨u, v, entry, committed⟩ := inv.finishRoot owner raw finished (oldFinish owner raw finished found) other
    exact ⟨u, v, grows.1 u v entry, PqxdhDeploymentHeadlineDctCommit.commitAt_mono codec _ _ _ _ committed grows.2⟩

/-- The split handler composed with the secrecy layer, on the product of the ledger and the extended state. -/
noncomputable def splitLedgerHandler (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl PqxdhDeploymentInterface.FullSpec
      (StateT (PqxdhDeploymentSecrecy.Ledger × XState KemSK SplitBk 2) ProbComp) :=
  ((PqxdhDeploymentBackend.handlerWith setup codec route
    (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)).flattenStateT

/-- Every query of the complete interface keeps the invariant between the ledger's transcript and the split state. -/
theorem dctInv_step (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : PqxdhDeploymentSecrecy.Ledger × XState KemSK SplitBk 2)
    (inv : DctInv setup codec t p state.1.transcript state.2)
    (result : PqxdhDeploymentInterface.FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × XState KemSK SplitBk 2))
    (member : result ∈ support ((splitLedgerHandler setup codec checks route t p bounds created query).run state)) :
    DctInv setup codec t p result.2.1.transcript result.2.2 := by
  rcases state with ⟨ledger, x⟩
  change result ∈ support ((fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created))
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run ledger)).run x)
    at member
  rw [support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at reachedMember
    obtain ⟨answer, answerMember, rfl⟩ := reachedMember
    exact dctInv_command setup codec checks route t p created phase2 frameBack request ledger.transcript x inv answer
      answerMember
  · have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId
        bounds (.inr secrecy)).run ledger) := by
      apply OracleComp.support_simulateQ_run'_subset (PqxdhDeploymentBackend.handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)) _ x
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, reachedMember, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      ledger reached.1 value
    obtain ⟨backend, grows, sessions, pending⟩ := coinSend_quiet setup codec route _ _
      (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy ledger) x reached
      reachedMember
    change DctInv setup codec t p reached.1.2.transcript reached.2
    rw [recorded]
    exact dctInv_quiet setup codec t p ledger.transcript secrecy _ x _ inv backend grows sessions pending

/-- On every outcome of the final split game of a target at fixed draws, the invariant holds between the final transcript and the final split state. -/
theorem split_dctInv {A X : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK SplitBk 2) × A)
    (supported : outcome ∈ support ((PqxdhDeploymentBackend.gameWith setup codec route
      PqxdhDeploymentIdealSteps.splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit
        identityIndex bounds mode adversary).run runtime))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (output : X)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (final : XState KemSK SplitBk 2)
    (reached : outcome.1 = some (created, output, ledger, final)) :
    DctInv setup codec t p ledger.transcript final := by
  simp only [PqxdhDeploymentBackend.gameWith, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, _, supported⟩ := supported
  rcases born with ⟨_ | constructed, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    cases reached
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    simp only [Option.some.injEq, Prod.mk.injEq] at reached
    obtain ⟨-, -, rfl, rfl⟩ := reached
    have flatEq := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (PqxdhDeploymentBackend.handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p constructed))
      (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)
      (PqxdhDeploymentInterface.asModeO mode adversary) PqxdhDeploymentSecrecy.Ledger.empty
      (PqxdhDeploymentBackend.xinitial constructed (PqxdhDeploymentIdealSteps.splitInit constructed))
    simp only [StateT.run] at flatEq
    simp only [PqxdhDeploymentSecrecy.wrap, StateT.run] at executedMember
    rw [flatEq, support_map] at executedMember
    obtain ⟨flat, flatMember, rfl⟩ := executedMember
    exact OracleComp.simulateQ_run_preserves_inv_of_query (splitLedgerHandler setup codec checks route t p bounds
      constructed) (fun state => DctInv setup codec t p state.1.transcript state.2)
      (fun query state inv result member => dctInv_step setup codec checks route t p phase2 frameBack bounds constructed
        query state inv result member)
      _ _ (dctInv_initial setup codec t p constructed) flat flatMember

/-- `world_dctInv` (design section 4.4): on every outcome of the record world with the ideal environment `envGD`, the reassembled final state, without the drawn parameters, satisfies the invariant at those parameters with the final transcript (through the support of `PqxdhDeploymentIdealEnv.c1_split`). -/
theorem world_dctInv {A X : Type} (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) ×
      PqxdhDeploymentEnvironment.EnvState KemSK (Params KemSK count × SplitBk)) × PqxdhRecordLiftWorld.State 2)
    (member : result ∈ support (PqxdhRecordLiftWorld.run setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode
        adversary))
    (value : PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK (Params KemSK count × SplitBk) 2)
    (joinedEq : PqxdhDeploymentEnvironmentJoin.joined result = some value) :
    DctInv setup codec t value.2.2.2.backend.1 value.2.2.1.transcript
      (PqxdhDeploymentEnvironmentDraw.dropX value.2.2.2) := by
  have inJoined : some value ∈ support (PqxdhDeploymentEnvironmentJoin.joined <$> PqxdhRecordLiftWorld.run setup codec
      route (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
        mode adversary) := by
    rw [support_map]
    exact ⟨result, member, joinedEq⟩
  rw [← PqxdhDeploymentIdealFrame.lawEq_support (PqxdhDeploymentIdealEnv.c1_split setup codec route checks t ensureInit
    identityIndex runtime bounds mode adversary), mem_support_bind_iff] at inJoined
  obtain ⟨drawn, _, inner⟩ := inJoined
  rw [support_map] at inner
  obtain ⟨outcome, outcomeMember, mapped⟩ := inner
  cases outcome with
  | none => cases mapped
  | some v =>
      simp only [Option.map_some, Option.some.injEq] at mapped
      subst mapped
      rw [StateT.run'_eq, support_map] at outcomeMember
      obtain ⟨full, fullMember, fullEq⟩ := outcomeMember
      exact split_dctInv setup codec checks route t drawn phase2 frameBack ensureInit identityIndex bounds mode adversary
        runtime full fullMember v.1 v.2.1 v.2.2.1 v.2.2.2 fullEq

end Game

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.build_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.build_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_command' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_command

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.coinSend_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.coinSend_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.dctInv_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.split_dctInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.split_dctInv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.world_dctInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant.world_dctInv
