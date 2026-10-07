-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptOrigin

/-! Mid-run report detection of raw-accept origin failures (CE-7, CE-A2 in signing-history form), stated for an arbitrary source14 program and instantiated for the common deployment experiment in `PqxdhDeploymentProvenance`. The program is stopped right after its raw accept at a chosen position (`upto`), so that the report run of the stopped program ends exactly when that accept and the public report batch that `PqxdhRegistrationJointRawReports.instrument` makes after every successful accept have run; resuming with the literal continuation recovers the original program and its report run (`upto_resume`, `run_upto`). `upto_detects` shows that the final report snapshot of the stopped run is the snapshot at which that accept's own batch was evaluated, so an original-field failure there raises the sticky report flag. `ViolationAt` is the native event at that accept: the accept returned a session handle, its raw bytes pass the native verification prefix with the identity key of a generated owner of the owner registry, the owner is unrevealed, and the verified key tuple is not among the owner's chronological signing attempts, failed publications included; all of it is read in the state reached when the accept returned, which the accept itself does not change for a Beacon owner's history or freshness. `violation_detects` turns it, through `AttemptReports.owner_origin` (the report-run form of `raw_origin`'s argument), into a failure detected by that accept's own report. `NativeForgery` is the event that the run passes through such an accept at some position, and continues to the final outcome; the position is existential, so one event covers every accept. Since the flag is sticky (`continuation_sticky`), every such final outcome has the flag raised (`forgery_detected`), and `forgery_bound` bounds the event by `PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum`: the sum over the `count + 1` generated identity positions of the ordinary joint-use weak-EUF advantages, with coefficient one, with no accept-position, owner, field or report-position factor and no collision term. The event is a set of final outcomes defined by reachability: a final outcome belongs to it when some execution path through a violating accept reaches it. This contains every final outcome of a path that actually passes through a violating accept, so the bound covers that path event; it can only be larger than it. The premises are the existing attached-signature format rule `shortRejects` (with `setup.wiring`) and the source caps that bound identity creation; no new assumption is used. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection
open PqxdhJointIdentity PqxdhDynamicIdentityReports PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhJointPhase1Reports (Monitor sourceImpl candidateAccepted FieldOriginFailure)
open PqxdhRegistrationJointRevealSchedule (Spec)
open PqxdhRegistrationJointAcceptCut (Cut scan finish)
open PqxdhRegistrationJointAcceptCutReports (resume continuation)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response X : Type}

/-- The state of a program stopped immediately after a selected raw accept returned: either the program completed before it, or the raw bytes, the public reply and the literal continuation. -/
inductive Stop (KemSK X : Type) where
  | done (result : X)
  | accepted (raw : Pqxdh.Bytes) (answer : Option Nat) (next : Option Nat → OracleComp (Spec KemSK) X)

/-- Execute the suspended raw accept and stop right after its reply. -/
noncomputable def stepAccept : Cut KemSK X → OracleComp (Spec KemSK) (Stop KemSK X)
  | .complete result => pure (.done result)
  | .pending raw next => (fun answer => Stop.accepted raw answer next) <$>
      ((Spec KemSK).query (.inl (.inr (.accept raw))) : OracleComp (Spec KemSK) _)

/-- The original program run up to and including its raw accept at zero-based position `index`, stopped right after that accept returned. -/
noncomputable def upto (work : OracleComp (Spec KemSK) X) (index : Nat) : OracleComp (Spec KemSK) (Stop KemSK X) :=
  scan work index >>= stepAccept

/-- Continue a stopped program with its literal continuation. -/
noncomputable def resumeStop : Stop KemSK X → OracleComp (Spec KemSK) X
  | .done result => pure result
  | .accepted _ answer next => next answer

/-- Stopping after the selected accept and resuming recovers the original program exactly. -/
theorem upto_resume (work : OracleComp (Spec KemSK) X) (index : Nat) : upto work index >>= resumeStop = work := by
  conv_rhs => rw [← PqxdhRegistrationJointAcceptCut.scan_finish work index]
  rw [upto, bind_assoc]
  apply bind_congr
  intro cut
  cases cut with
  | complete result => rfl
  | pending raw next => simp only [stepAccept, finish, bind_map_left, resumeStop]

/-- The report run of the original program is the report run of the stopped program followed by the literal continuation from the reached outcome. -/
theorem run_upto (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A) :
    PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count work runtime) =
      (PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count
          (upto work index) runtime) >>=
        continuation setup codec checks ensureInit count resumeStop) := by
  conv_lhs => rw [← upto_resume work index]
  exact PqxdhRegistrationJointAcceptCutReports.run_bind setup codec checks ensureInit supplied count _ _ runtime

/-- One step of the report interpreter never clears the sticky report flag. -/
theorem sourceImpl_sticky (joint : Primitives) (count : Nat) (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (state : Monitor count × ReportingState count)
    (result : PqxdhJointPhase1Reports.ProtocolSpec.Range query × (Monitor count × ReportingState count))
    (flag : state.1.occurred = true)
    (supported : result ∈ support ((sourceImpl joint count query).run state)) : result.2.1.occurred = true := by
  rw [sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at supported
  obtain ⟨inner, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  have reachable : inner.1 ∈ support ((PqxdhJointPhase1Reports.wrapper joint count query).run state.1) := by
    apply OracleComp.support_simulateQ_run'_subset (reportingImpl joint count) _ state.2
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, actual, rfl⟩
  have observed := (PqxdhJointPhase1Reports.wrapper_observation joint count query state.1 inner.1 reachable).2.2
  change inner.1.2.occurred = true
  rw [observed]
  cases query with
  | inl _ => exact flag
  | inr _ => simp [flag]

/-- Every continuation of a report run keeps a raised report flag raised. -/
theorem run_sticky {Result : Type} (joint : Primitives) (count : Nat)
    (client : OracleComp PqxdhJointPhase1Reports.ProtocolSpec Result) (state : Monitor count × ReportingState count)
    (flag : state.1.occurred = true) (result : Result × (Monitor count × ReportingState count))
    (supported : result ∈ support ((simulateQ (sourceImpl joint count) client).run state)) : result.2.1.occurred = true :=
  OracleComp.simulateQ_run_preserves_inv_of_query (sourceImpl joint count) (fun state => state.1.occurred = true)
    (fun query current held next member => sourceImpl_sticky joint count query current next held member)
    client state flag result supported

/-- Every continuation of a reached report outcome keeps its raised report flag raised. -/
theorem continuation_sticky {Y : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (next : X → OracleComp (Spec KemSK) Y)
    (reached : ReportResult KemSK A X count) (flag : reached.2.1.occurred = true)
    (final : ReportResult KemSK A Y count)
    (supported : final ∈ support (continuation setup codec checks ensureInit count next reached)) :
    final.2.1.occurred = true :=
  run_sticky setup.joint count _ reached.2 flag final supported

/-- Public reports pass through a stateful compiler without reading or changing its state. -/
theorem extend_report {κ κ' S : Type} {source : OracleSpec κ'} {target : OracleSpec κ}
    (impl : QueryImpl source (StateT S (OracleComp target))) (codec : Codec Reader Response) (count : Nat)
    (query : (Spec KemSK).Domain) (answer : (Spec KemSK).Range query) (state : S) :
    (simulateQ (PqxdhRegistrationJointReportLift.extend impl)
      (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) (source := source) codec count query answer)).run state =
      (fun _ => ((), state)) <$> (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count query answer :
        OracleComp (PqxdhRegistrationJointReportLift.Spec target) Unit) := by
  unfold PqxdhRegistrationJointRawReports.report
  split
  · split
    · rfl
    · exact PqxdhRegistrationJointTerminalReports.extend_batch impl _ _ state
  · rfl

/-- The reported command compiler on the suspended raw accept: the accept command, then its public report, then the stopped program state with the accept's reply. -/
theorem reported_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (count : Nat) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (Spec KemSK) X) (state : PqxdhRegistrationJointReportCommands.State KemSK) :
    (PqxdhRegistrationJointReportCommands.reported setup codec checks identityIndex publicIdentity count
      (stepAccept (.pending raw next))).run state =
      (PqxdhRegistrationJointReportLift.lift (PqxdhRegistrationJointReportCommands.commands setup codec checks identityIndex
        publicIdentity ((Spec KemSK).query (.inl (.inr (.accept raw)))) state) >>= fun step =>
        (fun _ => (Stop.accepted raw step.1 next, step.2)) <$>
          (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count (.inl (.inr (.accept raw))) step.1 :
            OracleComp (PqxdhRegistrationJointReportLift.Spec (PqxdhRegistrationJointReportCommands.Birth KemSK)) Unit)) := by
  simp only [PqxdhRegistrationJointReportCommands.reported, stepAccept, simulateQ_map, simulateQ_spec_query,
    PqxdhRegistrationJointRawReports.instrument, simulateQ_bind, simulateQ_pure, StateT.run_map, StateT.run_bind,
    StateT.run_pure, PqxdhRegistrationJointReportLift.extend, map_bind]
  apply bind_congr
  intro step
  rw [extend_report]
  simp only [map_pure, bind_pure_comp, Functor.map_map]

/-- The identity reduction passes a public report through unchanged, keeping its local and routing states. -/
theorem reduction_report (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (codec : Codec Reader Response) (count : Nat) (query : (Spec KemSK).Domain) (answer : (Spec KemSK).Range query)
    (localState : PqxdhRegistrationJointIdentityCompiler.Local KemSK A)
    (registry : PqxdhRegistrationJointIdentityRouting.Registry) :
    PqxdhRegistrationJointReportCompiler.reduction setup ensureInit
        (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count query answer) localState registry =
      (fun _ => (((), localState), registry)) <$>
        (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count query answer :
          OracleComp PqxdhJointPhase1Reports.ProtocolSpec Unit) := by
  simp only [PqxdhRegistrationJointReportCompiler.reduction, extend_report, simulateQ_map, StateT.run_map,
    Functor.map_map]

/-- The continuation of a reached pending raw cut by the stopping step: the accept command runs, then its public report runs from the reached report state, and nothing after it. The final outcome records the raw bytes, the reply and the literal continuation, and its report state is the result of the public report. -/
theorem continuation_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (reached : ReportResult KemSK A (Cut KemSK X) count)
    (outcome : PqxdhRegistrationJointOpenInitialization.Outcome KemSK (Cut KemSK X))
    (found : reached.1.1.1 = some outcome) (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) X)
    (pending : outcome.2.1 = .pending raw next) (final : ReportResult KemSK A (Stop KemSK X) count)
    (supported : final ∈ support (continuation setup codec checks ensureInit count stepAccept reached)) :
    ∃ (answer : Option Nat)
      (rest : PqxdhServerAuthNative.NativeState KemSK × List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
      (middle : Monitor count × ReportingState count),
      final.1.1.1 = some (outcome.1, .accepted raw answer next, rest) ∧
      ((), final.2) ∈ support ((simulateQ (sourceImpl setup.joint count)
        (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count (.inl (.inr (.accept raw))) answer)).run
          middle) := by
  rcases outcome with ⟨created, cut, encoded⟩
  dsimp only at pending
  subst pending
  simp only [continuation, found, resume, reported_step, map_bind,
    PqxdhRegistrationJointTerminalReports.compiler_bind, PqxdhRegistrationJointAcceptCutReports.reduction_map,
    reduction_report, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map, mem_support_bind_iff,
    support_map, Set.mem_image] at supported
  obtain ⟨step, _, _, ⟨_, ⟨⟨⟨⟩, after⟩, reportMember, rfl⟩, rfl⟩, rfl⟩ := supported
  exact ⟨step.1.1.1.1, (step.1.1.1.2.2, step.1.1.1.2.1), step.2, rfl, reportMember⟩

/-- A stopped outcome that records a reply of the selected accept came from a pending raw cut: the cut's continuation by the stopping step either keeps a failed constructor, or completes the program before the cut, or records the accept with its raw bytes. -/
theorem continuation_accepted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (count : Nat) (reached : ReportResult KemSK A (Cut KemSK X) count)
    (final : ReportResult KemSK A (Stop KemSK X) count)
    (supported : final ∈ support (continuation setup codec checks ensureInit count stepAccept reached))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (raw : Pqxdh.Bytes) (answer : Option Nat)
    (next : Option Nat → OracleComp (Spec KemSK) X)
    (rest : PqxdhServerAuthNative.NativeState KemSK × List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (stopped : final.1.1.1 = some (created, .accepted raw answer next, rest)) :
    ∃ (middle : Monitor count × ReportingState count),
      ((), final.2) ∈ support ((simulateQ (sourceImpl setup.joint count)
        (PqxdhRegistrationJointRawReports.report (KemSK := KemSK) codec count (.inl (.inr (.accept raw))) answer)).run
          middle) := by
  cases found : reached.1.1.1 with
  | none =>
      simp only [continuation, found, resume, PqxdhRegistrationJointReportCompiler.reduction, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases stopped
  | some outcome =>
      rcases outcome with ⟨outcomeCreated, cut, encoded⟩
      cases cut with
      | complete result =>
          simp only [continuation, found, resume, stepAccept, PqxdhRegistrationJointReportCommands.reported,
            PqxdhRegistrationJointReportCompiler.reduction, simulateQ_pure, StateT.run_pure, map_pure, support_pure,
            Set.mem_singleton_iff] at supported
          subst supported
          cases stopped
      | pending pendingRaw pendingNext =>
          obtain ⟨reply, other, middle, recorded, reportMember⟩ := continuation_step setup codec checks ensureInit count
            reached _ found pendingRaw pendingNext rfl final supported
          rw [recorded] at stopped
          simp only [Option.some.injEq, Prod.mk.injEq, Stop.accepted.injEq] at stopped
          obtain ⟨_, ⟨rfl, rfl, _⟩, _⟩ := stopped
          exact ⟨middle, reportMember⟩

/-- Mid-run detection at the selected accept. In the report run of the program stopped right after its raw accept at position `index`, suppose that accept returned a session handle and its unchanged raw candidate is an original-field failure at some generated index in the final report snapshot. Then the report flag is raised. The final report snapshot is the snapshot at which that accept's own public report batch was evaluated, so the failure is detected by the report made at that accept, not by a later or terminal report. -/
theorem upto_detects (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (final : ReportResult KemSK A (Stop KemSK X) count)
    (supported : final ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (upto work index)
        runtime)))
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Stop KemSK X))
    (finished : (sourceResult final).1 = some encoded) (raw : Pqxdh.Bytes) (session : Nat)
    (next : Option Nat → OracleComp (Spec KemSK) X) (stopped : encoded.2.1 = .accepted raw (some session) next)
    (candidate : Phase1Candidate) (parsed : PqxdhRegistrationJointRawSignatures.candidate codec raw = some candidate)
    (target : Nat) (failure : FieldOriginFailure setup.joint ⟨target, candidate⟩ final.2.1.snapshot) :
    final.2.1.occurred = true := by
  rw [upto, PqxdhRegistrationJointAcceptCutReports.run_bind, mem_support_bind_iff] at supported
  obtain ⟨reached, _, continued⟩ := supported
  change Option.map _ final.1.1.1 = some encoded at finished
  obtain ⟨recorded, found, rfl⟩ := Option.map_eq_some_iff.mp finished
  rcases recorded with ⟨created, stop, rest⟩
  simp only [PqxdhRegistrationJointOpenInitialization.attach] at stopped
  subst stopped
  obtain ⟨middle, reportMember⟩ := continuation_accepted setup codec checks ensureInit count reached final continued
    created raw (some session) next rest found
  simp only [PqxdhRegistrationJointRawReports.report, parsed] at reportMember
  obtain ⟨snapshot, occurred⟩ := PqxdhRegistrationJointTerminalReports.source_batch setup.joint count (List.range count)
    candidate middle ((), final.2) reportMember
  rw [snapshot] at failure
  rw [occurred, Bool.or_eq_true]
  exact Or.inr (List.any_eq_true.mpr ⟨target, List.mem_range.mpr failure.1,
    (PqxdhJointPhase1Reports.candidateAccepted_iff setup.joint ⟨target, candidate⟩ middle.1.snapshot).mpr failure⟩)

/-- Native origin failure at the selected accept, with explicit witnesses, read in the state reached when that accept returned and before any later command: the accept returned a session handle; its raw bytes pass the native verification prefix with a verified value whose identity key is the public identity key of the generated owner at `address` of the owner registry; that owner's identity is unrevealed; and the verified key tuple is not one of that owner's chronological signing attempts, failed publications included. The accept itself neither signs nor reveals for a Beacon owner, so these are the owner's history and freshness at the accept. -/
def ViolationAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (stopped : ReportResult KemSK A (Stop KemSK X) count)
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (Stop KemSK X)) (raw : Pqxdh.Bytes)
    (session : Nat) (next : Option Nat → OracleComp (Spec KemSK) X)
    (value : PqxdhServerRootPreparation.Verified Reader) (address : Nat)
    (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (target : Fin count) (publicKey : PublicIdentity) :
    Prop :=
  (sourceResult stopped).1 = some encoded ∧ encoded.2.1 = .accepted raw (some session) next ∧
    PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
    encoded.2.2.owners[address]? = some owner ∧
    stopped.1.2.refs[owner.1]? = some (.generated target.val) ∧
    sourceKeys setup.joint (sourceResult stopped).2.1.1.seeds owner.1 = some publicKey ∧
    value.identity = publicKey.ed25519 ∧
    PqxdhRegistrationJointRoutedReveals.revealedAt owner.1 (sourceResult stopped).2.1.1.transcript = false ∧
    ¬PqxdhRegistrationJointAttemptDecoding.Occurred value.keys
      (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult stopped).2.1.1.transcript)

/-- Some witnesses make the stopped outcome a native origin failure at its selected accept. -/
def Violation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (stopped : ReportResult KemSK A (Stop KemSK X) count) : Prop :=
  ∃ encoded raw session next value address owner target publicKey,
    ViolationAt setup codec checks stopped encoded raw session next value address owner target publicKey

/-- Mid-run report detection of a native origin failure: the report made at the selected accept raises the report flag. `raw_origin`'s argument, in its report-run form `AttemptReports.owner_origin`, turns the absent tuple into an unissued original field fresh at that accept, and `upto_detects` shows that the accept's own report batch recognizes it. The only premise beyond the execution is the existing attached-signature format rule `shortRejects`. -/
theorem violation_detects (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (runtime : A)
    (stopped : ReportResult KemSK A (Stop KemSK X) count)
    (supported : stopped ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (upto work index)
        runtime)))
    (violation : Violation setup codec checks stopped) : stopped.2.1.occurred = true := by
  obtain ⟨encoded, raw, session, next, value, address, owner, target, publicKey, finished, recorded, attached, found,
    generated, key, identity, fresh, absent⟩ := violation
  obtain ⟨parsed, accepted⟩ := PqxdhRegistrationJointAcceptOrigin.attached_detached setup codec checks shortRejects raw
    value attached
  rw [identity] at accepted
  obtain ⟨receipt, _, exactHistory, _, origin⟩ := PqxdhRegistrationJointAttemptReports.owner_origin setup codec checks
    ensureInit supplied count (upto work index) runtime stopped supported encoded finished address owner found target
    generated publicKey value.candidate value.keys key accepted fresh
  rcases origin with issued | forged
  · rw [exactHistory, PqxdhRegistrationJointAttemptDecoding.occurred_iff] at absent
    exact absurd issued absent
  · exact upto_detects setup codec checks ensureInit supplied count work index runtime stopped supported encoded finished
      raw session next recorded value.candidate parsed target.val forged

/-- CE-A2 event on the whole report run (signing-history form): the run passes through some raw accept whose stopped outcome is a native origin failure, and continues from it to the final outcome. The raw-accept position is existential, so every accept of the run is covered by this one event. -/
def NativeForgery (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (final : ReportResult KemSK A X count) : Prop :=
  ∃ (index : Nat) (stopped : ReportResult KemSK A (Stop KemSK X) count),
    stopped ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count (upto work index)
        runtime)) ∧
    final ∈ support (continuation setup codec checks ensureInit count resumeStop stopped) ∧
    Violation setup codec checks stopped

/-- Every final outcome that passes through a native origin failure at some accept has its report flag raised. -/
theorem forgery_detected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (final : ReportResult KemSK A X count)
    (forgery : NativeForgery setup codec checks ensureInit supplied count work runtime final) :
    final.2.1.occurred = true := by
  obtain ⟨index, stopped, stoppedMember, continued, violation⟩ := forgery
  exact continuation_sticky setup codec checks ensureInit count resumeStop stopped
    (violation_detects setup codec checks shortRejects ensureInit supplied count work index runtime stopped
      stoppedMember violation) final continued

/-- The ordinary joint-use weak-EUF reduction at generated position `target` for the report run of a source14 program. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) (target : Fin (count + 1)) :=
  PqxdhJointIdentityFreshness.globalReduction setup.joint target ordinaryFallback
    (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
      (PqxdhDynamicIdentityReports.reportExtractor setup.joint (count + 1) fallback
        (PqxdhJointPhase1Reports.routedClient setup.joint (count + 1)
          (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1) work
            runtime))))

/-- Factor-free CE-A2 bound for an arbitrary source14 program: the probability that the report run passes through a raw accept that is a native origin failure, at any position, is at most the sum over the `count + 1` generated identity positions of the ordinary joint-use weak-EUF advantages, with coefficient one. There is no accept-position, owner, field or report-position factor and no collision term. -/
theorem forgery_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 →
      setup.source.crypto.verify publicKey.toList bytes = none)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (work : OracleComp (Spec KemSK) X) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (capacity : (if supplied.isNone then 1 else 0) + budget (.inl 1) ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (NativeForgery setup codec checks ensureInit supplied (count + 1) work runtime final)) <$>
      PqxdhJointPhase1Reports.run setup.joint (count + 1)
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied (count + 1) work
          runtime)] {true} ≤
      ∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (reduction setup codec checks ensureInit supplied count work runtime fallback ordinaryFallback target) := by
  classical
  have creates := PqxdhRegistrationJointReportCosts.initialized_creates setup codec checks ensureInit supplied (count + 1)
    work runtime budget certified
  refine le_trans ?_ (PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint count _ fallback ordinaryFallback
    (creates.mono capacity))
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro final _ forgery
  exact forgery_detected setup codec checks shortRejects ensureInit supplied (count + 1) work runtime final
    (of_decide_eq_true forgery)

end BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.upto_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.upto_resume

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.run_upto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.run_upto

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.sourceImpl_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.sourceImpl_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.run_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.run_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.continuation_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.continuation_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.extend_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.extend_report

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.reported_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.reported_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.reduction_report' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.reduction_report

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.continuation_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.continuation_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.continuation_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.continuation_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.upto_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.upto_detects

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.violation_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.violation_detects

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.forgery_detected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.forgery_detected

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.forgery_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentAcceptDetection.forgery_bound
