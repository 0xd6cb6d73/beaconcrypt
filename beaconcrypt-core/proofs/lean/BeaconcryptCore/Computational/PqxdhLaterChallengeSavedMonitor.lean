import BeaconcryptCore.Computational.PqxdhLaterChallengeCapture
import BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler

/-! Split the actual saved callback from its carried outside continuation while retaining the complete instrumented state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C Value Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin B)

/-- Appending the actual outside continuation does not change the saved request address. -/
theorem append_address
    (outside : Value → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B) :
    PqxdhInitialBuilderContext.address (PqxdhLaterChallengeCapture.append outside context).original =
      PqxdhInitialBuilderContext.address context.original := by
  rcases context with ⟨(record | finish) | builder, trace, origin⟩ <;> rfl

/-- The actual complete descriptor's all-reply allowance already bounds its callback part. The quiet source continuation is retained unchanged. -/
theorem callback_fits
    (outside : Value → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost (PqxdhLaterChallengeCapture.append outside context)) :
    PqxdhInitialOriginCertificates.Fits qPost context := by
  rcases context with ⟨(⟨request, before, continuation, inner⟩ | ⟨index, before, control, candidate, continuation, inner⟩) | builder, trace, origin⟩
  case inr => exact fun reply => (fits reply).of_bind_left
  all_goals exact ⟨fun reply => (fits.1 reply).of_bind_left, fits.2⟩

/-- The saved request, both optional writers and all preparation effects are identical after splicing. Only the literal outside source program is extended. -/
theorem prepare_append
    (outside : Value → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (qCallback qPost : Nat)
    (callbackFits : PqxdhInitialOriginCertificates.Fits qCallback context)
    (fits : PqxdhInitialOriginCertificates.Fits qPost (PqxdhLaterChallengeCapture.append outside context))
    (localState : Local A N C) :
    PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux source writer prior target nonce next sender read
      qPost (PqxdhLaterChallengeCapture.append outside context) material fits localState =
    (fun result => (result.1 >>= outside, result.2)) <$>
      PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux source writer prior target nonce next sender read
        qCallback context material callbackFits localState := by
  rcases context with ⟨original, trace, origin⟩
  rcases original with (⟨request, before, continuation, inner⟩ | ⟨index, before, control, candidate, continuation, inner⟩) | builder
  all_goals simp only [PqxdhLaterChallengeCapture.append, PqxdhLaterSavedPostCompiler.prepare, map_bind, map_pure]
  rfl

/-- The complete saved callback hands its actual optional result and full instrumented state to the unchanged outside source program. Outer refusal keeps all completed work and state. -/
theorem complete_append
    (outside : Value → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (qCallback qPost : Nat)
    (callbackFits : PqxdhInitialOriginCertificates.Fits qCallback context)
    (fits : PqxdhInitialOriginCertificates.Fits qPost (PqxdhLaterChallengeCapture.append outside context))
    (localState : Local A N C) :
    PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark
      sender route read monitor qPost (PqxdhLaterChallengeCapture.append outside context) material fits localState = (do
    let result ← PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark
      sender route read monitor qCallback context material callbackFits localState
    match result.1 with
    | none => pure (none, result.2)
    | some value => ((simulateQ (insImpl pre application initial selector aux source writer prior
        (some ⟨PqxdhInitialBuilderContext.address context.original, material⟩) target nonce next sender route read mark monitor)
        (outside value)).run).run result.2) := by
  unfold PqxdhLaterSavedPostCompiler.complete
  rw [prepare_append pre application initial selector aux source writer prior target nonce next sender read outside context material qCallback qPost callbackFits fits localState]
  simp only [append_address, bind_map_left, bind_assoc, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  refine bind_congr fun prepared => bind_congr fun result => ?_
  rcases result with ⟨_ | value, state⟩ <;> rfl

/-- The literal outside wrapper retains its complete optional run and original output rule from any reached wrapper state. -/
theorem wrapped_run (parent : Entry) (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (current : PqxdhRecordConfidentialityChallenge.State)
    (before : InsState M P I D K A N C S B) :
    ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next sender route read mark monitor)
      (PqxdhLaterChallengeCapture.wrapped owner number bit work current)).run).run before =
    (fun result => (result.1.map (PqxdhRecordConfidentialityChallenge.output number), result.2)) <$>
      runStepper (simulateQ (PqxdhLaterChallengeTwin.handler pre application initial selector aux source writer prior parent target nonce next
        sender route read mark monitor owner number bit) work) current before := by
  unfold PqxdhLaterChallengeCapture.wrapped
  rw [simulateQ_map, PqxdhLaterChallengeTwin.program]
  simp only [runStepper, OptionT.run_map, StateT.run_map]

/-- Execute the captured callback once, then run its directly carried wrapper continuation with a private marker. The marker is operational data; source consumers must identify its value at this callback. -/
noncomputable def resume (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost details.callback)
    (localState : Local A N C) (choice : Option Bool) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (Option Bool × PqxdhLaterChallengeMonitor.State M P I D K A N C S B) := do
  let callback ← PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark
    sender route read monitor qPost details.callback material fits localState
  match callback.1 with
  | none => pure (none, (callback.2, choice))
  | some (reply, current) =>
    (fun result => (result.1.map (PqxdhRecordConfidentialityChallenge.output number), result.2)) <$>
      runStepper (simulateQ (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior
        ⟨PqxdhInitialBuilderContext.address details.callback.original, material⟩ target nonce next sender route read mark monitor
        owner number bit) (details.request.next reply)) current (callback.2, choice)

/-- Erasing the private marker returns the identical complete saved program, including all callback and outside effects on native failure or outer refusal. -/
theorem resume_erase (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (joined : PqxdhLaterChallengeCapture.Joined owner number bit (context, details))
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (callbackFits : PqxdhInitialOriginCertificates.Fits qPost details.callback)
    (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (localState : Local A N C) (choice : Option Bool) :
    Prod.map id Prod.fst <$> resume pre application initial selector aux source writer prior target nonce next sender route read mark monitor
      owner number bit details material qPost callbackFits localState choice =
    PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark sender route read monitor
      qPost context material fits localState := by
  change context = PqxdhLaterChallengeCapture.append
    (fun result => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next result.1) result.2) details.callback at joined
  subst context
  rw [complete_append pre application initial selector aux source writer prior target nonce next sender route read mark monitor _ details.callback material qPost qPost callbackFits fits localState]
  simp only [resume, map_bind]
  refine bind_congr fun callback => ?_
  rcases callback with ⟨_ | ⟨reply, current⟩, after⟩
  case none => rfl
  simp only [wrapped_run, Functor.map_map]
  rw [← PqxdhLaterChallengeMonitor.program_source pre application initial selector aux source writer prior
    ⟨PqxdhInitialBuilderContext.address details.callback.original, material⟩ target nonce next sender route read mark monitor
    owner number bit (details.request.next reply) current (after, choice), Functor.map_map]
  rfl

/-- The private monitor preserves every budget on the complete query tree, including callback work before refusal and every outside request. -/
theorem resume_budget {Budget : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (joined : PqxdhLaterChallengeCapture.Joined owner number bit (context, details))
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (callbackFits : PqxdhInitialOriginCertificates.Fits qPost details.callback)
    (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (localState : Local A N C) (choice : Option Bool)
    (budget : Budget) (allowed : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget) :
    (resume pre application initial selector aux source writer prior target nonce next sender route read mark monitor
      owner number bit details material qPost callbackFits localState choice).IsQueryBound budget allowed cost ↔
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark sender route read monitor
      qPost context material fits localState).IsQueryBound budget allowed cost := by
  rw [← resume_erase pre application initial selector aux source writer prior target nonce next sender route read mark monitor
    owner number bit details context joined material qPost callbackFits fits localState choice, isQueryBound_map_iff]

/-- The callback-only form of an actual saved Builder keeps every source field, its trace and origin. Only the explicit outside continuation becomes `pure`; no function is recovered. -/
def builderOnly (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Value S B)
    (trace : PqxdhInitialOriginPost.Trace Bool S B) (origin : Option Bool) :
    PqxdhInitialOriginContext.Context extra M P I D K PqxdhInitialBuilderContext.BuildResult Bool S B :=
  ⟨.inr { saved with outside := pure }, trace, origin⟩

/-- Appending the saved Builder's own outside continuation to its callback-only form gives back the exact descriptor. -/
theorem builder_append (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B)
    (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Value S B) (same : context.original = .inr saved) :
    PqxdhLaterChallengeCapture.append saved.outside (builderOnly saved context.trace context.origin) = context := by
  rcases context with ⟨original, trace, origin⟩
  change original = .inr saved at same
  subst same
  simp only [builderOnly, PqxdhLaterChallengeCapture.append, pure_bind]

/-- The callback-only Builder inherits its allowance from the actual descriptor. -/
theorem builder_fits (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B)
    (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Value S B) (same : context.original = .inr saved)
    (qPost : Nat) (fits : PqxdhInitialOriginCertificates.Fits qPost context) :
    PqxdhInitialOriginCertificates.Fits qPost (builderOnly saved context.trace context.origin) := by
  apply callback_fits saved.outside
  rw [builder_append context saved same]
  exact fits

/-- Execute the actual Builder callback once, then the adaptive adversary under the monitor from the wrapper's initial state with an unset marker. -/
noncomputable def builderResume (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : PqxdhInitialBuilderContext.BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (callback : PqxdhInitialOriginContext.Context extra M P I D K PqxdhInitialBuilderContext.BuildResult Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost callback) (localState : Local A N C) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (Option Bool × PqxdhLaterChallengeMonitor.State M P I D K A N C S B) := do
  let built ← PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark
    sender route read monitor qPost callback material fits localState
  match built.1 with
  | none => pure (none, (built.2, none))
  | some reply =>
    (fun result => (result.1.map (PqxdhRecordConfidentialityChallenge.output number), result.2)) <$>
      runStepper (simulateQ (PqxdhLaterChallengeMonitor.handler pre application initial selector aux source writer prior
        ⟨PqxdhInitialBuilderContext.address callback.original, material⟩ target nonce next sender route read mark monitor
        owner number bit) (work reply)) PqxdhRecordConfidentialityChallenge.initial (built.2, none)

/-- For a saved Builder whose literal outside continuation is the wrapper from its initial state, erasing the marker restores the complete saved program, including Builder effects, writer failures and outer refusal. -/
theorem builder_erase (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : PqxdhInitialBuilderContext.BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Bool S B) (same : context.original = .inr saved)
    (outside : saved.outside = fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (work reply)
      PqxdhRecordConfidentialityChallenge.initial)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (callbackFits : PqxdhInitialOriginCertificates.Fits qPost (builderOnly saved context.trace context.origin))
    (fits : PqxdhInitialOriginCertificates.Fits qPost context) (localState : Local A N C) :
    Prod.map id Prod.fst <$> builderResume pre application initial selector aux source writer prior target nonce next sender route read
      mark monitor owner number bit work (builderOnly saved context.trace context.origin) material qPost callbackFits localState =
    PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark sender route read
      monitor qPost context material fits localState := by
  have joined := builder_append context saved same
  rw [outside] at joined
  revert fits
  rw [← joined]
  intro fits
  rw [complete_append pre application initial selector aux source writer prior target nonce next sender route read mark monitor
    _ (builderOnly saved context.trace context.origin) material qPost qPost callbackFits fits localState]
  simp only [builderResume, map_bind]
  refine bind_congr fun built => ?_
  rcases built with ⟨_ | reply, after⟩
  case none => rfl
  simp only [wrapped_run, Functor.map_map]
  rw [← PqxdhLaterChallengeMonitor.program_source pre application initial selector aux source writer prior
    ⟨PqxdhInitialBuilderContext.address (builderOnly saved context.trace context.origin).original, material⟩ target nonce next sender
    route read mark monitor owner number bit (work reply) PqxdhRecordConfidentialityChallenge.initial (after, none), Functor.map_map]
  rfl

/-- The monitored Builder resume preserves every budget of the complete saved program, including Builder work before refusal and every later request. -/
theorem builder_budget {Budget : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (work : PqxdhInitialBuilderContext.BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Bool S B) (same : context.original = .inr saved)
    (outside : saved.outside = fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (work reply)
      PqxdhRecordConfidentialityChallenge.initial)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (callbackFits : PqxdhInitialOriginCertificates.Fits qPost (builderOnly saved context.trace context.origin))
    (fits : PqxdhInitialOriginCertificates.Fits qPost context) (localState : Local A N C)
    (budget : Budget) (allowed : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget) :
    (builderResume pre application initial selector aux source writer prior target nonce next sender route read mark monitor
      owner number bit work (builderOnly saved context.trace context.origin) material qPost callbackFits localState).IsQueryBound
      budget allowed cost ↔
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux source writer prior target nonce next mark sender route read
      monitor qPost context material fits localState).IsQueryBound budget allowed cost := by
  rw [← builder_erase pre application initial selector aux source writer prior target nonce next sender route read mark monitor
    owner number bit work context saved same outside material qPost callbackFits fits localState, isQueryBound_map_iff]

/-- In the two ordinary worlds, the Builder resume runs one identical callback and then the monitored adversary from the unused initial wrapper state. The pair is twin until the explicit private events; the inherited target-versus-parent address inequality stays a hypothesis. -/
theorem builder_pre (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (work : PqxdhInitialBuilderContext.BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (callback : PqxdhInitialOriginContext.Context extra M P I D K PqxdhInitialBuilderContext.BuildResult Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost callback) (localState : Local A N C)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠
      PqxdhInitialBuilderContext.address callback.original) :
    Pre (fun a b => a = b) (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (builderResume pre application initial selector aux source writer prior target nonce next sender route read mark monitor
        owner number false work callback material qPost fits localState)
      (builderResume pre application initial selector aux source writer prior target nonce next sender route read mark monitor
        owner number true work callback material qPost fits localState) := by
  unfold builderResume
  apply pre_bind_refl
  intro built _
  rcases built with ⟨_ | reply, after⟩
  · exact Pre.pure rfl
  · exact pre_map (PqxdhLaterChallengeMonitor.program_pre pre application initial selector aux source writer prior
      ⟨PqxdhInitialBuilderContext.address callback.original, material⟩ target nonce next sender route read mark monitor
      owner number (work reply) PqxdhRecordConfidentialityChallenge.initial rfl after separate)
      _ _ (fun _ _ same => by rw [same]) (fun _ dead => dead) (fun _ dead => dead)

end BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.append_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.append_address
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.callback_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.callback_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.prepare_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.prepare_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.complete_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.complete_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.wrapped_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.wrapped_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.resume_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.resume_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.resume_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.resume_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSavedMonitor.builder_pre
