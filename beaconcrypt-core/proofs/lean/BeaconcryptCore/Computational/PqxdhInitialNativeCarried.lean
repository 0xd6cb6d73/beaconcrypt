import BeaconcryptCore.Computational.PqxdhInitialNativePrefix
import BeaconcryptCore.Computational.PqxdhInitialNativeResponse
import BeaconcryptCore.Computational.PqxdhInitialOriginCertificates

/-!
The actual first-builder and complete adaptive post client supply the carried predecessor sampler. Every descriptor is emitted by its original source query before that query executes. The same sampler retains the complete primitive, identity, root-cache, selective-table and chronological state in both adjacent chain stages. Its selected cache-hit and fresh-miss cases remain separate.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeCarried
open PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhInitialPostContext PqxdhInitialBuilderContext
open PqxdhInitialNativeLog PqxdhInitialNativePrefix PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

structure Execution (extra : OracleSpec ι) (M P I D K Result Origin : Type) (S B : Nat) where
  initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)
  index : Fin S
  metadata : P
  ready : PqxdhPrivateAcceptedRoot.Ready
  outside : BuildResult → OracleComp (PostSpec extra S B) Result
  before : NativeFront M P I D K S B
  trace : PqxdhInitialOriginPost.Trace Origin S B
  origin : Origin

abbrev Context := @PqxdhInitialOriginContext.Context ι
abbrev Final (M P I D K Result Origin : Type) (S B : Nat) :=
  Result × (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)
abbrev Carried (extra : OracleSpec ι) (M P I D K Result Origin A N C : Type) (S B : Nat) :=
  RawCtxForwardScan.Cut (Context extra M P I D K Result Origin S B)
    (Final M P I D K Result Origin S B) (State A N C)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)

noncomputable def code :=
  PqxdhInitialOriginForwardBuilder.program (X := X) (Response := Response) source mark execution.origin sender route decode
    execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace

private theorem selection (depth : Nat)
    (query : (Base extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (chosen : selected (extra := extra) depth query state = true) : PqxdhInitialForwardPost.selected query = true := by
  cases query with
  | inl query => exact RawCtxFirstParentPrefix.selected_private depth query state.1 chosen
  | inr query => cases chosen

noncomputable def carried (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state : State A N C) : ProbComp (Carried extra M P I D K Result Origin A N C S B) :=
  RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (selected (extra := extra) depth) (selection depth)
    (handler source writer stage external) (code source mark sender route decode execution)
    (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
      execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state


/-- Annotated scanners retain the same literal descriptor when every actual unselected callback preserves an invariant and both complete callback computations agree there. -/
theorem annotated_same {Tag Value State ι : Type} {base : OracleSpec ι}
    (privateQuery : base.Domain → Bool) (chosen : base.Domain → State → Bool)
    (selection : ∀ query state, chosen query state = true → privateQuery query = true)
    (left right : QueryImpl base (StateT State ProbComp)) (valid : State → Prop)
    (agree : ∀ query state, valid state → chosen query state = false →
      (left query).run state = (right query).run state)
    (preserve : ∀ query state, valid state → chosen query state = false →
      ∀ reply ∈ support ((left query).run state), valid reply.2)
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag base) Value)
    (covered : RawCtxForwardCoverage.Covered privateQuery client)
    (state : State) (initial : valid state) :
    RawCtxForwardScan.scan privateQuery chosen selection left client covered state =
      RawCtxForwardScan.scan privateQuery chosen selection right client covered state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    cases selected : chosen query.2 state with
    | true =>
      rw [RawCtxForwardScan.scan_cut privateQuery chosen selection left query next covered state selected,
        RawCtxForwardScan.scan_cut privateQuery chosen selection right query next covered state selected]
    | false =>
      rw [RawCtxForwardScan.scan_other privateQuery chosen selection left query next covered state selected,
        RawCtxForwardScan.scan_other privateQuery chosen selection right query next covered state selected,
        ← agree query.2 state initial selected]
      apply bind_congr_of_forall_mem_support
      intro reply supported
      exact ih reply.1 (covered.2 reply.1) reply.2 (preserve query.2 state initial selected reply supported)

/-- The actual carried source sampler is identical in both adjacent stages, including the literal descriptor and every retained state field. -/
theorem carried_same (depth : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state : State A N C) (valid : Depth depth state) :
    carried source writer mark sender route decode execution depth (depth + 1) external state =
      carried source writer mark sender route decode execution depth (depth + 2) external state :=
  annotated_same PqxdhInitialForwardPost.selected (selected (extra := extra) depth) (selection depth) _ _ (Depth depth)
    (fun query reached invariant _ => step_same source writer depth external query reached invariant)
    (fun query reached invariant unchosen reply supported =>
      step_preserve source writer (depth + 1) depth external query reached invariant unchosen reply supported)
    _ _ state valid

noncomputable def original :=
  (PqxdhInitialOriginPost.sequence (X := X) (Response := Response) source execution.initial mark execution.origin
    sender route decode execution.index execution.metadata execution.ready execution.outside).run (execution.before, execution.trace)

/-- Packing the actual returned descriptor is the exact full pending prefix of the original builder and complete post source. -/
theorem carried_pack (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state : State A N C) :
    RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) <$>
        carried source writer mark sender route decode execution depth stage external state =
      RawCtxStatefulPendingPrefix.scan (selected (extra := extra) depth) (handler source writer stage external)
        (original source mark sender route decode execution) state := by
  simpa only [carried, code, original, PqxdhInitialOriginForwardBuilder.program_erase] using
    RawCtxForwardScan.scan_pack PqxdhInitialForwardPost.selected (selected (extra := extra) depth) (selection depth)
      (handler source writer stage external) (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (code source mark sender route decode execution)
      (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
        execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace)
      (PqxdhInitialOriginForwardBuilder.program_sound source mark execution.origin sender route decode
        execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state

/-- Resuming the actual carried prefix runs the same dependent query and complete source continuation without dropping any private effect. -/
theorem carried_finish (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state : State A N C) :
    (carried source writer mark sender route decode execution depth stage external state >>= fun cut =>
      RawCtxPendingMixedPrefix.finish (handler source writer stage external)
        (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) cut)) =
      (simulateQ (handler source writer stage external) (original source mark sender route decode execution)).run state := by
  simpa only [carried, code, original, PqxdhInitialOriginForwardBuilder.program_erase] using
    RawCtxForwardScan.scan_finish PqxdhInitialForwardPost.selected (selected (extra := extra) depth) (selection depth)
      (handler source writer stage external) (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (code source mark sender route decode execution)
      (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
        execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace)
      (PqxdhInitialOriginForwardBuilder.program_sound source mark execution.origin sender route decode
        execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state

/-- Every supported saved context has its own source-derived remaining-work certificate, including its complete origin metadata. -/
theorem carried_fits (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state reached : State A N C) (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer mark sender route decode execution depth stage external state)) :
    PqxdhInitialOriginCertificates.Fits qPost context :=
  PqxdhInitialOriginCertificates.carried_fits source mark execution.origin sender route decode
    execution.initial execution.index execution.metadata execution.ready execution.outside qPost bounded execution.before execution.trace
    (selected (extra := extra) depth) (selection depth) (handler source writer stage external) state reached context supported

/-- The actual saved predecessor is selected at its reached state and occurs with its full continuation in the original source execution. -/
theorem carried_origin (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C) (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer mark sender route decode execution depth stage external state)) :
    selected (extra := extra) depth (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1 reached = true ∧
      RawCtxQueryOccurrence.Occurs (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1
        (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).2
        (original source mark sender route decode execution) := by
  simpa only [code, original, PqxdhInitialOriginForwardBuilder.program_erase] using
    RawCtxForwardScan.pending_origin PqxdhInitialForwardPost.selected (selected (extra := extra) depth) (selection depth)
      (handler source writer stage external) (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (code source mark sender route decode execution)
      (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
        execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace)
      (PqxdhInitialOriginForwardBuilder.program_sound source mark execution.origin sender route decode
        execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace)
      state reached context supported

/-- The actual reached private table is covered by its chronological source input log; neither an unexecuted selected query nor an external callback creates past provenance. -/
theorem carried_covered (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C) (covered : Covered state) (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer mark sender route decode execution depth stage external state)) : Covered reached := by
  have mapped : RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode)
      (RawCtxForwardScan.Cut.pending context reached) ∈ support
      (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode) <$>
        carried source writer mark sender route decode execution depth stage external state) := by
    rw [support_map]
    exact ⟨RawCtxForwardScan.Cut.pending context reached, supported, rfl⟩
  rw [carried_pack] at mapped
  exact PqxdhInitialNativeLog.scan_covered source writer stage external (selected (extra := extra) depth)
    (original source mark sender route decode execution) state covered _ mapped

/-- A supported actual cut is a matching earlier recorded cache hit or a fresh miss at the requested predecessor depth. -/
theorem carried_cases (depth stage : Nat)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C) (covered : Covered state) (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer mark sender route decode execution depth stage external state)) :
    RawCtxSelectiveChainGame.matched reached.1.1.2.2 (address context.original) = true ∧
      (((address context.original) ∈ reached.1.2 ∧ ∃ output, reached.1.1.2.1 (address context.original) = some output) ∨
        (reached.1.1.2.1 (address context.original) = none ∧ reached.1.1.2.2.depth = depth)) := by
  exact selected_cases depth (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1 reached
    (carried_covered source writer mark sender route decode execution depth stage external state reached covered context supported)
    (address context.original) (PqxdhInitialBuilderContext.frame_address sender route decode context.original)
    (carried_origin source writer mark sender route decode execution depth stage external state reached context supported).1

/-- On the actual miss branch, the supported source cut draws precisely one full76 response and updates the whole original cache/cursor/log state. -/
theorem carried_miss (depth stage runStage : Nat) (before : depth < runStage)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))
    (state reached : State A N C) (covered : Covered state) (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer mark sender route decode execution depth stage external state))
    (missing : reached.1.1.2.1 (address context.original) = none) :
    (handler source writer runStage external
      (PqxdhInitialOriginContext.frame (X := X) (Response := Response) mark sender route decode context).1).run reached =
      (fun output => (PqxdhInitialParentBuilderContext.reply sender route decode context.original output,
        PqxdhInitialNativeResponse.updated (address context.original) output reached)) <$> ($ᵗ FullOutput) := by
  have cases := carried_cases source writer mark sender route decode execution depth stage external state reached covered context supported
  have actualDepth : reached.1.1.2.2.depth = depth := by
    rcases cases.2 with hit | miss
    · obtain ⟨output, found⟩ := hit.2
      rw [missing] at found
      cases found
    · exact miss.2
  exact PqxdhInitialNativeResponse.origin_frame_miss source writer runStage external mark sender route decode context reached missing cases.1
    (by simpa only [actualDepth] using before)

end BeaconcryptCore.Computational.PqxdhInitialNativeCarried

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.annotated_same' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.annotated_same
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_same
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_pack
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_finish
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_origin
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_covered
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_cases
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeCarried.carried_miss
