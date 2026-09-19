import BeaconcryptCore.Computational.PqxdhInitialNativeAudit
import BeaconcryptCore.Computational.PqxdhInitialNativeCarried
import BeaconcryptCore.Computational.PqxdhInitialPendingSourceBounds

/-!
The original annotated first-builder and full post program select their literal saved descriptor while carrying the complete native candidate audit. Both adjacent stages use the same entire sampler, including every candidate and state field. A saved descriptor exposes its actual pre-operation disclosure history directly. The stopped observer starts from those known disclosures and the chronological audit, rather than reconstructing metadata from an opaque continuation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient PqxdhInitialNativeAudit
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Execution := @PqxdhInitialNativeCarried.Execution ι
abbrev Context := @PqxdhInitialOriginContext.Context ι
abbrev Final := PqxdhInitialNativeCarried.Final
abbrev Carried (extra : OracleSpec ι) (M P I D K Result Origin A N C : Type) (S B : Nat) :=
  RawCtxForwardScan.Cut (Context extra M P I D K Result Origin S B)
    (Final M P I D K Result Origin S B) (State A N C)

def selected (depth : Nat) (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C) : Bool :=
  PqxdhInitialNativePrefix.selected depth query state.1

def Depth (depth : Nat) (state : State A N C) : Prop := PqxdhInitialNativePrefix.Depth depth state.1

private theorem selection (depth : Nat)
    (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (chosen : selected depth query state = true) : PqxdhInitialForwardPost.selected query = true := by
  cases query with
  | inl query => exact RawCtxFirstParentPrefix.selected_private depth query state.1.1 chosen
  | inr query => cases chosen

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The entire audited callback, including actual initializer roots and all candidate bytes, agrees in the two adjacent stages before the selected predecessor. -/
theorem step_same (depth : Nat) (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : State A N C) (valid : Depth depth state) :
    (handler source writer (depth + 1) pre application initial selector aux query).run state =
      (handler source writer (depth + 2) pre application initial selector aux query).run state := by
  cases query with
  | inr query => rcases query with query | (reply | (secrets | (query | query))) <;> rfl
  | inl query =>
      exact congrArg (fun work : ProbComp ((RawCtxPendingSelectiveFamily.Spec S B).Range query × PqxdhInitialNativeLog.State A N C) =>
        work >>= fun reply => pure (reply.1, (reply.2, state.2 ++ liveInputs query)))
        (PqxdhInitialNativePrefix.step_same source writer depth (external pre application initial selector aux) (.inl query) state.1 valid)

/-- Original unselected callbacks preserve the source depth even with the complete audit retained. -/
theorem step_preserve (stage depth : Nat) (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : State A N C) (valid : Depth depth state) (unchosen : selected depth query state = false)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage pre application initial selector aux query).run state)) :
    Depth depth result.2 := by
  apply PqxdhInitialNativePrefix.step_preserve source writer stage depth (external pre application initial selector aux)
    query state.1 valid unchosen (result.1, result.2.1)
  rw [← query_erase source writer stage pre application initial selector aux query state]
  rw [support_map]
  exact ⟨result, supported, rfl⟩

variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)

noncomputable def carried (depth stage : Nat) (state : State A N C) : ProbComp (Carried extra M P I D K Result Origin A N C S B) :=
  RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (selected depth) (selection depth)
    (handler source writer stage pre application initial selector aux)
    (PqxdhInitialNativeCarried.code source mark sender route decode execution)
    (PqxdhInitialOriginForwardBuilder.program_covered source mark execution.origin sender route decode
      execution.initial execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state

/-- The actual saved descriptor, entire native state and chronological candidate list share one identical sampler in adjacent selective stages. -/
theorem carried_same (depth : Nat) (state : State A N C) (valid : Depth depth state) :
    carried source writer pre application initial selector aux mark sender route decode execution depth (depth + 1) state =
      carried source writer pre application initial selector aux mark sender route decode execution depth (depth + 2) state :=
  PqxdhInitialNativeCarried.annotated_same PqxdhInitialForwardPost.selected (selected depth) (selection depth) _ _ (Depth depth)
    (fun query reached invariant _ => step_same source writer pre application initial selector aux depth query reached invariant)
    (fun query reached invariant unchosen reply supported =>
      step_preserve source writer pre application initial selector aux (depth + 1) depth query reached invariant unchosen reply supported)
    _ _ state valid

def eraseCut {Tag Value : Type} : RawCtxForwardScan.Cut Tag Value (State A N C) →
    RawCtxForwardScan.Cut Tag Value (PqxdhInitialNativeLog.State A N C)
  | .complete result state => .complete result state.1
  | .pending tag state => .pending tag state.1

private theorem scan_projection {Tag Value : Type} (depth stage : Nat)
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag (Spec extra RatchetChain I D K X Response Shared S B)) Value)
    (covered : RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected client)
    (state : State A N C) :
    eraseCut <$> RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (selected depth) (selection depth)
        (handler source writer stage pre application initial selector aux) client covered state =
      RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (PqxdhInitialNativePrefix.selected depth)
        (fun query native chosen => selection depth query (native, []) chosen)
        (PqxdhInitialNativeLog.handler source writer stage (external pre application initial selector aux)) client covered state.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      cases chosen : selected depth query.2 state with
      | true =>
          rw [RawCtxForwardScan.scan_cut _ _ _ _ query next covered state chosen,
            RawCtxForwardScan.scan_cut _ _ _ _ query next covered state.1 chosen, map_pure]
          rfl
      | false =>
          rw [RawCtxForwardScan.scan_other _ _ _ _ query next covered state chosen,
            RawCtxForwardScan.scan_other _ _ _ _ query next covered state.1 chosen, map_bind,
            ← query_erase source writer stage pre application initial selector aux query.2 state, bind_map_left]
          exact bind_congr fun reply => ih reply.1 (covered.2 reply.1) reply.2

/-- Erasing the added audit from the carried source sampler preserves the literal original descriptor, rather than recovering it from a continuation projection. -/
theorem carried_projection (depth stage : Nat) (state : State A N C) :
    eraseCut <$> carried source writer pre application initial selector aux mark sender route decode execution depth stage state =
      PqxdhInitialNativeCarried.carried source writer mark sender route decode execution depth stage
        (external pre application initial selector aux) state.1 :=
  scan_projection source writer pre application initial selector aux depth stage _ _ state

def cutState {Tag Value : Type} : RawCtxForwardScan.Cut Tag Value (State A N C) → State A N C
  | .complete _ state | .pending _ state => state

private theorem scan_audit {Tag Value : Type} (depth stage : Nat)
    (client : OracleComp (RawCtxForwardAnnotation.Spec Tag (Spec extra RatchetChain I D K X Response Shared S B)) Value)
    (covered : RawCtxForwardCoverage.Covered PqxdhInitialForwardPost.selected client)
    (budget : Nat) (bounded : (simulateQ RawCtxForwardAnnotation.erase client).IsTotalQueryBound budget)
    (state : State A N C) (result : RawCtxForwardScan.Cut Tag Value (State A N C))
    (supported : result ∈ support (RawCtxForwardScan.scan PqxdhInitialForwardPost.selected (selected depth) (selection depth)
      (handler source writer stage pre application initial selector aux) client covered state)) :
    ∃ added, (cutState result).2 = state.2 ++ added ∧ added.length ≤ 3 * budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [RawCtxForwardScan.scan_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩
  | query_bind query next ih =>
      cases chosen : selected depth query.2 state with
      | true =>
          rw [RawCtxForwardScan.scan_cut _ _ _ _ query next covered state chosen] at supported
          simp only [mem_support_pure_iff] at supported
          subst result
          exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩
      | false =>
          rw [RawCtxForwardScan.scan_other _ _ _ _ query next covered state chosen] at supported
          simp only [mem_support_bind_iff] at supported
          obtain ⟨reply, head, tail⟩ := supported
          simp only [simulateQ_bind, simulateQ_spec_query, RawCtxForwardAnnotation.erase, isTotalQueryBound_query_bind_iff] at bounded
          obtain ⟨first, firstEq, firstBound⟩ := step_audit source writer stage pre application initial selector aux query.2 state reply head
          obtain ⟨rest, restEq, restBound⟩ := ih reply.1 (covered.2 reply.1) (budget - 1) (bounded.2 reply.1) reply.2 result tail
          refine ⟨first ++ rest, ?_, ?_⟩
          · rw [restEq, firstEq, List.append_assoc]
          · simp only [List.length_append]
            omega

/-- The original first-builder and full adaptive post limit bound every pre-cut candidate, retaining the entire initial audit and every repeated attempted callback. -/
theorem carried_audit (depth stage qPost : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (result : Carried extra M P I D K Result Origin A N C S B)
    (supported : result ∈ support (carried source writer pre application initial selector aux mark sender route decode execution depth stage state)) :
    ∃ added, (cutState result).2 = state.2 ++ added ∧ added.length ≤ 3 * (7 + qPost * 67) := by
  apply scan_audit source writer pre application initial selector aux depth stage _ _ (7 + qPost * 67) _ state result supported
  simpa only [PqxdhInitialNativeCarried.code, PqxdhInitialOriginForwardBuilder.program_erase] using
    PqxdhInitialOriginPost.sequence_total source execution.initial mark execution.origin sender route decode
      execution.index execution.metadata execution.ready execution.outside qPost bounded (execution.before, execution.trace)

/-- Every supported audited source cut inherits its source-derived full outside continuation certificate from the same literal original descriptor. -/
theorem carried_fits (depth stage qPost : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state reached : State A N C) (context : Context extra M P I D K Result Origin S B)
    (supported : RawCtxForwardScan.Cut.pending context reached ∈ support
      (carried source writer pre application initial selector aux mark sender route decode execution depth stage state)) :
    PqxdhInitialOriginCertificates.Fits qPost context := by
  apply PqxdhInitialNativeCarried.carried_fits source writer mark sender route decode execution depth stage
    (external pre application initial selector aux) qPost bounded state.1 reached.1 context
  rw [← carried_projection source writer pre application initial selector aux mark sender route decode execution depth stage state,
    support_map]
  exact ⟨.pending context reached, supported, rfl⟩

/-- The original source uniform bill also bounds its audited prefix: both audit erasure and scan completion are literal oracle-program equations. -/
theorem carried_uniform (depth stage budget : Nat) (state : State A N C)
    (bounded : ((simulateQ (PqxdhInitialNativeLog.handler source writer stage (external pre application initial selector aux))
      (PqxdhInitialNativeCarried.original source mark sender route decode execution)).run state.1).IsTotalQueryBound budget) :
    (carried source writer pre application initial selector aux mark sender route decode execution depth stage state).IsTotalQueryBound budget := by
  apply RawCtxForwardScan.scan_uniform PqxdhInitialForwardPost.selected (selected depth) (selection depth)
    (handler source writer stage pre application initial selector aux) (PqxdhInitialOriginContext.frame mark sender route decode)
    _ _ (PqxdhInitialOriginForwardBuilder.program_sound source mark execution.origin sender route decode execution.initial
      execution.index execution.metadata execution.ready execution.outside execution.before execution.trace) state budget
  apply (isQueryBound_map_iff _ (Prod.map id Prod.fst) _ _ _).mp
  rw [program_erase source writer stage pre application initial selector aux]
  simpa only [PqxdhInitialNativeCarried.code, PqxdhInitialOriginForwardBuilder.program_erase,
    PqxdhInitialNativeCarried.original, IsTotalQueryBound] using bounded

end BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.step_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.step_same

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.step_preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.step_preserve

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_same

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAuditCarried.carried_uniform
