import BeaconcryptCore.Computational.PqxdhInitialNativeLog
import BeaconcryptCore.Computational.PqxdhInitialParentObserverCompiler
import BeaconcryptCore.Computational.RawCtxFamilyFreshnessProxy

/-!
The actual native prefix retains a chronological candidate audit beside its complete selective table, cursor, private input log, shared state, identity state and initializer cache. Every executed private KDF input, public HKDF input and actual optional read value is recorded. The actual initializer executes once and additionally records its real input root and both returned chains. Erasing this separate audit preserves the original native interpreter, including root-cache effects. Initializer aliases are candidates, not disclosure events. No root-cache function is enumerated and no freshness or small-probability premise is introduced.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeAudit
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
abbrev Spec := @PqxdhInitialNativeLog.Spec ι
abbrev State (A N C : Type) := PqxdhInitialNativeLog.State A N C × List RootOutput
abbrev InitialReply := PqxdhInitialParentObserverCompiler.InitialReply
abbrev ReadInput (S B : Nat) := RawCtxGenericFamilyRead.ReadInput (RawCtxPendingOwnerQueries.Kernel RatchetChain) S B

noncomputable def readInputs (input : ReadInput S B) : List RootOutput :=
  (RawCtxLiveLineage.disclosed ⟨input.1, RawCtxGenericFamilyRead.nativeValue ConcreteRatchetKernel.mk input⟩).map
    RawCtxSelectedQueryTrace.rootVector

noncomputable def liveInputs : (RawCtxPendingSelectiveFamily.Spec S B).Domain → List RootOutput
  | .inl (.inl (.inl pending)) => [RawCtxSelectedQueryTrace.rootVector pending.request]
  | .inl (.inl (.inr _)) => []
  | .inl (.inr (.inl (.inl pending))) => [RawCtxSelectedQueryTrace.rootVector pending.request]
  | .inl (.inr (.inl (.inr _))) => []
  | .inl (.inr (.inr query)) => RawCtxSelectedPublicTrace.inputs query
  | .inr input => readInputs input

/-- Every original native read records at most one actual chain or skipped message-key value. -/
theorem read_length (input : ReadInput S B) : (readInputs input).length ≤ 1 := by
  simpa only [readInputs, List.length_map] using
    RawCtxLiveLineage.disclosed_length ⟨input.1, RawCtxGenericFamilyRead.nativeValue ConcreteRatchetKernel.mk input⟩

/-- Private requests and actual public/read interfaces contribute at most one32-byte candidate each. -/
theorem live_length (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) : (liveInputs query).length ≤ 1 := by
  rcases query with (pending | (pending | query)) | read
  · cases pending <;> simp [liveInputs]
  · cases pending <;> simp [liveInputs]
  · exact (RawCtxSelectedPublicTrace.inputs_bound query).trans (by split <;> decide)
  · exact read_length read

section Interpreter
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

def external : QueryImpl (PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared) (Ambient A N C)
  | .inl query => pre query
  | .inr (.inl reply) => application reply
  | .inr (.inr (.inl secrets)) => Prod.snd <$> initial secrets
  | .inr (.inr (.inr (.inl query))) => selector query
  | .inr (.inr (.inr (.inr query))) => aux query

noncomputable def handler : QueryImpl (Spec extra RatchetChain I D K X Response Shared S B) (StateT (State A N C) ProbComp)
  | .inl query => fun state => do
      let reply ← (PqxdhInitialNativeLog.handler source writer stage
        (external pre application initial selector aux) (.inl query)).run state.1
      pure (reply.1, (reply.2, state.2 ++ liveInputs query))
  | .inr (.inr (.inr (.inl secrets))) => fun state => do
      let reply ← (initial secrets (state.1.1.1.1, state.1.2.1)).run state.1.2.2
      pure (reply.1.1.2, ((((reply.1.2.1, state.1.1.1.2), state.1.1.2), (reply.1.2.2, reply.2)),
        state.2 ++ PqxdhInitialParentObserverCompiler.candidates reply.1.1))
  | .inr query => fun state => do
      let reply ← (PqxdhInitialNativeLog.handler source writer stage
        (external pre application initial selector aux) (.inr query)).run state.1
      pure (reply.1, (reply.2, state.2))

/-- Erasing only the candidate audit retains the original dependent reply and every native state field. -/
theorem query_erase (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C) :
    Prod.map id Prod.fst <$> (handler source writer stage pre application initial selector aux query).run state =
      (PqxdhInitialNativeLog.handler source writer stage (external pre application initial selector aux) query).run state.1 := by
  rcases query with query | (query | (reply | (secrets | (query | query))))
  all_goals simp only [handler, StateT.run, map_bind, map_pure, Prod.map_apply, id_eq, Prod.mk.eta, bind_pure]
  simp only [PqxdhInitialNativeLog.handler, PqxdhInitialNativeLog.bare,
    PqxdhInitialNativeLog.liftExternal, PqxdhInitialNativeLog.erase, PqxdhInitialNativeLog.inputs,
    external, StateT.run, bind_assoc, pure_bind]
  change (initial secrets (state.1.1.1.1, state.1.2.1) state.1.2.2 >>= fun a =>
      pure (a.1.1.2, (((a.1.2.1, state.1.1.1.2), state.1.1.2), (a.1.2.2, a.2)))) =
    (((fun a => ((a.1.1.2, a.1.2), a.2)) <$>
      initial secrets (state.1.1.1.1, state.1.2.1) state.1.2.2) >>= fun a =>
      pure (a.1.1, (((a.1.2.1, state.1.1.1.2), state.1.1.2), (a.1.2.2, a.2))))
  simp only [bind_map_left]

/-- The entire adaptive original program is unchanged when only its added candidate list is erased. -/
theorem program_erase (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) :
    Prod.map id Prod.fst <$> (simulateQ (handler source writer stage pre application initial selector aux) client).run state =
      (simulateQ (PqxdhInitialNativeLog.handler source writer stage (external pre application initial selector aux)) client).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (query_erase source writer stage pre application initial selector aux) client state

/-- Every supported callback retains its whole chronological prefix and appends at most three actual candidates, including failed initializer calls. -/
theorem step_audit (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain) (state : State A N C)
    (result : (Spec extra RatchetChain I D K X Response Shared S B).Range query × State A N C)
    (supported : result ∈ support ((handler source writer stage pre application initial selector aux query).run state)) :
    ∃ added, result.2.2 = state.2 ++ added ∧ added.length ≤ 3 := by
  rcases query with query | (query | (reply | (secrets | (query | query))))
  all_goals simp only [handler, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  all_goals obtain ⟨reply, _, rfl⟩ := supported
  · exact ⟨liveInputs query, rfl, (live_length query).trans (by decide)⟩
  · exact ⟨[], (List.append_nil _).symm, by decide⟩
  · exact ⟨[], (List.append_nil _).symm, by decide⟩
  · exact ⟨PqxdhInitialParentObserverCompiler.candidates reply.1.1, rfl,
      PqxdhInitialParentObserverCompiler.candidates_bound reply.1.1⟩
  · exact ⟨[], (List.append_nil _).symm, by decide⟩
  · exact ⟨[], (List.append_nil _).symm, by decide⟩

/-- The complete source execution appends at most three values per attempted callback and never deletes earlier audit entries. -/
theorem program_audit (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget) (state : State A N C) (result : Result × State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer stage pre application initial selector aux) client).run state)) :
    ∃ added, result.2.2 = state.2 ++ added ∧ added.length ≤ 3 * budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨[], (List.append_nil _).symm, Nat.zero_le _⟩
  | query_bind query next ih =>
      simp only [isTotalQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      obtain ⟨first, firstEq, firstBound⟩ := step_audit source writer stage pre application initial selector aux query state reply head
      obtain ⟨rest, restEq, restBound⟩ := ih reply.1 (budget - 1) (bounded.2 reply.1) reply.2 result tail
      refine ⟨first ++ rest, ?_, ?_⟩
      · rw [restEq, firstEq, List.append_assoc]
      · simp only [List.length_append]
        omega

/-- An actual family read keeps its native optional reply and every source interpreter field while recording exactly the bytes disclosed by that reply. -/
theorem read_step (input : ReadInput S B) (state : State A N C) :
    (handler source writer stage pre application initial selector aux (.inl (.inr input))).run state =
      pure (RawCtxGenericFamilyRead.nativeValue ConcreteRatchetKernel.mk input,
        (state.1, state.2 ++ readInputs input)) := rfl

/-- Pure audit bookkeeping preserves the literal uniform-query bill; the equality is of oracle programs, not evaluated distributions. -/
theorem query_uniform (query : (Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : State A N C) (budget : Nat) :
    ((handler source writer stage pre application initial selector aux query).run state).IsTotalQueryBound budget ↔
      ((PqxdhInitialNativeLog.handler source writer stage (external pre application initial selector aux) query).run state.1).IsTotalQueryBound budget := by
  rw [← query_erase source writer stage pre application initial selector aux query state]
  exact (isQueryBound_map_iff _ _ _ _ _).symm

end Interpreter

/-- Appending the original timestamped read adds precisely the same disclosed-value candidates as the private audit. -/
theorem read_known_note (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B) (input : ReadInput S B) :
    RawCtxFamilyFreshnessProxy.knownInputs prior
      (RawCtxProtocolReveals.note ⟨input.1, RawCtxGenericFamilyRead.nativeValue ConcreteRatchetKernel.mk input⟩ history) =
      RawCtxFamilyFreshnessProxy.knownInputs prior history ++ readInputs input := by
  simp only [RawCtxFamilyFreshnessProxy.knownInputs, RawCtxFamilyFreshnessProxy.known_note,
    List.map_append, readInputs]

end BeaconcryptCore.Computational.PqxdhInitialNativeAudit

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.read_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.read_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.live_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.live_length

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.query_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.step_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.step_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.program_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.program_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.read_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.query_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.query_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAudit.read_known_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAudit.read_known_note
