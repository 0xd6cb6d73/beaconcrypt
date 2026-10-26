import BeaconcryptCore.Computational.PqxdhServerAuthPublicationJournalClient
import BeaconcryptCore.Computational.PqxdhRegistrationPending
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationWriter

/-! Allocated pending-token disposal for the actual optional selected-component scheduler. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhRegistrationPending (Spent)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- The complete resource footprint preserves an allocated consumed handle. Future guessed handles remain outside this predicate. -/
theorem footprint_spent (query : ServerAuthSpec.Domain) (index : Nat)
    (before after : GameState KemSK) (spent : Spent index before)
    (step : ResourceStep query before after) : Spent index after := by
  have unchanged (sessions : after.sessions = before.sessions) (pending : after.pending = before.pending) :
      Spent index after := ⟨sessions ▸ spent.1, pending ▸ spent.2⟩
  rcases query with coin | query
  · exact unchanged step.1 step.2.2
  cases query with
  | accept raw =>
      rcases step with ⟨sessions, _, same | ⟨token, inserted⟩⟩
      · exact ⟨by rw [sessions]; exact Nat.lt_trans spent.1 (Nat.lt_succ_self _), same ▸ spent.2⟩
      · refine ⟨by rw [sessions]; exact Nat.lt_trans spent.1 (Nat.lt_succ_self _), ?_⟩
        rw [inserted, Function.update_of_ne (Nat.ne_of_lt spent.1)]
        exact spent.2
  | build other payload =>
      refine ⟨step.1 ▸ spent.1, ?_⟩
      rw [step.2.2]
      by_cases same : index = other
      · subst index
        exact Function.update_self ..
      · rw [Function.update_of_ne same]
        exact spent.2
  | finish raw => exact unchanged step.1 step.2.1
  | _ => exact unchanged step.1 step.2.2

/-- Every actual normal stopped callback preserves disposal, including native failure and ordinary known-key operations. -/
theorem stopped_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (index : Nat)
    (before : Local KemSK × Option Nat)
    (result : Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat))
    (spent : Spent index before.1.1.1)
    (supported : result ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run before))
    (reply : ServerAuthSpec.Range query) (normal : result.1 = some reply) : Spent index result.2.1.1.1 :=
  footprint_spent query index before.1.1.1 result.2.1.1.1 spent
    (PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j
      query before result supported reply normal).1

/-- Arbitrary continuing optional source suffixes cannot resurrect the allocated moved token; all actual component work remains in the program. -/
theorem program_spent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (index : Nat)
    (before : Local KemSK × Option Nat) (spent : Spent index before.1.1.1)
    (result : Option Result × (Local KemSK × Option Nat))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run before))
    (reply : Result) (normal : result.1 = some reply) : Spent index result.2.1.1.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact spent
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      cases middleReply : middle.1 with
      | none =>
          simp only [middleReply, Option.elim_none, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases normal
      | some value =>
          simp only [middleReply, Option.elim_some] at supported
          exact ih value middle.2
            (stopped_spent setup codec checks context rest Q j query index before middle spent reached value middleReply)
            supported

/-- A reached allocated build consumes its source token on every normal native outcome, independently of inner or outer writer success. -/
theorem build_consumes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (index : Nat) (payload : Option Pqxdh.Bytes)
    (before : Local KemSK × Option Nat)
    (result : Option (Option PqxdhServerRegistrationPublication.Response) × (Local KemSK × Option Nat))
    (allocated : index < before.1.1.1.sessions)
    (supported : result ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index payload))).run.run before))
    (reply : Option PqxdhServerRegistrationPublication.Response) (normal : result.1 = some reply) :
    Spent index result.2.1.1.1 := by
  have footprint := (PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j
    (.inr (.build index payload)) before result supported reply normal).1
  exact ⟨footprint.1 ▸ allocated, by rw [footprint.2.2]; exact Function.update_self ..⟩

/-- An absent token rejects before every ordinary or selected builder request; full local state and the stop monitor are unchanged. -/
theorem missing_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (index : Nat) (payload : Option Pqxdh.Bytes)
    (before : Local KemSK × Option Nat) (missing : before.1.1.1.pending index = none) :
    (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index payload))).run.run before = pure (some none, before) := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped,
    OptionT.run_mk, StateT.run, PqxdhServerAuthCtxHandler.handler,
    PqxdhServerAuthCtxHandler.route, PqxdhServerAuthCtxBuild.build, missing,
    map_pure, pure_bind, PqxdhServerAuthCtxHandler.settle, hiddenDesignated, designated]
  cases bad : before.1.1.2.2.bad <;>
    simp [keepHiddenBad, bad, PqxdhServerAuthCtxStop.observe, PqxdhServerAuthCtxStop.checkpoint]
  rw [← bad]

/-- After one reached allocated build and any continuing adaptive suffix, a second build at that same occurrence coordinate rejects without a component request. -/
theorem no_rebuild (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (index : Nat) (payload replayPayload : Option Pqxdh.Bytes)
    (before : Local KemSK × Option Nat)
    (first : Option (Option PqxdhServerRegistrationPublication.Response) × (Local KemSK × Option Nat))
    (allocated : index < before.1.1.1.sessions)
    (firstRun : first ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index payload))).run.run before))
    (firstReply : Option PqxdhServerRegistrationPublication.Response) (firstNormal : first.1 = some firstReply)
    (work : OracleComp ServerAuthSpec Result) (last : Option Result × (Local KemSK × Option Nat))
    (continued : last ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run first.2))
    (lastReply : Result) (lastNormal : last.1 = some lastReply) :
    (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index replayPayload))).run.run last.2 = pure (some none, last.2) :=
  missing_build setup codec checks context rest Q j index replayPayload last.2
    (program_spent setup codec checks context rest Q j work index first.2
      (build_consumes setup codec checks context rest Q j index payload before first allocated
        firstRun firstReply firstNormal) last continued lastReply lastNormal).2

/-- The complete optional compiled source preserves literal pending-handle allocation through arbitrary continuing adversary work. -/
theorem program_valid (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (before : Local KemSK × Option Nat) (valid : ResourceValid before.1.1.1)
    (result : Option Result × (Local KemSK × Option Nat))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run before))
    (reply : Result) (normal : result.1 = some reply) : ResourceValid result.2.1.1.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact valid
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, supported⟩ := supported
      cases middleReply : middle.1 with
      | none =>
          simp only [middleReply, Option.elim_none, StateT.run_pure, mem_support_pure_iff] at supported
          subst result
          cases normal
      | some value =>
          simp only [middleReply, Option.elim_some] at supported
          exact ih value middle.2
            (ResourceStep.valid query before.1.1.1 middle.2.1.1.1 valid
              (PqxdhServerAuthPublicationJournalClean.stopped_footprint setup codec checks context rest Q j
                query before middle reached value middleReply).1) supported

/-- Every actual present token after a normal prefix from the literal initial state has already been allocated. This rules out the guessed-future-handle exception without a caller premise. -/
theorem initial_allocated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (result : Option Result × (Local KemSK × Option Nat))
    (supported : result ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run
        (PqxdhServerAuthCtxReserve.initial setup context).1))
    (reply : Result) (normal : result.1 = some reply)
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (present : result.2.1.1.1.pending index = some token) : index < result.2.1.1.1.sessions := by
  exact program_valid setup codec checks context rest Q j work _
    (by intro index token found; cases found) result supported reply normal index token present

/-- A token actually reached after a literal initial prefix has one build opportunity across all later normal API interleavings. Writer failure does not restore that opportunity. -/
theorem initial_no_rebuild {PrefixResult : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (priorWork : OracleComp ServerAuthSpec PrefixResult)
    (before : Option PrefixResult × (Local KemSK × Option Nat))
    (prefixRun : before ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) priorWork).run.run
        (PqxdhServerAuthCtxReserve.initial setup context).1))
    (prefixReply : PrefixResult) (prefixNormal : before.1 = some prefixReply)
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (present : before.2.1.1.1.pending index = some token) (payload replayPayload : Option Pqxdh.Bytes)
    (first : Option (Option PqxdhServerRegistrationPublication.Response) × (Local KemSK × Option Nat))
    (firstRun : first ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index payload))).run.run before.2))
    (firstReply : Option PqxdhServerRegistrationPublication.Response) (firstNormal : first.1 = some firstReply)
    (suffix : OracleComp ServerAuthSpec Result) (last : Option Result × (Local KemSK × Option Nat))
    (suffixRun : last ∈ support ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) suffix).run.run first.2))
    (lastReply : Result) (lastNormal : last.1 = some lastReply) :
    (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index replayPayload))).run.run last.2 = pure (some none, last.2) :=
  no_rebuild setup codec checks context rest Q j index payload replayPayload before.2 first
    (initial_allocated setup codec checks context rest Q j priorWork before prefixRun prefixReply
      prefixNormal index token present) firstRun firstReply firstNormal suffix last suffixRun lastReply lastNormal

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.footprint_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.footprint_spent
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.stopped_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.stopped_spent
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.program_spent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.program_spent
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.build_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.build_consumes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.missing_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.missing_build
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.no_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.no_rebuild
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.program_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.program_valid
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.initial_allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.initial_allocated
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.initial_no_rebuild' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild.initial_no_rebuild
