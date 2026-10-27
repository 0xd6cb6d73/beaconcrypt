import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Receipt

/-! Original acceptance journal and verified-field provenance for live pending tokens. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerRootPreparation PqxdhServerStaticDhSource PqxdhServerAuthPhase1Receipt
variable {ι KemSK Reader Response τ : Type} {baseSpec : OracleSpec ι}

/-- A token retains its original raw acceptance fields through an actual supported prefix input. -/
def TokenReceipt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (token : PqxdhServerRelatedRootConsumer.Returned) : Prop :=
  ∃ consumed after, ∃ input : Inputs Reader ScalarBytes PeerEncoding,
    (some input, after) ∈ support ((serverPrefix setup codec checks raw).run consumed) ∧
    token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
    Decoded codec raw input.verified ∧
    PqxdhJointPhase1Reports.sourceAccept (fun identity => setup.source.crypto.verify identity.toList)
      input.verified.candidate = some (input.verified.identity, input.verified.keys)

/-- Each currently present token has an actual successful accept at its literal index in the chronological public journal. -/
def Origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (journal : QueryLog ServerAuthSpec) (game : GameState KemSK) : Prop :=
  ∀ index token, game.pending index = some token → ∃ raw,
    (⟨.inr (.accept raw), some index⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal ∧
    TokenReceipt setup codec checks publicValue raw token

/-- Journal extension and removal of pending tokens retain every previous receipt. -/
theorem preserve (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (journal extra : QueryLog ServerAuthSpec) (before after : GameState KemSK)
    (origins : Origins setup codec checks publicValue journal before)
    (retained : ∀ index token, after.pending index = some token → before.pending index = some token) :
    Origins setup codec checks publicValue (journal ++ extra) after := by
  intro index token found
  exact (origins index token (retained index token found)).imp fun raw receipt =>
    ⟨List.mem_append_left extra receipt.1, receipt.2⟩

/-- The actual accept appends precisely its public reply while attaching the receipt only to the token created at that same source index. -/
theorem accept_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (services : Services Response τ) (journal : QueryLog ServerAuthSpec)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK τ) (result : Option Nat × FlatState KemSK τ)
    (supported : result ∈ support ((acceptStep setup codec checks publicValue services raw).run state))
    (origins : Origins setup codec checks publicValue journal state.1) :
    Origins setup codec checks publicValue (journal ++ [⟨.inr (.accept raw), result.1⟩]) result.2.1 := by
  intro index token found
  rcases pending_source setup codec checks publicValue services raw state result supported index token found with
    old | ⟨allocated, returned, input, consumed, reply, table, root, collected, derived, rooted, created, decoded, accepted⟩
  · exact (origins index token old).imp fun original receipt =>
      ⟨List.mem_append_left _ receipt.1, receipt.2⟩
  · refine ⟨raw, ?_, state.1.server.consumed, consumed, input, collected,
      congrArg PqxdhServerRelatedRootConsumer.Returned.pending created, decoded, accepted⟩
    simp only [returned, List.mem_append, List.mem_singleton, or_true]

/-- All complete source callbacks preserve token provenance while appending their actual public reply. -/
theorem skeleton_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (journal : QueryLog ServerAuthSpec) (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state))
    (origins : Origins setup codec checks publicValue journal state.1) :
    Origins setup codec checks publicValue (journal ++ [⟨query, result.1⟩]) result.2.1 := by
  have footprint := skeleton_resources setup codec checks publicValue beaconSeed services query state result supported
  rcases query with coin | (raw | ⟨index, payload⟩ | raw | ⟨key, bytes⟩ | bytes | key)
  case inr.accept => exact accept_origins setup codec checks publicValue services journal raw state result supported origins
  all_goals apply preserve setup codec checks publicValue journal _ state.1 result.2.1 origins
  all_goals intro other token found
  all_goals first
    | exact (congrFun footprint.2.2 other).symm.trans found
    | exact (congrFun footprint.2.1 other).symm.trans found
    | skip
  by_cases same : other = index
  · simp only [footprint.2.2, same, Function.update_self, reduceCtorEq] at found
  · simpa only [footprint.2.2, Function.update_of_ne same] using found

/-- Designation and sticky-refusal bookkeeping preserve the original API replies and native pending-origin journal. -/
theorem handler_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (journal : QueryLog ServerAuthSpec) (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state))
    (origins : Origins setup codec checks (context.publicValue setup) journal state.1.1) :
    Origins setup codec checks (context.publicValue setup) (journal ++ [⟨query, result.1⟩]) result.2.1.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  have answer : (keepHiddenBad state middle).1 = middle.1 := by
    unfold keepHiddenBad
    split <;> rfl
  rw [answer, keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    exact skeleton_origins setup codec checks (context.publicValue setup) context.beaconSeed _ journal query
      state.1 step supported origins

/-- The complete adaptive source journal retains each live token's earlier successful acceptance and original verified fields. -/
theorem program_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    {Result : Type} (work : OracleComp ServerAuthSpec Result) (journal : QueryLog ServerAuthSpec)
    (state : HiddenState KemSK) (result : (Result × QueryLog ServerAuthSpec) × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services)
      (PqxdhServerAuthApiJournal.record work)).run state))
    (origins : Origins setup codec checks (context.publicValue setup) journal state.1.1) :
    Origins setup codec checks (context.publicValue setup) (journal ++ result.1.2) result.2.1.1 := by
  induction work using OracleComp.inductionOn generalizing journal state result with
  | pure value =>
      change result ∈ support (pure ((value, []), state)) at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      simpa only [List.append_nil] using origins
  | query_bind query next ih =>
      rw [PqxdhServerAuthApiJournal.record, run_simulateQ_loggingOracle_query_bind] at supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff,
        simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
      obtain ⟨middle, reached, tail, continued, rfl⟩ := supported
      convert ih middle.1 (journal ++ [⟨query, middle.1⟩]) middle.2 tail continued
        (handler_origins setup codec checks context Q j services journal query state middle reached origins) using 1
      exact (List.append_assoc journal [⟨query, middle.1⟩] tail.1.2).symm

/-- The literal source initial state has no pending token; the complete journal theorem therefore needs no initial provenance assumption. -/
theorem initial_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    {Result : Type} (work : OracleComp ServerAuthSpec Result)
    (result : (Result × QueryLog ServerAuthSpec) × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services)
      (PqxdhServerAuthApiJournal.record work)).run
        ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false))) :
    Origins setup codec checks (context.publicValue setup) result.1.2 result.2.1.1 := by
  have empty : Origins setup codec checks (context.publicValue setup) [] (contextState setup context) := by
    intro index token found
    cases found
  simpa only [List.nil_append] using
    program_origins setup codec checks context Q j services work [] _ result supported empty

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.preserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.preserve

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.accept_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.accept_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.skeleton_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.skeleton_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.handler_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.handler_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.program_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.program_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.initial_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Origins.initial_origins
