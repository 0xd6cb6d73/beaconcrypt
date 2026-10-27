import BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin

/-! Actual retained-table and acceptance chronology for the dynamic CTX source consumer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Presence of an actual retained-table entry persists; no claim about independent table outputs is used. -/
def Retained (before after : HmacOracle.QueryCache) : Prop :=
  ∀ bytes, before bytes ≠ none → after bytes ≠ none

/-- A concrete lazy table read retains every existing input and leaves its queried input present. -/
theorem oracle_retained (bytes : Pqxdh.Bytes) (before : HmacOracle.QueryCache)
    (result : HmacBlock × HmacOracle.QueryCache)
    (supported : result ∈ support ((HmacOracle.randomOracle bytes).run before)) :
    Retained before result.2 ∧ result.2 bytes ≠ none := by
  rw [randomOracle.run_eq] at supported
  cases hit : before bytes with
  | some value =>
    simp only [hit, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨fun _ present => present, by change before bytes ≠ none; rw [hit]; exact Option.some_ne_none value⟩
  | none =>
    simp only [hit, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨value, _, rfl⟩ := supported
    refine ⟨?_, by change before.cacheQuery bytes value bytes ≠ none; rw [QueryCache.cacheQuery_self]; exact Option.some_ne_none value⟩
    intro input present
    have distinct : input ≠ bytes := by rintro rfl; exact present hit
    simpa only [QueryCache.cacheQuery_of_ne _ _ distinct] using present

/-- The real ordinary derivation retains its complete prior table on every source rejection or root reply. -/
theorem real_retained (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (before : HmacOracle.QueryCache)
    (result : Reply × HmacOracle.QueryCache)
    (supported : result ∈ support ((realDerive setup.hmac setup.joint setup.dh
      context.seed context.scalar message).run before)) : Retained before result.2 := by
  simp only [realDerive, StateT.run] at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact fun _ present => present
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨read, reached, rfl⟩ := supported
    exact (oracle_retained _ before read reached).1

/-- Returning an ordinary root leaves the literal source input present in the real retained table. -/
theorem real_root (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (before after : HmacOracle.QueryCache) (root : RootOutput)
    (supported : (Reply.root root, after) ∈ support ((realDerive setup.hmac setup.joint setup.dh
      context.seed context.scalar message).run before)) :
    ∃ bytes, rootInput setup context.seed context.scalar message = some bytes ∧ after bytes ≠ none := by
  simp only [realDerive, StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar message with
  | none => simp only [input, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | some bytes =>
    simp only [input, support_map, Set.mem_image] at supported
    obtain ⟨read, reached, equal⟩ := supported
    refine ⟨bytes, input, ?_⟩
    have cache := congrArg Prod.snd equal
    dsimp only at cache
    rw [← cache]
    exact (oracle_retained bytes before read reached).2

/-- Both actual derivation routes preserve retained entries and omission of the selected input, including every rejection and cache-hit refusal. -/
theorem table_history (setup : Setup baseSpec KemSK) (context : Context KemSK) (select : Bool)
    (message : PqxdhJointDhExtractFamily.Message) (before : HiddenTable) (clean : before.Clean)
    (result : Reply × HiddenTable)
    (supported : result ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive message).run before)) :
    Retained before.cache result.2.cache ∧ result.2.Clean := by
  cases select with
  | false =>
    refine ⟨?_, (hiddenDerive_keeps setup context.seed context.scalar message before clean result supported).2.2⟩
    simp only [PqxdhServerAuthCtxState.tableServices, Bool.false_eq_true, ite_false, hiddenDerive, StateT.run] at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact fun _ present => present
    · split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact fun _ present => present
      · simp only [ordinaryHiddenDerive, StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨read, reached, rfl⟩ := supported
        exact real_retained setup context message before.cache read reached
  | true =>
    simp only [PqxdhServerAuthCtxState.tableServices, ite_true, selectHidden, StateT.run] at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ present => present, clean⟩
    · rename_i bytes input
      cases cached : before.cache bytes with
      | some value =>
        simp only [cached, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨fun _ present => present, clean⟩
      | none =>
        simp only [cached, support_pure, Set.mem_singleton_iff] at supported
        subst result
        refine ⟨fun _ present => present, ?_⟩
        intro other hidden
        have same : bytes = other := Option.some.inj hidden
        exact same ▸ cached

/-- A reached ordinary-root reply of the concrete selected table puts the actual request input in the retained cache; neither rejection nor the hidden label is confused with this branch. -/
theorem table_root (setup : Setup baseSpec KemSK) (context : Context KemSK) (select : Bool)
    (message : PqxdhJointDhExtractFamily.Message) (before after : HiddenTable) (root : RootOutput)
    (supported : (Reply.root root, after) ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive message).run before)) :
    ∃ bytes, rootInput setup context.seed context.scalar message = some bytes ∧ after.cache bytes ≠ none := by
  cases select with
  | false =>
    simp only [PqxdhServerAuthCtxState.tableServices, Bool.false_eq_true, ite_false, hiddenDerive, StateT.run] at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
    · split at supported
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
      · simp only [ordinaryHiddenDerive, StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨read, reached, equal⟩ := supported
        have reply := congrArg Prod.fst equal
        have table := congrArg Prod.snd equal
        dsimp only at reply table
        have actual : (Reply.root root, read.2) ∈ support ((realDerive setup.hmac setup.joint setup.dh
            context.seed context.scalar message).run before.cache) := by
          rw [← reply]
          exact reached
        obtain ⟨bytes, input, cached⟩ := real_root setup context message before.cache read.2 root actual
        exact ⟨bytes, input, by rw [← table]; exact cached⟩
  | true =>
    simp only [PqxdhServerAuthCtxState.tableServices, ite_true, selectHidden, StateT.run] at supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
    · split at supported <;>
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

/-- Public on-domain requests preserve all retained entries and selected-input omission, including the actual refusal query itself. -/
theorem public_history (bytes : Pqxdh.Bytes) (before : HiddenTable) (clean : before.Clean)
    (result : HmacBlock × HiddenTable)
    (supported : result ∈ support ((hiddenPublic bytes).run before)) :
    Retained before.cache result.2.cache ∧ result.2.Clean := by
  by_cases selected : before.hidden = some bytes
  · simp only [hiddenPublic, StateT.run, selected, ite_true, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨fun _ present => present, by simpa only [HiddenTable.Clean, selected] using clean⟩
  · simp only [hiddenPublic, StateT.run, selected, ite_false, support_map, Set.mem_image] at supported
    obtain ⟨read, reached, rfl⟩ := supported
    refine ⟨(oracle_retained bytes before.cache read reached).1, ?_⟩
    exact HiddenTable.Clean.update before _ clean rfl [bytes]
      (oracle_adds bytes before.cache read reached)
      (fun other member => (List.mem_singleton.mp member) ▸ selected)

/-- The exact factor services used by the adaptive source, with the actual optional designation of this operation. -/
noncomputable def services (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool) : Services Response HiddenTable :=
  if select then selectingServices setup context (factorServices setup codec checks context value)
  else factorServices setup codec checks context value

/-- The exact selected or ordinary factor service has the same retained-table callback proved above. -/
theorem services_derive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool) :
    (services setup codec checks context value select).derive =
      (PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive := by
  cases select <;> rfl

/-- Complete source admission preserves all prior table entries and the selected-input omission invariant. Every rejected prefix and attempted derivation is retained. -/
theorem accept_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool)
    (raw : Pqxdh.Bytes) (before : FlatState KemSK HiddenTable) (clean : before.2.2.Clean)
    (result : Option Nat × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((acceptStep setup codec checks (context.publicValue setup)
      (services setup codec checks context value select) raw).run before)) :
    Retained before.2.2.cache result.2.2.2.cache ∧ result.2.2.2.Clean := by
  simp only [acceptStep, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨collected, _, supported⟩ := supported
  cases found : collected.1 with
  | none =>
    simp only [found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨fun _ present => present, clean⟩
  | some input =>
    simp only [found] at supported
    split_ifs at supported with nonzero
    · obtain ⟨derived, reached, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      rw [services_derive] at reached
      exact table_history setup context select _ before.2.2 clean derived reached
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ present => present, clean⟩

/-- The full actual Beacon finish preserves retained Extract entries and omission across prefix rejection, ordinary and selected callbacks, final binding checks and native failure. -/
theorem finish_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool)
    (raw : Pqxdh.Bytes) (before : FlatState KemSK HiddenTable) (clean : before.2.2.Clean)
    (result : Option Pqxdh.Bytes × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((finishStep setup codec (context.publicValue setup) context.beaconSeed
      (services setup codec checks context value select) raw).run before)) :
    Retained before.2.2.cache result.2.2.2.cache ∧ result.2.2.2.Clean := by
  simp only [finishStep, StateT.run] at supported
  cases phase : before.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [phase, mem_support_bind_iff] at supported
    obtain ⟨prepared, _, supported⟩ := supported
    cases found : prepared with
    | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ present => present, clean⟩
    | some pending =>
      simp only [found, mem_support_bind_iff] at supported
      obtain ⟨derived, reached, supported⟩ := supported
      rw [services_derive] at reached
      have kept := table_history setup context select _ before.2.2 clean derived reached
      cases reply : derived.1 with
      | rejected =>
        simp only [reply, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact kept
      | root root =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, _, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact kept
      | hidden =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, _, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact kept
  | _ =>
    simp only [phase, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨fun _ present => present, clean⟩

/-- Complete response construction retains the identical Extract table; all native and selected tail effects stay in their separate full source/cache state. -/
theorem build_table (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool)
    (index : Nat) (payload : Option Pqxdh.Bytes) (before : FlatState KemSK HiddenTable)
    (result : Option PqxdhServerRegistrationPublication.Response × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((buildStep setup codec checks
      (services setup codec checks context value select) index payload).run before)) : result.2.2.2 = before.2.2 := by
  simp only [buildStep, StateT.run] at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  · obtain ⟨built, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- Complete public HMAC keeps real off-domain evaluation and on-domain retained-table/refusal effects while preserving prior entries and selected-input omission. -/
theorem hmac_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool)
    (key : HmacBlock) (message : Pqxdh.Bytes) (before : FlatState KemSK HiddenTable) (clean : before.2.2.Clean)
    (result : HmacBlock × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((hmacStep setup
      (services setup codec checks context value select) key message).run before)) :
    Retained before.2.2.cache result.2.2.2.cache ∧ result.2.2.2.Clean := by
  simp only [hmacStep, StateT.run] at supported
  split_ifs at supported with domain
  · obtain ⟨read, reached, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    have publicEq : (services setup codec checks context value select).table = hiddenPublic := by
      cases select <;> rfl
    rw [publicEq] at reached
    exact public_history message before.2.2 clean read reached
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ⟨fun _ present => present, clean⟩

/-- Every concrete source capability preserves retained-table presence and omission, including all raw deliveries, builds, disclosures, public requests and actual coin draws. -/
theorem skeleton_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (select : Bool)
    (query : ServerAuthSpec.Domain) (before : FlatState KemSK HiddenTable) (clean : before.2.2.Clean)
    (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (services setup codec checks context value select) query).run before)) :
    Retained before.2.2.cache result.2.2.2.cache ∧ result.2.2.2.Clean := by
  cases query with
  | inl coin =>
    simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨sample, _, rfl⟩ := supported
    exact ⟨fun _ present => present, clean⟩
  | inr query =>
    cases query with
    | accept raw => exact accept_history setup codec checks context value select raw before clean result supported
    | build index payload =>
      rw [build_table setup codec checks context value select index payload before result supported]
      exact ⟨fun _ present => present, clean⟩
    | finish raw => exact finish_history setup codec checks context value select raw before clean result supported
    | hmac key message => exact hmac_history setup codec checks context value select key message before clean result supported
    | hash bytes =>
      simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨read, _, supported⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ present => present, clean⟩
    | reveal keyId =>
      simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨fun _ present => present, clean⟩

/-- The actual one-shot designation and sticky refusal wrapper preserve retained-table history on every source query and reply. -/
theorem handler_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (before : HiddenState KemSK) (clean : before.1.2.2.Clean)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j
      (factorServices setup codec checks context value) query).run before)) :
    Retained before.1.2.2.cache result.2.1.2.2.cache ∧ result.2.1.2.2.Clean := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨step, reached, rfl⟩ := supported
  have kept : Retained before.1.2.2.cache step.2.1.2.2.cache ∧ step.2.1.2.2.Clean := by
    simp only [once, StateT.run] at reached
    split at reached
    · simp only [latch, StateT.run, support_map, Set.mem_image] at reached
      obtain ⟨middle, executed, rfl⟩ := reached
      exact skeleton_history setup codec checks context value false query before.1 clean middle executed
    · split at reached
      · simp only [latch, StateT.run, support_map, Set.mem_image] at reached
        obtain ⟨middle, executed, rfl⟩ := reached
        exact skeleton_history setup codec checks context value true query before.1 clean middle executed
      · simp only [latch, StateT.run, support_map, Set.mem_image] at reached
        obtain ⟨middle, executed, rfl⟩ := reached
        exact skeleton_history setup codec checks context value false query before.1 clean middle executed
  simp only [keepHiddenBad]
  split <;> exact kept

/-- Every adaptive continuation of the actual omitted-entry source retains prior table entries and selected-input omission. The full source state and every original callback remain in the evaluated program. -/
theorem program_history {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1))
    (program : OracleComp ServerAuthSpec α) (before : HiddenState KemSK) (clean : before.1.2.2.Clean)
    (result : α × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j
      (factorServices setup codec checks context value)) program).run before)) :
    Retained before.1.2.2.cache result.2.1.2.2.cache ∧ result.2.1.2.2.Clean := by
  exact run_rel _ (fun before after => before.1.2.2.Clean →
      Retained before.1.2.2.cache after.1.2.2.cache ∧ after.1.2.2.Clean)
    (fun _ clean => ⟨fun _ present => present, clean⟩)
    (fun _ _ _ first second clean => by
      obtain ⟨old, middleClean⟩ := first clean
      obtain ⟨later, afterClean⟩ := second middleClean
      exact ⟨fun bytes present => later bytes (old bytes present), afterClean⟩)
    (fun query before after reached clean => handler_history setup codec checks context value Q j
      query before clean after reached) program before result supported clean

/-- The original factor-side run starts with literal empty instrumentation and preserves selected-input omission for arbitrary contexts and complete uniform-factor values. -/
theorem run_clean (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1)) (result : HiddenState KemSK)
    (supported : result ∈ support (hiddenRun setup codec checks adversary revealSeed context Q j
      (factorServices setup codec checks context value))) : result.1.2.2.Clean := by
  simp only [hiddenRun, support_map, Set.mem_image] at supported
  obtain ⟨final, reached, rfl⟩ := supported
  exact (program_history setup codec checks context value Q j _ _
    (fun _ _ => rfl) final reached).2

/-- After an actual ordinary-root reply, its literal input cannot become the omitted selected input during any later adaptive source continuation. The proof consumes retained table presence and the actual omission invariant, not a probability or independence assumption. -/
theorem root_suffix {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1))
    (select : Bool) (message : PqxdhJointDhExtractFamily.Message)
    (before after : HiddenTable) (clean : before.Clean) (root : RootOutput)
    (derived : (Reply.root root, after) ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive message).run before))
    (game : GameState KemSK) (marks : Marks) (flag : Bool)
    (program : OracleComp ServerAuthSpec α) (result : α × HiddenState KemSK)
    (continued : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j
      (factorServices setup codec checks context value)) program).run ((game, marks, after), flag))) :
    ∃ bytes, rootInput setup context.seed context.scalar message = some bytes ∧
      result.2.1.2.2.hidden ≠ some bytes := by
  obtain ⟨bytes, input, present⟩ := table_root setup context select message before after root derived
  have afterClean := (table_history setup context select message before clean (.root root, after) derived).2
  obtain ⟨retained, finalClean⟩ := program_history setup codec checks context value Q j program
    ((game, marks, after), flag) afterClean result continued
  exact ⟨bytes, input, fun selected => retained bytes present (finalClean bytes selected)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.oracle_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.oracle_retained
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.real_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.real_retained
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.real_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.real_root
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.table_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.table_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.table_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.table_root
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.public_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.public_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.services_derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.services_derive
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.accept_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.accept_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.finish_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.finish_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.build_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.build_table
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.hmac_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.hmac_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.skeleton_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.skeleton_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.handler_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.handler_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.program_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.program_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.run_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.run_clean
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.root_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxChronology.root_suffix
