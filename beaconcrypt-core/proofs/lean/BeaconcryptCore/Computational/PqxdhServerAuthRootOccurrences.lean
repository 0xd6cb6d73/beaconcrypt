import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding

/-! Actual R1 root callback receipts, retained at their source occurrences. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhJointIdentity PqxdhJointGapDh PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhJointDhExtractFamily PqxdhJointDhExtractRoot
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The unchanged composed R1 primitive interpreter. Its full family state retains the actual Extract cache and primitive history. -/
noncomputable def family (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp) :=
  PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction

/-- One actual returned root comes from the cached PRK at this request's original 192-byte input and the real root Expand. -/
def RootAt (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (cache : HmacOracle.QueryCache) (message : Message) (root : RootOutput) : Prop :=
  ∃ bytes prk, input setup.joint setup.dh seed scalar message = some bytes ∧
    cache bytes = some prk ∧ root = expandRoot setup.hmac prk

/-- The actual successful root callback supplies its source input, exact table cell and returned root together, retaining all prior history/cache effects. -/
theorem root_at (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (before after : PqxdhJointDhExtractFamily.State) (root : RootOutput)
    (supported : (some root, after) ∈ support ((family setup seed scalar (.inr (.derive message))).run before)) :
    RootAt setup seed scalar after.cache message root := by
  rw [family, PqxdhExtractRomFamily.rom_root] at supported
  cases actual : input setup.joint setup.dh seed scalar message with
  | none => simp only [actual, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq,
      false_and] at supported
  | some bytes =>
      simp only [actual, support_map, Set.mem_image] at supported
      obtain ⟨read, reached, same⟩ := supported
      cases same
      exact ⟨bytes, read.1, actual, (PqxdhExtractRomFamily.oracle_step bytes before.cache read reached).2, rfl⟩

/-- A later retained cache preserves the exact source-root receipt, including equal-input aliases. -/
theorem root_mono (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : HmacOracle.QueryCache) (grows : before ≤ after) (message : Message) (root : RootOutput)
    (recorded : RootAt setup seed scalar before message root) : RootAt setup seed scalar after message root := by
  obtain ⟨bytes, prk, actual, cached, value⟩ := recorded
  exact ⟨bytes, prk, actual, grows cached, value⟩

/-- Only successful root queries carry a root receipt; all other original query classes retain their ordinary meanings. -/
def QueryAt (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (cache : HmacOracle.QueryCache) (query : RootSpec.Domain) (reply : RootSpec.Range query) : Prop :=
  match query with
  | .inr (.derive message) => ∀ root, reply = some root → RootAt setup seed scalar cache message root
  | _ => True

/-- The actual composed family supplies the receipt for every reached query and preserves its prior cache. -/
theorem query_at (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : RootSpec.Domain) (before : PqxdhJointDhExtractFamily.State)
    (result : RootSpec.Range query × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support ((family setup seed scalar query).run before)) :
    before.cache ≤ result.2.cache ∧ QueryAt setup seed scalar result.2.cache query result.1 := by
  refine ⟨PqxdhExtractRomFamily.rom_reduction_cache_mono setup.hmac setup.joint setup.dh seed scalar
    query before result supported, ?_⟩
  cases query with
  | inl coin => trivial
  | inr query =>
      cases query with
      | sign message => trivial
      | publicHmac key message => trivial
      | derive message =>
          intro root reply
          exact root_at setup seed scalar message before result.2 root (by rw [← reply]; exact supported)

/-- Every completed private query observation remains true after later original cache growth. -/
theorem query_mono (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : HmacOracle.QueryCache) (grows : before ≤ after)
    (query : RootSpec.Domain) (reply : RootSpec.Range query)
    (recorded : QueryAt setup seed scalar before query reply) : QueryAt setup seed scalar after query reply := by
  cases query with
  | inl coin => trivial
  | inr query =>
      cases query with
      | sign message => trivial
      | publicHmac key message => trivial
      | derive message => exact fun root same => root_mono setup seed scalar before after grows message root (recorded root same)

/-- The full adaptive original root client preserves the complete cache and derives every logged root equation at the final cache. Logging observes the actual reply once and never supplies its private log to the client. -/
theorem program_roots {Result : Type} (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp RootSpec Result) (before : PqxdhJointDhExtractFamily.State)
    (result : (Result × QueryLog RootSpec) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support ((simulateQ (family setup seed scalar)
      (PqxdhServerAuthApiJournal.record work)).run before)) :
    before.cache ≤ result.2.cache ∧
      ∀ entry ∈ result.1.2, QueryAt setup seed scalar result.2.cache entry.1 entry.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [PqxdhServerAuthApiJournal.record, simulateQ_pure, WriterT.run_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨le_rfl, by simp⟩
  | query_bind query next ih =>
      unfold PqxdhServerAuthApiJournal.record at supported
      rw [run_simulateQ_loggingOracle_query_bind] at supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_map, StateT.run_map,
        mem_support_bind_iff, support_map] at supported
      obtain ⟨middle, reached, final, continued, rfl⟩ := supported
      obtain ⟨suffixCache, suffixRoots⟩ := ih middle.1 middle.2 final continued
      obtain ⟨stepCache, stepRoot⟩ := query_at setup seed scalar query before middle reached
      refine ⟨stepCache.trans suffixCache, ?_⟩
      intro entry found
      rcases List.mem_cons.mp found with same | later
      · cases same
        exact query_mono setup seed scalar middle.2.cache final.2.cache suffixCache query middle.1 stepRoot
      · exact suffixRoots entry later

/-- Two actual root occurrences at the same original input have the same returned root because they use the same retained cache cell. No converse or output-injectivity claim is made. -/
theorem same_input (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (cache : HmacOracle.QueryCache) (left right : Message) (first second : RootOutput)
    (firstAt : RootAt setup seed scalar cache left first)
    (secondAt : RootAt setup seed scalar cache right second)
    (same : input setup.joint setup.dh seed scalar left = input setup.joint setup.dh seed scalar right) :
    first = second := by
  obtain ⟨bytes, prk, actual, cached, value⟩ := firstAt
  obtain ⟨otherBytes, otherPrk, otherActual, otherCached, otherValue⟩ := secondAt
  have bytesEq := Option.some.inj (actual.symm.trans (same.trans otherActual))
  subst otherBytes
  have prkEq := Option.some.inj (cached.symm.trans otherCached)
  exact value.trans ((congrArg (expandRoot setup.hmac) prkEq).trans otherValue.symm)

/-- The private callback annotation keeps the literal public query/reply, complete before/after protocol states and chronological internal root-interface observations. None of these added observations is passed to the public adversary. -/
structure Call (KemSK : Type) where
  query : ServerAuthSpec.Domain
  reply : ServerAuthSpec.Range query
  before : GameState KemSK
  after : GameState KemSK
  roots : QueryLog RootSpec

/-- Execute the unchanged complete source callback exactly once, with its root-interface journal retained privately. -/
noncomputable def callback (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (before : GameState KemSK) : OracleComp RootSpec (ServerAuthSpec.Range query × GameState KemSK × QueryLog RootSpec) :=
  (fun result => (result.1.1, result.1.2, result.2)) <$>
    PqxdhServerAuthApiJournal.record ((authHandler setup codec checks publicValue beaconSeed query).run before)

/-- Erasing only the private root-interface journal recovers the original complete source callback as an oracle program. -/
theorem callback_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (before : GameState KemSK) :
    (fun result => (result.1, result.2.1)) <$> callback setup codec checks publicValue beaconSeed query before =
      (authHandler setup codec checks publicValue beaconSeed query).run before := by
  simpa only [callback, Functor.map_map, Function.comp_def] using
    PqxdhServerAuthApiJournal.erase ((authHandler setup codec checks publicValue beaconSeed query).run before)

/-- Private chronological source occurrences; the original handler only reads the first component. -/
abbrev Audit (KemSK : Type) := GameState KemSK × List (Call KemSK)

/-- The literal original API handler with a private completion receipt. Every optional rejection is recorded after its original effects; the public return value is unchanged. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) :
    QueryImpl ServerAuthSpec (StateT (Audit KemSK) (OracleComp RootSpec)) := fun query before =>
  (fun result => (result.1, result.2.1, before.2 ++
    [⟨query, result.1, before.1, result.2.1, result.2.2⟩])) <$>
      callback setup codec checks publicValue beaconSeed query before.1

/-- The complete actual API reply and protocol state erase from the private callback annotation before any root interpretation. -/
theorem handler_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (before : Audit KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (handler setup codec checks publicValue beaconSeed query).run before =
      (authHandler setup codec checks publicValue beaconSeed query).run before.1 := by
  simpa only [handler, StateT.run, Functor.map_map, Function.comp_def] using
    callback_erase setup codec checks publicValue beaconSeed query before.1

/-- The original adaptive client receives its original replies, and erasing the final private audit recovers the complete source program. -/
theorem program_erase {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (work : OracleComp ServerAuthSpec Result) (before : Audit KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler setup codec checks publicValue beaconSeed) work).run before =
      (simulateQ (authHandler setup codec checks publicValue beaconSeed) work).run before.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp_rw [ih]
      have same := congrArg
        (fun step : OracleComp RootSpec (ServerAuthSpec.Range query × GameState KemSK) =>
          step >>= fun result =>
            (simulateQ (authHandler setup codec checks publicValue beaconSeed) (next result.1)).run result.2)
        (handler_erase setup codec checks publicValue beaconSeed query before)
      simpa only [bind_map_left] using same

/-- A chronological chain of actual completed callbacks, including their exact primitive-family states and internal journals. Each successor starts in the complete state returned by its predecessor. -/
inductive Path (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes) :
    (GameState KemSK × PqxdhJointDhExtractFamily.State) → List (Call KemSK) →
      (GameState KemSK × PqxdhJointDhExtractFamily.State) → Prop where
  | nil (state : GameState KemSK) (primitive : PqxdhJointDhExtractFamily.State) :
      Path setup codec checks publicValue beaconSeed seed scalar (state, primitive) [] (state, primitive)
  | cons (call : Call KemSK) (before middle : PqxdhJointDhExtractFamily.State)
      (suffix : List (Call KemSK)) (final : GameState KemSK × PqxdhJointDhExtractFamily.State)
      (reached : ((call.reply, call.after, call.roots), middle) ∈ support
        ((simulateQ (family setup seed scalar)
          (callback setup codec checks publicValue beaconSeed call.query call.before)).run before))
      (rest : Path setup codec checks publicValue beaconSeed seed scalar (call.after, middle) suffix final) :
      Path setup codec checks publicValue beaconSeed seed scalar (call.before, before) (call :: suffix) final

/-- Every original adaptive API execution supplies one actual state-linked callback path; an arbitrary prior private audit is retained verbatim. -/
theorem program_path {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (work : OracleComp ServerAuthSpec Result) (before : Audit KemSK) (primitive : PqxdhJointDhExtractFamily.State)
    (result : (Result × Audit KemSK) × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support ((simulateQ (family setup seed scalar)
      ((simulateQ (handler setup codec checks publicValue beaconSeed) work).run before)).run primitive)) :
    ∃ calls, result.1.2.2 = before.2 ++ calls ∧
      Path setup codec checks publicValue beaconSeed seed scalar (before.1, primitive) calls
        (result.1.2.1, result.2) := by
  induction work using OracleComp.inductionOn generalizing before primitive result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨[], (List.append_nil _).symm, .nil before.1 primitive⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      change middle ∈ support ((simulateQ (family setup seed scalar)
        ((fun step => (step.1, step.2.1, before.2 ++
          [⟨query, step.1, before.1, step.2.1, step.2.2⟩])) <$>
          callback setup codec checks publicValue beaconSeed query before.1)).run primitive) at reached
      simp only [simulateQ_map, StateT.run_map, support_map] at reached
      obtain ⟨step, stepRun, rfl⟩ := reached
      obtain ⟨calls, appended, rest⟩ := ih step.1.1 _ step.2 result continued
      refine ⟨⟨query, step.1.1, before.1, step.1.2.1, step.1.2.2⟩ :: calls, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using appended
      · exact .cons ⟨query, step.1.1, before.1, step.1.2.1, step.1.2.2⟩
          primitive step.2 calls (result.1.2.1, result.2) stepRun rest

/-- Every root observation of a completed actual API callback is justified by the callback's own interpreted execution and remains in its final cache. -/
theorem callback_roots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (call : Call KemSK) (before after : PqxdhJointDhExtractFamily.State)
    (supported : ((call.reply, call.after, call.roots), after) ∈ support
      ((simulateQ (family setup seed scalar)
        (callback setup codec checks publicValue beaconSeed call.query call.before)).run before)) :
    before.cache ≤ after.cache ∧
      ∀ entry ∈ call.roots, QueryAt setup seed scalar after.cache entry.1 entry.2 := by
  simp only [callback, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, same⟩ := supported
  have primitiveEq : result.2 = after := congrArg Prod.snd same
  have logEq : result.1.2 = call.roots := congrArg (fun value => value.1.2.2) same
  have roots := program_roots setup seed scalar
    ((authHandler setup codec checks publicValue beaconSeed call.query).run call.before) before result reached
  simpa only [primitiveEq, logEq] using roots

/-- Actual completed callback chains retain every root occurrence at the final cache; intermediate family states are linked by the same execution. -/
theorem path_roots (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after) :
    before.2.cache ≤ after.2.cache ∧
      ∀ call ∈ calls, ∀ entry ∈ call.roots, QueryAt setup seed scalar after.2.cache entry.1 entry.2 := by
  induction path with
  | nil state primitive => exact ⟨le_rfl, by simp⟩
  | cons call before middle suffix final reached rest ih =>
      obtain ⟨headCache, headRoots⟩ := callback_roots setup codec checks publicValue beaconSeed seed scalar
        call before middle reached
      obtain ⟨tailCache, tailRoots⟩ := ih
      refine ⟨headCache.trans tailCache, ?_⟩
      intro found member entry observed
      rcases List.mem_cons.mp member with same | later
      · subst found
        exact query_mono setup seed scalar middle.cache final.2.cache tailCache entry.1 entry.2
          (headRoots entry observed)
      · exact tailRoots found later entry observed

/-- The same private completed callback supplies the full original interpreted source occurrence, with both complete protocol and primitive states retained. -/
theorem callback_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (call : Call KemSK) (before after : PqxdhJointDhExtractFamily.State)
    (supported : ((call.reply, call.after, call.roots), after) ∈ support
      ((simulateQ (family setup seed scalar)
        (callback setup codec checks publicValue beaconSeed call.query call.before)).run before)) :
    (call.reply, call.after, after) ∈ support
      ((PqxdhServerAuthEntryFactor.interp (family setup seed scalar)
        (authHandler setup codec checks publicValue beaconSeed call.query)).run (call.before, before)) := by
  have erased : ((call.reply, call.after), after) ∈ support
      ((simulateQ (family setup seed scalar)
        ((fun result => (result.1, result.2.1)) <$>
          callback setup codec checks publicValue beaconSeed call.query call.before)).run before) := by
    simp only [simulateQ_map, StateT.run_map, support_map]
    exact ⟨((call.reply, call.after, call.roots), after), supported, rfl⟩
  rw [callback_erase] at erased
  rw [PqxdhServerAuthEntryFactor.interp_run, support_map]
  exact ⟨((call.reply, call.after), after), erased, rfl⟩

/-- Actual interpretation can only restrict original source support. This projection retains the entire protocol result/state and discards only the primitive-family wrapper. -/
theorem interpreted_source {Result : Type} (setup : Setup baseSpec KemSK) (seed : IdentitySeed)
    (scalar : ScalarBytes) (work : Game KemSK Result)
    (before : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (result : Result × GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : result ∈ support ((interp (family setup seed scalar) work).run before)) :
    (result.1, result.2.1) ∈ support (work.run before.1) := by
  rw [interp_run, support_map] at supported
  obtain ⟨actual, reached, same⟩ := supported
  have projected : actual.1 ∈ support
      ((simulateQ (family setup seed scalar) (work.run before.1)).run' before.2) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨actual, reached, rfl⟩
  have original := support_simulateQ_run'_subset (family setup seed scalar) (work.run before.1) before.2 projected
  have outputEq : actual.1 = (result.1, result.2.1) :=
    congrArg (fun value => (value.1, value.2.1)) same
  exact outputEq ▸ original

/-- A recorded callback occurs at a literal chronological position with its actual linked prefix and suffix; equal bytes or repeated callback values do not identify the position. -/
theorem path_occurrence (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after)
    (call : Call KemSK) (member : call ∈ calls) :
    ∃ earlier later primitive middle,
      calls = earlier ++ call :: later ∧
      Path setup codec checks publicValue beaconSeed seed scalar before earlier (call.before, primitive) ∧
      ((call.reply, call.after, call.roots), middle) ∈ support
        ((simulateQ (family setup seed scalar)
          (callback setup codec checks publicValue beaconSeed call.query call.before)).run primitive) ∧
      Path setup codec checks publicValue beaconSeed seed scalar (call.after, middle) later after := by
  induction path with
  | nil state primitive => simp only [List.not_mem_nil] at member
  | cons head primitive middle suffix final reached rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst call
        exact ⟨[], suffix, primitive, middle, rfl, .nil _ _, reached, rest⟩
      · obtain ⟨earlier, later, atCall, afterCall, split, preceding, actual, following⟩ := ih later
        exact ⟨head :: earlier, later, atCall, afterCall, by rw [split]; rfl,
          .cons head primitive middle earlier _ reached preceding, actual, following⟩

end BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.root_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.root_at

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.root_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.root_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.query_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.query_at

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.query_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.query_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.program_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.program_roots

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.same_input' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.same_input

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.callback_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.callback_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.handler_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.handler_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.program_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.program_path

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.callback_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.callback_roots

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.path_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.path_roots

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.callback_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.callback_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.interpreted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.interpreted_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.path_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootOccurrences.path_occurrence
