import BeaconcryptCore.Computational.PqxdhServerAuthEntryEager

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes)

/-- The factored table omits the selected entry's value. Its input and a sticky refusal flag are private analysis state. -/
structure HiddenTable where
  cache : HmacOracle.QueryCache
  hidden : Option Pqxdh.Bytes
  bad : Bool

/-- The selected input is absent from the retained table; unrelated entries may carry equal block values. -/
def HiddenTable.Clean (table : HiddenTable) : Prop :=
  ∀ bytes, table.hidden = some bytes → table.cache bytes = none

/-- Mathematical source reconstruction inserts the selected block. The executable factored table never calls this function. -/
noncomputable def HiddenTable.fill (prk : HmacBlock) (table : HiddenTable) : HmacOracle.QueryCache :=
  match table.hidden with
  | none => table.cache
  | some bytes => table.cache.cacheQuery bytes prk

/-- Reconstruct the native reply for the omitted entry only inside the source comparison. -/
def Reply.materialize (hmac : HmacSha512) (prk : HmacBlock) : Reply → Reply
  | .hidden => .root (expandRoot hmac prk)
  | reply => reply

/-- Forward an ordinary root request on the remaining table and retain both private annotations. -/
noncomputable def ordinaryHiddenDerive (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message) :
    StateT HiddenTable ProbComp Reply := fun table =>
  (fun result => (result.1, { table with cache := result.2 })) <$>
    (realDerive hmac joint dh seed scalar message).run table.cache

/-- Honest access to the selected input returns its label. All other honest derivations use the real source HMAC and remaining random-oracle table. -/
noncomputable def hiddenDerive (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message) :
    StateT HiddenTable ProbComp Reply := fun table =>
  match PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => pure (.rejected, table)
  | some bytes => if table.hidden = some bytes then pure (.hidden, table)
      else (ordinaryHiddenDerive hmac joint dh seed scalar message).run table

/-- Select a fresh actual input at the designated source operation. A prior table hit raises the refusal flag; that branch is later excluded by the original owner event. -/
noncomputable def selectHidden (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message) :
    StateT HiddenTable ProbComp Reply := fun table =>
  match PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => pure (.rejected, table)
  | some bytes => match table.cache bytes with
    | some _ => pure (.rejected, { table with bad := true })
    | none => pure (.hidden, { table with hidden := some bytes })

/-- The adversary's query at the omitted input raises the sticky refusal flag and receives a fixed placeholder. Every other public table request remains real. -/
noncomputable def hiddenPublic (bytes : Pqxdh.Bytes) : StateT HiddenTable ProbComp HmacBlock := fun table =>
  if table.hidden = some bytes then pure (zeroSalt, { table with bad := true })
  else (fun result => (result.1, { table with cache := result.2 })) <$>
    (HmacOracle.randomOracle bytes).run table.cache

/-- Source reconstruction changes no other input's table lookup. -/
theorem fill_away (prk : HmacBlock) (table : HiddenTable) (bytes : Pqxdh.Bytes)
    (away : table.hidden ≠ some bytes) : table.fill prk bytes = table.cache bytes := by
  cases hidden : table.hidden with
  | none => simp [HiddenTable.fill, hidden]
  | some selected =>
      have ne : bytes ≠ selected := by intro same; subst same; exact away hidden
      simp [HiddenTable.fill, hidden, QueryCache.cacheQuery_of_ne _ _ ne]

/-- Updating an ordinary input commutes with mathematical reconstruction of the omitted entry. -/
theorem fill_update (prk : HmacBlock) (table : HiddenTable) (bytes : Pqxdh.Bytes)
    (away : table.hidden ≠ some bytes) (value : HmacBlock) :
    ({ table with cache := table.cache.cacheQuery bytes value } : HiddenTable).fill prk =
      (table.fill prk).cacheQuery bytes value := by
  cases hidden : table.hidden with
  | none => simp [HiddenTable.fill, hidden]
  | some selected =>
      have ne : bytes ≠ selected := by intro same; subst same; exact away hidden
      funext input
      by_cases here : input = bytes
      · subst here; simp [HiddenTable.fill, hidden, QueryCache.cacheQuery, ne]
      · by_cases chosen : input = selected
        · subst chosen; simp [HiddenTable.fill, hidden, QueryCache.cacheQuery, here]
        · simp [HiddenTable.fill, hidden, QueryCache.cacheQuery, here, chosen]


/-- A read at any other input is exactly the original random-oracle read after source reconstruction, including its full updated cache. -/
theorem table_away_source (prk : HmacBlock) (table : HiddenTable) (bytes : Pqxdh.Bytes)
    (away : table.hidden ≠ some bytes) :
    (fun result => (result.1, ({ table with cache := result.2 } : HiddenTable).fill prk)) <$>
      (HmacOracle.randomOracle bytes).run table.cache =
        (HmacOracle.randomOracle bytes).run (table.fill prk) := by
  rw [randomOracle.run_eq, randomOracle.run_eq, fill_away prk table bytes away]
  cases hit : table.cache bytes with
  | some value => simp only [map_pure]
  | none =>
      simp only [map_bind, map_pure, fill_update prk table bytes away]


/-- Honest derivations through the label interpreter exactly reconstruct the source reply and entire cache. The label is interpreted only by this comparison. -/
theorem hiddenDerive_source (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (prk : HmacBlock)
    (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable) :
    (fun result => (Reply.materialize hmac prk result.1, result.2.fill prk)) <$>
      (hiddenDerive hmac joint dh seed scalar message).run table =
        (realDerive hmac joint dh seed scalar message).run (table.fill prk) := by
  unfold hiddenDerive realDerive
  dsimp only [StateT.run]
  cases input : PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => simp only [map_pure, Reply.materialize]
  | some bytes =>
      by_cases selected : table.hidden = some bytes
      · simp only [selected, ite_true, map_pure, Reply.materialize, HiddenTable.fill]
        have hit : HmacOracle.randomOracle bytes (table.cache.cacheQuery bytes prk) =
            pure (prk, table.cache.cacheQuery bytes prk) := by
          simpa only [QueryCache.cacheQuery_self, StateT.run] using
            (randomOracle.run_eq bytes (table.cache.cacheQuery bytes prk))
        rw [hit, map_pure]
      · simp only [selected, ite_false, ordinaryHiddenDerive, StateT.run, realDerive, input,
          Functor.map_map, Reply.materialize]
        simpa only [Functor.map_map, Function.comp_def, StateT.run] using
          congrArg (fun work => (fun result => (Reply.root (expandRoot hmac result.1), result.2)) <$> work)
            (table_away_source prk table bytes selected)


/-- Selecting a fresh designated input is exactly the prefetched source derivation after mathematical reconstruction. Freshness here is table provenance, to be discharged by the original first-owner event. -/
theorem selectHidden_source (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (prk : HmacBlock)
    (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable)
    (unselected : table.hidden = none)
    (fresh : ∀ bytes, PqxdhJointDhExtractFamily.input joint dh seed scalar message = some bytes →
      table.cache bytes = none) :
    (fun result => (Reply.materialize hmac prk result.1, result.2.fill prk)) <$>
      (selectHidden joint dh seed scalar message).run table =
        (programmedDerive hmac joint dh seed scalar prk message).run table.cache := by
  unfold selectHidden programmedDerive
  dsimp only [StateT.run]
  cases input : PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => simp [map_pure, Reply.materialize, HiddenTable.fill, unselected]
  | some bytes =>
      simp [fresh bytes input, programmedRead, Reply.materialize, HiddenTable.fill]

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

set_option linter.deprecated false in
/-- Exact distributional form of the already checked flat coupling; the complete source game state is retained and only family history is projected away. -/
theorem flat_step_projection (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) (state : GameState KemSK × PqxdhJointDhExtractFamily.State) :
    𝒮[(fun result => (result.1, project result.2)) <$>
      (flatReal setup codec checks publicValue beaconSeed seed scalar query).run state] =
      𝒮[(skeleton setup codec checks publicValue beaconSeed
        (realServices seed scalar setup codec checks) query).run (project state)] := by
  apply evalSPMF_eq_of_relTriple_eqRel
  have paired := relTriple_post_mono (flat_couple setup codec checks publicValue beaconSeed seed scalar query state)
    (fun left right related => show (left.1, project left.2) = right from
      Prod.ext related.1 related.2.symm)
  simpa only [id_map, EqRel] using relTriple_map
    (f := fun result : ServerAuthSpec.Range query × (GameState KemSK × PqxdhJointDhExtractFamily.State) =>
      (result.1, project result.2)) (g := id) (R := Eq) paired


/-- Every flat source operation inherits B4a's original state invariant and chronological ghost growth, and keeps the source marks absent. -/
theorem realStep_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK HmacOracle.QueryCache)
    (marks : state.2.1 = fun _ => false)
    (result : ServerAuthSpec.Range query × FlatState KemSK HmacOracle.QueryCache)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed
      (realServices seed scalar setup codec checks) query).run state)) :
    (GameInv Reader Response setup publicValue state.1 → GameInv Reader Response setup publicValue result.2.1) ∧
      Grows state.1 result.2.1 ∧ result.2.2.1 = fun _ => false := by
  let original : GameState KemSK × PqxdhJointDhExtractFamily.State := (state.1, ⟨[], state.2.2⟩)
  have projected : project original = state := by
    change (state.1, (fun _ => false), state.2.2) = state
    rw [← marks]
  have distribution := flat_step_projection setup codec checks publicValue beaconSeed seed scalar query original
  rw [projected] at distribution
  have projectedSupport : result ∈ support ((fun result => (result.1, project result.2)) <$>
      (flatReal setup codec checks publicValue beaconSeed seed scalar query).run original) := by
    simpa only [support_eq_evalSPMF_support, distribution] using supported
  rw [support_map] at projectedSupport
  obtain ⟨sourceResult, sourceSupported, rfl⟩ := projectedSupport
  simp only [flatReal, interp, StateT.run, support_map, Set.mem_image] at sourceSupported
  obtain ⟨evaluated, evaluatedSupported, rfl⟩ := sourceSupported
  have nativeSupport : evaluated.1 ∈ support
      ((authHandler setup codec checks publicValue beaconSeed query).run original.1) := by
    apply support_simulateQ_run'_subset
      (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ
        PqxdhJointDhExtractRoot.reduction)
      ((authHandler setup codec checks publicValue beaconSeed query).run original.1) original.2
    rw [StateT.run'_eq, support_map]
    exact ⟨evaluated, by simpa only [StateT.run] using evaluatedSupported, rfl⟩
  have kept := authHandler_step codec checks beaconSeed query original.1 evaluated.1 nativeSupport
  exact ⟨kept.1, kept.2.1, rfl⟩


/-- Any fixed prefetched block has source-supported complete query outcomes, because every block is supported by the uniform sampler in the checked eager law. -/
theorem programmedStep_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (prk : HmacBlock) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HmacOracle.QueryCache)
    (result : ServerAuthSpec.Range query × FlatState KemSK HmacOracle.QueryCache)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed
      (programmedServices seed scalar setup codec checks prk) query).run state)) :
    result ∈ support ((skeleton setup codec checks publicValue beaconSeed
      (realServices seed scalar setup codec checks) query).run state) := by
  have mixed : result ∈ support (do
      let value ← $ᵗ HmacBlock
      (skeleton setup codec checks publicValue beaconSeed
        (programmedServices seed scalar setup codec checks value) query).run state) := by
    rw [mem_support_bind_iff]
    exact ⟨prk, mem_support_uniformSample HmacBlock, supported⟩
  simpa only [support_eq_evalSPMF_support,
    programmedStep_sample setup codec checks publicValue beaconSeed seed scalar query state] using mixed

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual input touched by the designated source session, or by the Beacon when it owns the last coordinate. No key equality or honest-target condition is used. -/
def SelectedAt (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) (bytes : Pqxdh.Bytes) : Prop :=
  if j.val < Q then
    ∃ message reply, Touch.session j.val message reply ∈ ghost.touches ∧
      rootInput setup seed scalar message = some bytes
  else beaconInput setup seed scalar ghost.touches = some bytes

/-- The owner calculation at a supplied actual input, preserving the original chronological first-touch rule. -/
def ownerAt (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (bytes : Pqxdh.Bytes) (touches : List Touch) : Option (Fin (Q + 1)) :=
  match touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes)) with
  | some (.session index _ _) => if bound : index < Q then some ⟨index, Nat.lt_succ_of_lt bound⟩ else none
  | some (.adversary _) => none
  | _ => some (Fin.last Q)

/-- Refusal is a property of the actual source log: the selected input was first owned elsewhere, or was queried through the public table. -/
def SelectedBad (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) : Prop :=
  ∃ bytes, SelectedAt setup seed scalar Q j ghost bytes ∧
    (ownerAt setup seed scalar Q bytes ghost.touches ≠ some j ∨ Touch.adversary bytes ∈ ghost.touches)

/-- On the original per-entry event, a reached designated input is exactly the accepted Beacon's root input. This uses the source invariant's unique session touch, not injectivity of a cryptographic constructor. -/
theorem selectedAt_beacon (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (Q : Nat) (j : Fin (Q + 1)) (state : GameState KemSK)
    (invariant : GameInv Reader Response setup publicValue state)
    (event : EntryEvent setup seed scalar Q j state.ghost) (bytes : Pqxdh.Bytes)
    (selected : SelectedAt setup seed scalar Q j state.ghost bytes) :
    beaconInput setup seed scalar state.ghost.touches = some bytes := by
  by_cases session : j.val < Q
  · have accepted : ∃ snap, state.ghost.acceptance = some snap :=
      event.1.elim (fun win => ⟨win.choose, win.choose_spec.1⟩)
        (fun win => ⟨win.choose, win.choose_spec.1⟩)
    obtain ⟨snap, accepted⟩ := accepted
    obtain ⟨before, beaconTouch, snapEq, clean⟩ := invariant.atomic snap accepted
    have partner := owner_session_ghost setup seed scalar Q state.ghost snap
      (invariant.frozen snap accepted).1 before beaconTouch snapEq clean j event.2.2.2 session
    obtain ⟨message, reply, touched, rooted⟩ :
        ∃ message reply, Touch.session j.val message reply ∈ state.ghost.touches ∧
          rootInput setup seed scalar message = some bytes := by
      simpa only [SelectedAt, session, ↓reduceIte] using selected
    obtain ⟨otherMessage, otherReply, otherBytes, otherTouched, otherRooted, beaconRooted⟩ := partner
    have same := (invariant.sessionOnce j.val message reply otherMessage otherReply touched
      ((invariant.frozen snap accepted).1.subset otherTouched)).1
    have sameBytes : otherBytes = bytes := Option.some.inj (otherRooted.symm.trans ((congrArg (rootInput setup seed scalar) same).symm.trans rooted))
    exact sameBytes ▸ beaconInput_prefix setup seed scalar _ _ otherBytes beaconRooted
      (invariant.frozen snap accepted).1
  · simpa only [SelectedAt, session, ↓reduceIte] using selected

/-- Neither hidden-table refusal is compatible with the original authenticated per-entry event. The exclusion follows from the original owner and public-query events and the source invariant. -/
theorem entry_not_selectedBad (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (Q : Nat) (j : Fin (Q + 1)) (state : GameState KemSK)
    (invariant : GameInv Reader Response setup publicValue state)
    (event : EntryEvent setup seed scalar Q j state.ghost) :
    ¬ SelectedBad setup seed scalar Q j state.ghost := by
  rintro ⟨bytes, selected, refused⟩
  have beacon := selectedAt_beacon setup seed scalar publicValue Q j state invariant event bytes selected
  exact refused.elim (fun wrong => wrong (by
    have owned := event.2.2.2
    unfold entryOwner at owned
    rw [beacon] at owned
    unfold ownerAt
    split <;> simp_all))
    (fun queried => event.2.1 ⟨bytes, beacon, queried⟩)

/-- Once a designated source touch exists, later chronological extensions retain its actual input. -/
theorem selectedAt_prefix (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (before after : Ghost) (bytes : Pqxdh.Bytes)
    (grown : before.touches <+: after.touches)
    (selected : SelectedAt setup seed scalar Q j before bytes) :
    SelectedAt setup seed scalar Q j after bytes := by
  unfold SelectedAt at selected ⊢
  split at selected
  · rename_i session
    simpa only [session, ↓reduceIte] using selected.imp (fun message rest =>
      rest.imp (fun reply pair => ⟨grown.subset pair.1, pair.2⟩))
  · rename_i beacon
    simpa only [beacon, ↓reduceIte] using
      beaconInput_prefix setup seed scalar _ _ bytes selected grown

/-- A designated input has a literal matching touch in the original log. -/
theorem selectedAt_touched (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (ghost : Ghost) (bytes : Pqxdh.Bytes)
    (selected : SelectedAt setup seed scalar Q j ghost bytes) :
    ∃ touch ∈ ghost.touches, touchInput setup seed scalar touch = some bytes := by
  unfold SelectedAt at selected
  split at selected
  · obtain ⟨message, reply, member, rooted⟩ := selected
    exact ⟨.session j.val message reply, member, rooted⟩
  · unfold beaconInput at selected
    rw [Option.bind_eq_some_iff] at selected
    obtain ⟨message, found, rooted⟩ := selected
    unfold firstBeacon at found
    obtain ⟨touch, member, hit⟩ := List.exists_of_findSome?_eq_some found
    cases touch with
    | beacon other =>
        simp only [Option.some.injEq] at hit
        subst hit
        exact ⟨_, member, rooted⟩
    | session index other reply => simp at hit
    | adversary other => simp at hit

/-- Once an input has been touched, extending the chronological log cannot change its first owner. -/
theorem ownerAt_prefix (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (bytes : Pqxdh.Bytes) (before after : List Touch) (grown : before <+: after)
    (present : ∃ touch ∈ before, touchInput setup seed scalar touch = some bytes) :
    ownerAt setup seed scalar Q bytes after = ownerAt setup seed scalar Q bytes before := by
  obtain ⟨rest, rfl⟩ := grown
  have found : (before.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes))).isSome := by
    rw [List.find?_isSome]
    exact present.imp (fun touch pair => ⟨pair.1, by simpa using pair.2⟩)
  obtain ⟨touch, found⟩ := Option.isSome_iff_exists.mp found
  simp only [ownerAt, List.find?_append, found]
  rfl

/-- The refusal event is sticky along the exact source touch history. No final-decision restriction is needed. -/
theorem selectedBad_prefix (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (before after : Ghost) (grown : before.touches <+: after.touches)
    (bad : SelectedBad setup seed scalar Q j before) : SelectedBad setup seed scalar Q j after := by
  obtain ⟨bytes, selected, refused⟩ := bad
  refine ⟨bytes, selectedAt_prefix setup seed scalar Q j before after bytes grown selected, ?_⟩
  exact refused.imp
    (fun wrong same => wrong ((ownerAt_prefix setup seed scalar Q bytes before.touches after.touches grown
      (selectedAt_touched setup seed scalar Q j before bytes selected)).symm.trans same))
    (fun queried => grown.subset queried)

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Every occupied Extract-table input was touched in the actual chronological source log. This records inputs only and places no restriction on equal output blocks. -/
def CacheOrigin (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (ghost : Ghost) (cache : HmacOracle.QueryCache) : Prop :=
  ∀ bytes, cache bytes ≠ none → ∃ touch ∈ ghost.touches, touchInput setup seed scalar touch = some bytes

/-- A source table operation can add only the listed inputs; cached values remain unconstrained here. -/
def CacheAdds (inputs : List Pqxdh.Bytes) (before after : HmacOracle.QueryCache) : Prop :=
  ∀ bytes, after bytes ≠ none → before bytes ≠ none ∨ bytes ∈ inputs

/-- A lazy random-oracle read adds only its literal queried input. -/
theorem oracle_adds (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache)
    (result : HmacBlock × HmacOracle.QueryCache)
    (supported : result ∈ support ((HmacOracle.randomOracle bytes).run cache)) :
    CacheAdds [bytes] cache result.2 := by
  rw [randomOracle.run_eq] at supported
  cases hit : cache bytes with
  | some value =>
      simp only [hit, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact fun _ occupied => Or.inl occupied
  | none =>
      simp only [hit, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨value, _, rfl⟩ := supported
      intro input occupied
      by_cases same : input = bytes
      · exact Or.inr (by simp [same])
      · exact Or.inl (by simpa only [QueryCache.cacheQuery_of_ne _ _ same] using occupied)

/-- A real derivation can add only its exact joint-source input, including ordinary DH rejection. -/
theorem realDerive_adds (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (cache : HmacOracle.QueryCache)
    (result : Reply × HmacOracle.QueryCache)
    (supported : result ∈ support ((realDerive setup.hmac setup.joint setup.dh seed scalar message).run cache)) :
    CacheAdds (rootInput setup seed scalar message).toList cache result.2 := by
  unfold realDerive at supported
  dsimp only [StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
  | none =>
      simp only [input, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact fun _ occupied => Or.inl occupied
  | some bytes =>
      simp only [input, support_map, Set.mem_image] at supported
      obtain ⟨read, readSupported, rfl⟩ := supported
      simpa only [rootInput, input, Option.toList_some] using oracle_adds bytes cache read readSupported

/-- Cache provenance survives a complete source transition whenever its old touches remain and every newly permitted cache input has a literal new touch. -/
theorem CacheOrigin.transport (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : Ghost) (oldCache newCache : HmacOracle.QueryCache) (inputs : List Pqxdh.Bytes)
    (origin : CacheOrigin setup seed scalar before oldCache) (grown : before.touches <+: after.touches)
    (adds : CacheAdds inputs oldCache newCache)
    (newTouches : ∀ bytes ∈ inputs, ∃ touch ∈ after.touches, touchInput setup seed scalar touch = some bytes) :
    CacheOrigin setup seed scalar after newCache := by
  intro bytes occupied
  rcases adds bytes occupied with old | fresh
  · exact (origin bytes old).imp (fun touch pair => ⟨grown.subset pair.1, pair.2⟩)
  · exact newTouches bytes fresh

/-- The source derivation continuation logs its literal session touch on rejection and success alike. -/
theorem afterDerive_touches (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (index : Nat) (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding)
    (reply : Reply) (game : GameState KemSK) :
    (afterDerive setup publicValue index input reply game).2.ghost.touches =
      game.ghost.touches ++ [.session index (PqxdhServerRelatedRootInput.message input) reply.value] := by
  cases reply <;> rfl

/-- Final receive and binding checks freeze an acceptance but do not rewrite the source touch history. -/
theorem finishOutcome_touches (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (finishOutcome control game staged).2.ghost.touches = game.ghost.touches := by
  exact Ghost.accept_touches _ _

/-- Every actual source interface operation preserves provenance of the complete retained Extract cache. -/
theorem realStep_cacheOrigin (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HmacOracle.QueryCache)
    (origin : CacheOrigin setup seed scalar state.1.ghost state.2.2)
    (result : ServerAuthSpec.Range query × FlatState KemSK HmacOracle.QueryCache)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed
      (realServices seed scalar setup codec checks) query).run state)) :
    CacheOrigin setup seed scalar result.2.1.ghost result.2.2.2 := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact origin
  | inr query =>
      cases query with
      | accept raw =>
          simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨collected, _, supported⟩ := supported
          cases collected with
          | mk answer consumed =>
            cases answer with
            | none =>
                simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact origin
            | some input =>
                dsimp only at supported
                split at supported
                · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
                  obtain ⟨derived, derivedSupported, rfl⟩ := supported
                  have adds := realDerive_adds setup seed scalar
                    (PqxdhServerRelatedRootInput.message input) state.2.2 derived derivedSupported
                  apply CacheOrigin.transport setup seed scalar _ _ state.2.2 derived.2 _ origin
                    (by rw [afterDerive_touches]; exact ⟨_, rfl⟩) adds
                  intro bytes belongs
                  refine ⟨.session state.1.sessions (PqxdhServerRelatedRootInput.message input) derived.1.value, ?_, ?_⟩
                  · rw [afterDerive_touches]; exact List.mem_append_right _ (List.mem_singleton_self _)
                  · simpa [touchInput] using belongs
                · simp only [support_pure, Set.mem_singleton_iff] at supported
                  subst supported
                  exact origin
      | build session payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending session with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              exact origin
          | some token =>
              simp only [found, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
              obtain ⟨built, _, rfl⟩ := supported
              exact origin
      | finish raw =>
          simp only [skeleton, finishStep, StateT.run] at supported
          cases phase : state.1.beacon.beacon.phase <;> simp only [phase] at supported
          all_goals try { simp only [support_pure, Set.mem_singleton_iff] at supported; subst supported; exact origin }
          simp only [mem_support_bind_iff] at supported
          obtain ⟨prepared, _, supported⟩ := supported
          cases prepared with
          | none =>
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              simpa only [CacheOrigin, finishOutcome_touches] using origin
          | some pending =>
              simp only [mem_support_bind_iff] at supported
              obtain ⟨derived, derivedSupported, supported⟩ := supported
              have adds := realDerive_adds setup seed scalar
                (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected) state.2.2 derived derivedSupported
              have updated : CacheOrigin setup seed scalar
                  { state.1.ghost with touches := state.1.ghost.touches ++
                    [.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)] } derived.2 := by
                apply CacheOrigin.transport setup seed scalar _ _ state.2.2 derived.2 _ origin
                  ⟨_, rfl⟩ adds
                intro bytes belongs
                exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by simpa [touchInput] using belongs⟩
              cases derived with
              | mk reply cache =>
                cases reply with
                | rejected =>
                    simp only [support_pure, Set.mem_singleton_iff] at supported
                    subst supported
                    simpa only [CacheOrigin, finishOutcome_touches] using updated
                | root root =>
                    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
                    obtain ⟨staged, _, rfl⟩ := supported
                    simpa only [CacheOrigin, finishOutcome_touches] using updated
                | hidden =>
                    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
                    obtain ⟨staged, _, rfl⟩ := supported
                    simpa only [CacheOrigin, finishOutcome_touches] using updated
      | hmac key message =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split at supported
          · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
            obtain ⟨read, readSupported, rfl⟩ := supported
            apply CacheOrigin.transport setup seed scalar _ _ state.2.2 read.2 [message] origin
              ⟨_, rfl⟩ (oracle_adds message state.2.2 read readSupported)
            intro bytes belongs
            simp only [List.mem_singleton] at belongs
            subst belongs
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact origin
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨read, _, rfl⟩ := supported
          exact origin
      | reveal keyId =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact origin

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Before the designated session is allocated, any already-touched input has another first owner. -/
theorem ownerAt_before_session (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (session : j.val < Q) (bytes : Pqxdh.Bytes) (touches : List Touch)
    (below : ∀ index message reply, Touch.session index message reply ∈ touches → index < j.val)
    (present : ∃ touch ∈ touches, touchInput setup seed scalar touch = some bytes) :
    ownerAt setup seed scalar Q bytes touches ≠ some j := by
  have found : (touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes))).isSome := by
    rw [List.find?_isSome]
    exact present.imp (fun touch pair => ⟨pair.1, by simpa using pair.2⟩)
  obtain ⟨touch, found⟩ := Option.isSome_iff_exists.mp found
  have member := List.mem_of_find?_eq_some found
  unfold ownerAt
  rw [found]
  cases touch with
  | session index message reply =>
      have earlier := below index message reply member
      have bound : index < Q := earlier.trans session
      simp only [bound, ↓reduceDIte, ne_eq, Option.some.injEq, Fin.ext_iff]
      omega
  | beacon message =>
      simp only [ne_eq, Option.some.injEq, Fin.ext_iff, Fin.val_last]
      omega
  | adversary other => simp

/-- Before the Beacon's one-shot finish, an already-touched input cannot first be owned by the Beacon. -/
theorem ownerAt_before_beacon (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (bytes : Pqxdh.Bytes) (touches : List Touch)
    (clean : ∀ message, Touch.beacon message ∉ touches)
    (present : ∃ touch ∈ touches, touchInput setup seed scalar touch = some bytes) :
    ownerAt setup seed scalar Q bytes touches ≠ some (Fin.last Q) := by
  have found : (touches.find? (fun touch => decide (touchInput setup seed scalar touch = some bytes))).isSome := by
    rw [List.find?_isSome]
    exact present.imp (fun touch pair => ⟨pair.1, by simpa using pair.2⟩)
  obtain ⟨touch, found⟩ := Option.isSome_iff_exists.mp found
  have member := List.mem_of_find?_eq_some found
  unfold ownerAt
  rw [found]
  cases touch with
  | session index message reply =>
      dsimp only
      split
      · simp only [ne_eq, Option.some.injEq, Fin.ext_iff, Fin.val_last]
        omega
      · simp
  | beacon message => exact (clean message member).elim
  | adversary other => simp

/-- A cached input selected by its designated new Server session is already permanently excluded by the source event. All premises are source state/trace facts; no cache-miss condition is assumed. -/
theorem session_cache_refusal (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (Q : Nat) (j : Fin (Q + 1)) (before : GameState KemSK)
    (cache : HmacOracle.QueryCache) (after : Ghost) (bytes : Pqxdh.Bytes)
    (invariant : GameInv Reader Response setup publicValue before)
    (origin : CacheOrigin setup seed scalar before.ghost cache)
    (session : j.val < Q) (next : before.sessions = j.val) (occupied : cache bytes ≠ none)
    (grown : before.ghost.touches <+: after.touches)
    (selected : SelectedAt setup seed scalar Q j after bytes) :
    SelectedBad setup seed scalar Q j after := by
  have present := origin bytes occupied
  have earlier := ownerAt_before_session setup seed scalar Q j session bytes before.ghost.touches
    (fun index message reply member => next ▸ invariant.touched index message reply member) present
  exact ⟨bytes, selected, Or.inl (fun owned => earlier
    ((ownerAt_prefix setup seed scalar Q bytes before.ghost.touches after.touches grown present).symm.trans owned))⟩

/-- A cached input selected by an active Beacon finish is likewise already owned elsewhere in the original chronological log. -/
theorem beacon_cache_refusal (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) (Q : Nat) (before : GameState KemSK)
    (cache : HmacOracle.QueryCache) (after : Ghost) (bytes : Pqxdh.Bytes)
    (invariant : GameInv Reader Response setup publicValue before)
    (origin : CacheOrigin setup seed scalar before.ghost cache)
    (active : InitSent before) (occupied : cache bytes ≠ none)
    (grown : before.ghost.touches <+: after.touches)
    (selected : SelectedAt setup seed scalar Q (Fin.last Q) after bytes) :
    SelectedBad setup seed scalar Q (Fin.last Q) after := by
  have present := origin bytes occupied
  have earlier := ownerAt_before_beacon setup seed scalar Q bytes before.ghost.touches
    (invariant.clean active) present
  exact ⟨bytes, selected, Or.inl (fun owned => earlier
    ((ownerAt_prefix setup seed scalar Q bytes before.ghost.touches after.touches grown present).symm.trans owned))⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The preserved source facts needed by the omitted-entry coupling: original protocol invariant, absent source marks and literal cache provenance. -/
def SourceInvariant (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (state : FlatState KemSK HmacOracle.QueryCache) : Prop :=
  GameInv Reader Response setup (context.publicValue setup) state.1 ∧
    state.2.1 = (fun _ => false) ∧ CacheOrigin setup context.seed context.scalar state.1.ghost state.2.2

/-- A complete prefetched query projects to a supported original-source query for every fixed block. This does not merely compare marginal outputs. -/
theorem prefetchedStep_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (query : ServerAuthSpec.Domain) (state : EntryState KemSK)
    (result : ServerAuthSpec.Range query × EntryState KemSK)
    (supported : result ∈ support ((prefetchedHandler setup codec checks context Q j prk query).run state)) :
    (result.1, result.2.1) ∈ support ((skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks) query).run state.1) := by
  simp only [prefetchedHandler, once, StateT.run] at supported
  split at supported
  · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, member, rfl⟩ := supported
    exact member
  · split at supported
    · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨step, member, rfl⟩ := supported
      exact programmedStep_support setup codec checks (context.publicValue setup) context.beaconSeed
        context.seed context.scalar prk query state.1 step member
    · simp only [latch, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨step, member, rfl⟩ := supported
      exact member

/-- Every prefetched query preserves the original complete protocol invariant and cache provenance and grows the original chronological logs. -/
theorem prefetchedStep_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (query : ServerAuthSpec.Domain) (state : EntryState KemSK)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context state.1)
    (result : ServerAuthSpec.Range query × EntryState KemSK)
    (supported : result ∈ support ((prefetchedHandler setup codec checks context Q j prk query).run state)) :
    SourceInvariant (Reader := Reader) (Response := Response) setup context result.2.1 ∧
      Grows state.1.1 result.2.1.1 := by
  have original := prefetchedStep_support setup codec checks context Q j prk query state result supported
  have kept := realStep_invariant setup codec checks (context.publicValue setup) context.beaconSeed
    context.seed context.scalar query state.1 invariant.2.1 (result.1, result.2.1) original
  exact ⟨⟨kept.1 invariant.1, kept.2.2,
    realStep_cacheOrigin setup codec checks (context.publicValue setup) context.beaconSeed context.seed
      context.scalar query state.1 invariant.2.2 (result.1, result.2.1) original⟩, kept.2.1⟩

/-- Once a source refusal occurs, every later adaptive query keeps it; original state validity and literal cache provenance are retained alongside the event. -/
theorem prefetchedStep_bad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (query : ServerAuthSpec.Domain) (state : EntryState KemSK)
    (bad : SourceInvariant (Reader := Reader) (Response := Response) setup context state.1 ∧
      SelectedBad setup context.seed context.scalar Q j state.1.1.ghost)
    (result : ServerAuthSpec.Range query × EntryState KemSK)
    (supported : result ∈ support ((prefetchedHandler setup codec checks context Q j prk query).run state)) :
    SourceInvariant (Reader := Reader) (Response := Response) setup context result.2.1 ∧
      SelectedBad setup context.seed context.scalar Q j result.2.1.1.ghost := by
  have kept := prefetchedStep_invariant setup codec checks context Q j prk query state bad.1 result supported
  exact ⟨kept.1, selectedBad_prefix setup context.seed context.scalar Q j state.1.1.ghost result.2.1.1.ghost
    kept.2.touches bad.2⟩

/-- The original R1 experiment's ordered context sampler supplies the invariant at the empty Extract cache. Arbitrary caller-supplied contexts are not assumed well formed. -/
theorem contextSample_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (supported : context ∈ support (contextSample setup codec)) :
    SourceInvariant (Reader := Reader) (Response := Response) setup context
      (contextState setup context, fun _ => false, ∅) := by
  simp only [contextSample, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, scalar, _, beaconSeed, _, oneTime, _, keys, _, published, publishedSupported, rfl⟩ := supported
  refine ⟨?_, rfl, ?_⟩
  · exact inv_initial setup codec beaconSeed _ oneTime keys.1 keys.2 published publishedSupported
  · intro bytes occupied
    exact (occupied rfl).elim

/-- The entire unchanged adaptive adversary preserves the source invariant for every fixed prefetched block, starting from the actual source context sampler. -/
theorem prefetchedRun_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (contextSupported : context ∈ support (contextSample setup codec))
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (result : EntryState KemSK)
    (supported : result ∈ support (prefetchedRun setup codec checks adversary revealSeed context Q j prk)) :
    SourceInvariant (Reader := Reader) (Response := Response) setup context result.1 := by
  simp only [prefetchedRun, support_map, Set.mem_image] at supported
  obtain ⟨run, member, rfl⟩ := supported
  exact support_run_bad (prefetchedHandler setup codec checks context Q j prk)
    (fun state => SourceInvariant (Reader := Reader) (Response := Response) setup context state.1)
    (fun query state invariant result supported =>
      (prefetchedStep_invariant setup codec checks context Q j prk query state invariant result supported).1)
    (adversary (contextInput setup revealSeed context))
    ((contextState setup context, fun _ => false, ∅), false)
    (contextSample_invariant setup codec context contextSupported) run member

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.fill_away' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.fill_away
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.fill_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.fill_update
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.table_away_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.table_away_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenDerive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenDerive_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectHidden_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectHidden_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.flat_step_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.flat_step_projection
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.realStep_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.realStep_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedStep_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedStep_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedAt_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedAt_beacon
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_not_selectedBad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_not_selectedBad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedAt_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedAt_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedAt_touched' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedAt_touched
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ownerAt_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ownerAt_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedBad_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectedBad_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.oracle_adds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.oracle_adds
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.realDerive_adds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.realDerive_adds
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.CacheOrigin.transport' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.CacheOrigin.transport
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.afterDerive_touches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.afterDerive_touches
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishOutcome_touches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finishOutcome_touches
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.realStep_cacheOrigin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.realStep_cacheOrigin
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ownerAt_before_session' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ownerAt_before_session
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ownerAt_before_beacon' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ownerAt_before_beacon
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.session_cache_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.session_cache_refusal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.beacon_cache_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.beacon_cache_refusal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedStep_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedStep_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedStep_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedStep_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedStep_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedStep_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.contextSample_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.contextSample_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedRun_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedRun_invariant
