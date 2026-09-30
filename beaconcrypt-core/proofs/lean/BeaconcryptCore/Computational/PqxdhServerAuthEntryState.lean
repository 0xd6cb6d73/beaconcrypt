import BeaconcryptCore.Computational.PqxdhServerAuthEntryTable

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

/-- Mathematical reconstruction of a marked pending token. The factored executable uses its original pending fields and never calls this function. -/
def restoreToken (root : RootOutput) (marked : Bool)
    (token : PqxdhServerRelatedRootConsumer.Returned) : PqxdhServerRelatedRootConsumer.Returned :=
  if marked then { token with root := root } else token

/-- The two games keep exact native roles, public state and cache. Only marked pending roots and instrumented ghost root replies are represented differently. -/
structure ProtocolRel (root : RootOutput) (marks : Marks) (left right : GameState KemSK) : Prop where
  ctx : left.ctx = right.ctx
  server : left.server = right.server
  beacon : left.beacon = right.beacon
  sessions : left.sessions = right.sessions
  pending : ∀ index, left.pending index = (right.pending index).map (restoreToken root (marks index))
  ghost : eraseGhost left.ghost = eraseGhost right.ghost

/-- With no marks, the original complete state is related to itself for every proposed challenge root. -/
theorem ProtocolRel.initial (root : RootOutput) (state : GameState KemSK) :
    ProtocolRel root (fun _ => false) state state := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
  intro index
  cases state.pending index <;> rfl

/-- Root erasure commutes with appending a literal source touch. -/
theorem eraseGhost_touch (ghost : Ghost) (touch : Touch) :
    eraseGhost { ghost with touches := ghost.touches ++ [touch] } =
      { eraseGhost ghost with touches := (eraseGhost ghost).touches ++ [eraseTouch touch] } := by
  simp only [eraseGhost, List.map_append, List.map_singleton]

/-- Root erasure commutes with recording actual successful seal contexts. -/
theorem eraseGhost_seals (ghost : Ghost) (seals : List (Nat × RawCtxSourceSend.SealContext)) :
    eraseGhost { ghost with seals := ghost.seals ++ seals } =
      { eraseGhost ghost with seals := (eraseGhost ghost).seals ++ seals } := by
  rfl

/-- Root erasure commutes with freezing the actual first acceptance snapshot. -/
theorem eraseGhost_accept (ghost : Ghost) (accepted : Option Accepted) :
    eraseGhost (ghost.accept accepted) = (eraseGhost ghost).accept accepted := by
  cases accepted with
  | none => rfl
  | some accepted =>
      cases old : ghost.acceptance <;> simp [Ghost.accept, eraseGhost, eraseSnap, old]

/-- The complete original per-entry event is unchanged by the protocol state relation. -/
theorem ProtocolRel.entry (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (Q : Nat) (j : Fin (Q + 1)) (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) :
    EntryEvent setup seed scalar Q j left.ghost ↔ EntryEvent setup seed scalar Q j right.ghost := by
  rw [← entryEvent_erase setup seed scalar Q j left.ghost, related.ghost,
    entryEvent_erase setup seed scalar Q j right.ghost]

/-- Appending source touches with the same root-erased fields preserves the relation on complete protocol states. -/
theorem ProtocolRel.touch (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) (first second : Touch)
    (same : eraseTouch first = eraseTouch second) :
    ProtocolRel root marks
      { left with ghost := { left.ghost with touches := left.ghost.touches ++ [first] } }
      { right with ghost := { right.ghost with touches := right.ghost.touches ++ [second] } } := by
  refine ⟨related.ctx, related.server, related.beacon, related.sessions, related.pending, ?_⟩
  rw [eraseGhost_touch, eraseGhost_touch, related.ghost, same]

/-- The original source prefix writes the same consumed-registration state and advances the same attempt counter in both runs. -/
theorem ProtocolRel.prefix (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) (consumed : List Pqxdh.Bytes) :
    ProtocolRel root marks
      { left with sessions := left.sessions + 1, server := { left.server with consumed := consumed } }
      { right with sessions := right.sessions + 1, server := { right.server with consumed := consumed } } := by
  refine ⟨related.ctx, ?_, related.beacon, congrArg (· + 1) related.sessions, related.pending, related.ghost⟩
  rw [related.server]

/-- The source root consumer and the hidden-label consumer return the same optional token index and preserve all protocol fields under marked-token reconstruction. -/
theorem ProtocolRel.derive (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (prk : HmacBlock) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel (expandRoot setup.hmac prk) marks left right) (index : Nat)
    (fresh : marks index = false)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding) (reply : Reply) :
    (afterDerive setup publicValue index input (Reply.materialize setup.hmac prk reply) left).1 =
        (afterDerive setup publicValue index input reply right).1 ∧
      ProtocolRel (expandRoot setup.hmac prk)
        (if reply.isHidden then Function.update marks index true else marks)
        (afterDerive setup publicValue index input (Reply.materialize setup.hmac prk reply) left).2
        (afterDerive setup publicValue index input reply right).2 := by
  cases reply with
  | rejected =>
      exact ⟨rfl, ProtocolRel.touch _ marks left right related _ _ rfl⟩
  | root value =>
      refine ⟨rfl, related.ctx, ?_, related.beacon, related.sessions, ?_, ?_⟩
      · dsimp only [afterDerive, Reply.materialize, Reply.value]
        rw [related.server]
      · intro other
        by_cases same : other = index
        · subst other
          simp [afterDerive, Reply.materialize, Reply.value, Reply.isHidden, restoreToken, fresh]
        · simpa only [afterDerive, Reply.materialize, Reply.value, Reply.isHidden, Bool.false_eq_true,
            ↓reduceIte, Function.update_of_ne same] using related.pending other
      · dsimp only [afterDerive, Reply.materialize, Reply.value]
        rw [eraseGhost_touch, eraseGhost_touch, related.ghost]
  | hidden =>
      refine ⟨rfl, related.ctx, ?_, related.beacon, related.sessions, ?_, ?_⟩
      · dsimp only [afterDerive, Reply.materialize, Reply.value]
        rw [related.server]
      · intro other
        by_cases same : other = index
        · subst other
          simp [afterDerive, Reply.materialize, Reply.value, Reply.isHidden, restoreToken]
        · simpa only [afterDerive, Reply.materialize, Reply.value, Reply.isHidden, ↓reduceIte,
            Function.update_of_ne same] using related.pending other
      · dsimp only [afterDerive, Reply.materialize, Reply.value]
        rw [eraseGhost_touch, eraseGhost_touch, related.ghost]
        rfl

/-- A common shared-CTX operation retains the relation after installing its exact returned cache. -/
theorem ProtocolRel.context (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) (cache : CtxRomAuth.CtxRO.QueryCache) :
    ProtocolRel root marks { left with ctx := cache } { right with ctx := cache } :=
  ⟨rfl, related.server, related.beacon, related.sessions, related.pending, related.ghost⟩

/-- Actual response settlement, token consumption and the complete successful-seal trailer preserve the relation. -/
theorem ProtocolRel.build (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) (session : Nat)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × ServerState) × SealState) :
    (afterBuild session left result).1 = (afterBuild session right result).1 ∧
      ProtocolRel root marks (afterBuild session left result).2 (afterBuild session right result).2 := by
  refine ⟨?_, rfl, ?_, related.beacon, related.sessions, ?_, ?_⟩
  · dsimp only [afterBuild]
    rw [related.server]
  · dsimp only [afterBuild]
    rw [related.server]
  · intro index
    by_cases same : index = session
    · subst index
      simp [afterBuild]
    · simpa only [afterBuild, Function.update_of_ne same] using related.pending index
  · dsimp only [afterBuild]
    rw [eraseGhost_seals, eraseGhost_seals, related.ghost]

/-- The actual final finish checks and frozen acceptance snapshot preserve the complete state relation for a common staged result. -/
theorem ProtocolRel.finish (root : RootOutput) (marks : Marks) (left right : GameState KemSK)
    (related : ProtocolRel root marks left right) (control : pqxdh.BeaconInitSent)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    (finishOutcome control left staged).1 = (finishOutcome control right staged).1 ∧
      ProtocolRel root marks (finishOutcome control left staged).2 (finishOutcome control right staged).2 := by
  refine ⟨?_, related.ctx, related.server, ?_, related.sessions, related.pending, ?_⟩
  · dsimp only [finishOutcome]
    rw [related.beacon]
  · dsimp only [finishOutcome]
    rw [related.beacon]
  · dsimp only [finishOutcome]
    rw [eraseGhost_accept, eraseGhost_accept, related.beacon, related.ghost]

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

/-- The omitted-entry run retains every protocol field and the one-shot operation flag, with the selected Extract block absent from its table. -/
abbrev HiddenState (KemSK : Type) := FlatState KemSK HiddenTable × Bool

/-- Feed only the original operation counter and phase to the designated-operation test. The retained cache argument is unused by that test. -/
def hiddenDesignated (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HiddenTable) : Bool :=
  designated Q j query (state.1, state.2.1, state.2.2.cache)

/-- Source-comparison services for the omitted entry. Only the two continuation callbacks use the mathematical root; the final factorization replaces both by the actual 108-byte consumers. -/
noncomputable def sourceHiddenServices (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (root : RootOutput) : Services Response HiddenTable where
  derive := hiddenDerive setup.hmac setup.joint setup.dh context.seed context.scalar
  table := hiddenPublic
  hiddenBuild token payload server := simulateQ (tailImpl setup codec checks)
    (PqxdhServerRegistrationPublication.build setup.source token.pending root payload () server)
  hiddenAfter pending := simulateQ (beaconNative setup codec)
    (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))

/-- Selection changes only the derive service, keeping both actual continuations and every other source operation. -/
noncomputable def selectingServices (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (services : Services Response HiddenTable) : Services Response HiddenTable :=
  { services with derive := selectHidden setup.joint setup.dh context.seed context.scalar }

/-- Once already refused, retain the refusal bit irrespective of later unrelated behavior. This changes no answer and makes no oracle query. -/
def keepHiddenBad {α : Type} (before : HiddenState KemSK) (result : α × HiddenState KemSK) : α × HiddenState KemSK :=
  if before.1.2.2.bad then
    (result.1, ((result.2.1.1, result.2.1.2.1, { result.2.1.2.2 with bad := true }), result.2.2))
  else result

/-- Complete adaptive omitted-entry handler. Its continuation services will be instantiated by the checked source or factor consumers; the Extract services and designation schedule remain fixed. -/
noncomputable def hiddenHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) : QueryImpl ServerAuthSpec (StateT (HiddenState KemSK) ProbComp) :=
  fun query state => keepHiddenBad state <$>
    (once (hiddenDesignated Q j)
      (skeleton setup codec checks (context.publicValue setup) context.beaconSeed services)
      (fun _ : Unit => skeleton setup codec checks (context.publicValue setup) context.beaconSeed
        (selectingServices setup context services)) () query).run state

/-- The private refusal bit is sticky for every complete hidden query and all its replies. -/
theorem hiddenHandler_bad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (bad : state.1.2.2.bad = true) (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    result.2.1.2.2.bad = true := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨step, _, rfl⟩ := supported
  simp only [keepHiddenBad, bad, ↓reduceIte]

/-- Before refusal the wrapper is exactly the complete one-shot hidden computation. -/
theorem hiddenHandler_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1))
    (services : Services Response HiddenTable) (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (good : state.1.2.2.bad = false) :
    (hiddenHandler setup codec checks context Q j services query).run state =
      (once (hiddenDesignated Q j)
        (skeleton setup codec checks (context.publicValue setup) context.beaconSeed services)
        (fun _ : Unit => skeleton setup codec checks (context.publicValue setup) context.beaconSeed
          (selectingServices setup context services)) () query).run state := by
  have same : keepHiddenBad (α := ServerAuthSpec.Range query) state = id := by
    funext result
    simp only [keepHiddenBad, good, Bool.false_eq_true, ↓reduceIte, id_eq]
  simp only [hiddenHandler, StateT.run, same, id_map]

/-- Complete good-state relation for the source and omitted-entry runs. Every clause is established from the actual initial sampler and preserved by source operations; none is an authentication or primitive security assumption. -/
structure EntryRel (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK) : Prop where
  source : SourceInvariant (Reader := Reader) (Response := Response) setup context left.1
  protocol : ProtocolRel (expandRoot setup.hmac prk) right.1.2.1 left.1.1 right.1.1
  cache : left.1.2.2 = right.1.2.2.fill prk
  flag : left.2 = right.2
  unselected : right.2 = false → right.1.2.2.hidden = none
  selected : ∀ bytes, right.1.2.2.hidden = some bytes →
    SelectedAt setup context.seed context.scalar Q j left.1.1.ghost bytes
  below : ∀ index, right.1.2.1 index = true → index < left.1.1.sessions
  marked : ∀ index, right.1.2.1 index = true →
    ∃ message reply bytes, Touch.session index message reply ∈ right.1.1.ghost.touches ∧
      right.1.2.2.hidden = some bytes ∧ rootInput setup context.seed context.scalar message = some bytes
  good : right.1.2.2.bad = false
  clean : right.1.2.2.Clean

/-- Designation depends only on the exact shared source counter and Beacon phase. -/
theorem designated_related (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (root : RootOutput) (left : FlatState KemSK HmacOracle.QueryCache)
    (right : FlatState KemSK HiddenTable) (related : ProtocolRel root right.2.1 left.1 right.1) :
    designated Q j query left = hiddenDesignated Q j query right := by
  cases query with
  | inl coin => rfl
  | inr query =>
      cases query <;> simp only [designated, hiddenDesignated, related.sessions, related.beacon]

/-- The original source context supplies the complete relation at the empty cache, before any operation is selected. -/
theorem EntryRel.initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (supported : context ∈ support (contextSample setup codec))
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      ((contextState setup context, fun _ => false, ∅), false)
      ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false) := by
  refine ⟨contextSample_invariant setup codec context supported, ProtocolRel.initial _ _, rfl, rfl,
    (fun _ => rfl), ?_, ?_, ?_, rfl, ?_⟩
  · intro bytes found
    cases found
  · intro index marked
    cases marked
  · intro index marked
    cases marked
  · intro bytes found
    cases found

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (ScalarBytes)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Adding only other inputs preserves absence of the omitted entry. This permits arbitrary equal output values at those other inputs. -/
theorem HiddenTable.Clean.update (before after : HiddenTable) (clean : before.Clean)
    (hidden : after.hidden = before.hidden) (inputs : List Pqxdh.Bytes)
    (adds : CacheAdds inputs before.cache after.cache)
    (away : ∀ bytes ∈ inputs, before.hidden ≠ some bytes) : after.Clean := by
  intro bytes selected
  by_contra occupied
  rcases adds bytes occupied with old | member
  · exact old (clean bytes (hidden ▸ selected))
  · exact away bytes member (hidden ▸ selected)

/-- An honest hidden-table derivation keeps its selected input, refusal flag and omitted-entry invariant. -/
theorem hiddenDerive_keeps (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable) (clean : table.Clean)
    (result : Reply × HiddenTable)
    (supported : result ∈ support ((hiddenDerive setup.hmac setup.joint setup.dh seed scalar message).run table)) :
    result.2.hidden = table.hidden ∧ result.2.bad = table.bad ∧ result.2.Clean := by
  simp only [hiddenDerive, StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
  | none =>
      simp only [input, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨rfl, rfl, clean⟩
  | some bytes =>
      simp only [input] at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨rfl, rfl, clean⟩
      · rename_i away
        simp only [ordinaryHiddenDerive, StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨read, readSupported, rfl⟩ := supported
        refine ⟨rfl, rfl, HiddenTable.Clean.update table _ clean rfl _
          (realDerive_adds setup seed scalar message table.cache read readSupported) ?_⟩
        intro other member
        have same : other = bytes := by simpa only [rootInput, input, Option.toList_some, List.mem_singleton] using member
        exact same ▸ away

/-- Selecting a fresh actual input records only its private label and preserves cache absence; rejected inputs keep the table unselected. -/
theorem selectHidden_keeps (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable)
    (unselected : table.hidden = none)
    (fresh : ∀ bytes, rootInput setup seed scalar message = some bytes → table.cache bytes = none)
    (result : Reply × HiddenTable)
    (supported : result ∈ support ((selectHidden setup.joint setup.dh seed scalar message).run table)) :
    result.2.bad = table.bad ∧ result.2.Clean ∧
      ∀ bytes, result.2.hidden = some bytes → rootInput setup seed scalar message = some bytes := by
  simp only [selectHidden, StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
  | none =>
      simp only [input, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨rfl, ?_, ?_⟩
      · intro bytes found
        simp [unselected] at found
      · intro bytes found
        simp [unselected] at found
  | some bytes =>
      have missing := fresh bytes input
      simp only [input, missing, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      refine ⟨rfl, ?_, ?_⟩
      · intro other found
        have same : bytes = other := Option.some.inj found
        exact same ▸ missing
      · intro other found
        have same : bytes = other := Option.some.inj found
        exact same ▸ input

/-- A public query away from the selected input preserves the same omitted-entry invariant and both private flags. -/
theorem hiddenPublic_keeps (bytes : Pqxdh.Bytes) (table : HiddenTable) (clean : table.Clean)
    (away : table.hidden ≠ some bytes) (result : HmacBlock × HiddenTable)
    (supported : result ∈ support ((hiddenPublic bytes).run table)) :
    result.2.hidden = table.hidden ∧ result.2.bad = table.bad ∧ result.2.Clean := by
  simp only [hiddenPublic, StateT.run, away, ↓reduceIte, support_map, Set.mem_image] at supported
  obtain ⟨read, readSupported, rfl⟩ := supported
  refine ⟨rfl, rfl, HiddenTable.Clean.update table _ clean rfl [bytes]
    (oracle_adds bytes table.cache read readSupported) ?_⟩
  intro other member
  have same : other = bytes := List.mem_singleton.mp member
  exact same ▸ away

/-- Public queries at every other input return the real block and reconstruct the complete original cache. No public HKDF evaluation is replaced by an independent table. -/
theorem hiddenPublic_source (prk : HmacBlock) (bytes : Pqxdh.Bytes) (table : HiddenTable)
    (away : table.hidden ≠ some bytes) :
    (fun result => (result.1, result.2.fill prk)) <$> (hiddenPublic bytes).run table =
      (HmacOracle.randomOracle bytes).run (table.fill prk) := by
  simp only [hiddenPublic, StateT.run, away, ↓reduceIte, Functor.map_map]
  exact table_away_source prk table bytes away

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- A checked coupling may retain the supported complete outputs of both runs in its postcondition, without changing either marginal distribution. -/
theorem relTriple_with_support {α β : Type} (left : ProbComp α) (right : ProbComp β)
    (relation : α → β → Prop) (coupled : RelTriple left right relation) :
    RelTriple left right (fun a b => relation a b ∧ a ∈ support left ∧ b ∈ support right) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at coupled ⊢
  obtain ⟨coupling, holds⟩ := coupled
  refine ⟨coupling, fun pair member => ⟨holds pair member, ?_, ?_⟩⟩
  · rw [support_eq_evalSPMF_support, ← coupling.2.map_fst, spmf_support_map]
    exact ⟨pair, member, rfl⟩
  · rw [support_eq_evalSPMF_support, ← coupling.2.map_snd, spmf_support_map]
    exact ⟨pair, member, rfl⟩

/-- If the current operation is not designated, the prefetched interpreter executes the ordinary complete query regardless of its private flag. -/
theorem once_away {ι σ V : Type} {spec : OracleSpec ι}
    (choose : spec.Domain → σ → Bool) (lazy : QueryImpl spec (StateT σ ProbComp))
    (programmed : V → QueryImpl spec (StateT σ ProbComp)) (value : V)
    (query : spec.Domain) (state : σ × Bool) (away : choose query state.1 = false) :
    (once choose lazy programmed value query).run state = (latch choose lazy query).run state := by
  simp only [once, StateT.run, away, Bool.false_eq_true, ↓reduceIte, ite_self]

open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Source refusal carries the already proved source invariant, so it remains valid after arbitrary further adversary decisions. -/
def SourceBad (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (state : EntryState KemSK) : Prop :=
  SourceInvariant (Reader := Reader) (Response := Response) setup context state.1 ∧
    SelectedBad setup context.seed context.scalar Q j state.1.1.ghost

/-- A query coupling can defer only the operational invariant to the independently proved original source support theorem. -/
def QueryPost {α : Type} (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (left : α × EntryState KemSK) (right : α × HiddenState KemSK) : Prop :=
  (left.1 = right.1 ∧ (SourceInvariant (Reader := Reader) (Response := Response) setup context left.2.1 →
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left.2 right.2)) ∨
    (SelectedBad setup context.seed context.scalar Q j left.2.1.1.ghost ∧ right.2.1.2.2.bad = true)

/-- The deferred operational invariant is discharged using the actual complete prefetched source query, yielding the full identical-until-bad postcondition. -/
theorem close_query_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (query : ServerAuthSpec.Domain)
    (left : EntryState KemSK) (right : HiddenState KemSK)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context left.1)
    (coupled : RelTriple ((prefetchedHandler setup codec checks context Q j prk query).run left)
      ((hiddenHandler setup codec checks context Q j services query).run right)
      (QueryPost (Reader := Reader) (Response := Response) setup context Q j prk)) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk query).run left)
      ((hiddenHandler setup codec checks context Q j services query).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  apply relTriple_post_mono (relTriple_with_support _ _ _ coupled)
  intro first second post
  have kept := (prefetchedStep_invariant setup codec checks context Q j prk query left invariant first post.2.1).1
  rcases post.1 with ⟨same, next⟩ | ⟨bad, refused⟩
  · exact Or.inl ⟨same, next kept⟩
  · exact Or.inr ⟨⟨kept, bad⟩, refused⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointIdentity PqxdhJointGapDh

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- A hidden honest derive reply identifies the exact input in the retained table, without any injectivity property of output bytes. -/
theorem hiddenDerive_hidden (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable) (result : Reply × HiddenTable)
    (supported : result ∈ support ((hiddenDerive setup.hmac setup.joint setup.dh seed scalar message).run table))
    (hidden : result.1.isHidden = true) :
    ∃ bytes, result.2.hidden = some bytes ∧ rootInput setup seed scalar message = some bytes := by
  simp only [hiddenDerive, StateT.run] at supported
  cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar message with
  | none =>
      simp only [input, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases hidden
  | some bytes =>
      simp only [input] at supported
      split at supported
      · rename_i selected
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨bytes, selected, input⟩
      · simp only [ordinaryHiddenDerive, StateT.run, realDerive, input, support_map, Set.mem_image] at supported
        obtain ⟨_, ⟨read, _, rfl⟩, rfl⟩ := supported
        cases hidden

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.initial
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eraseGhost_touch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eraseGhost_touch
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eraseGhost_seals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eraseGhost_seals
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eraseGhost_accept' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eraseGhost_accept
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.entry
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.touch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.touch
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.derive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.derive
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.context
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.build
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.ProtocolRel.finish
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenHandler_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenHandler_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenHandler_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenHandler_good
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.designated_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.designated_related
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.initial
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.HiddenTable.Clean.update' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.HiddenTable.Clean.update
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenDerive_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenDerive_keeps
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectHidden_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.selectHidden_keeps
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenPublic_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenPublic_keeps
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenPublic_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenPublic_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_with_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.relTriple_with_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.once_away' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.once_away
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.close_query_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.close_query_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenDerive_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hiddenDerive_hidden
