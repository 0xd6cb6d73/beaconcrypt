import BeaconcryptCore.Computational.PqxdhServerAuthEntryState

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Adversary coin queries preserve every related protocol/table field and return the identical sampled values. -/
theorem coin_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (coin : Nat) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inl coin)).run left)
      ((hiddenHandler setup codec checks context Q j services (.inl coin)).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  rw [hiddenHandler_good setup codec checks context Q j services (.inl coin) right related.good]
  simp only [prefetchedHandler, once, StateT.run, designated, hiddenDesignated,
    Bool.false_eq_true, ↓reduceIte, ite_self, latch, skeleton, Functor.map_map, Bool.or_false]
  exact relTriple_map_same _ _ _ _ (fun _ _ => Or.inl ⟨rfl, related⟩)

/-- Post-registration Server kernel reveals return the exact same native state; marked pending tokens remain outside this source interface. -/
theorem reveal_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (keyId : Aeneas.Std.U64)
    (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.reveal keyId))).run left)
      ((hiddenHandler setup codec checks context Q j services (.inr (.reveal keyId))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  rw [hiddenHandler_good setup codec checks context Q j services (.inr (.reveal keyId)) right related.good]
  simp only [prefetchedHandler, once, StateT.run, designated, hiddenDesignated,
    Bool.false_eq_true, ↓reduceIte, ite_self, latch, skeleton, map_pure, Bool.or_false]
  apply relTriple_pure_pure
  refine Or.inl ⟨?_, related⟩
  simp only [revealKernel, related.protocol.server]

/-- Installing the same actual CTX-cache reply preserves all omitted-entry metadata, given the independently proved source operational invariant. -/
theorem EntryRel.context (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      ({ left.1.1 with ctx := cache }, left.1.2)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      (({ left.1.1 with ctx := cache }, left.1.2), left.2)
      (({ right.1.1 with ctx := cache }, right.1.2), right.2) :=
  ⟨invariant, ProtocolRel.context _ _ _ _ related.protocol cache, related.cache, related.flag,
    related.unselected, related.selected, related.below, related.marked, related.good, related.clean⟩

/-- Public CTX hash queries preserve the common random-oracle cache and the complete selected-entry relation. -/
theorem hash_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (bytes : Pqxdh.Bytes)
    (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.hash bytes))).run left)
      ((hiddenHandler setup codec checks context Q j services (.inr (.hash bytes))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  apply close_query_coupling setup codec checks context Q j prk services (.inr (.hash bytes)) left right related.source
  rw [hiddenHandler_good setup codec checks context Q j services (.inr (.hash bytes)) right related.good]
  simp only [prefetchedHandler, once, StateT.run, designated, hiddenDesignated,
    Bool.false_eq_true, ↓reduceIte, ite_self, latch, skeleton, hashStep, map_bind, map_pure, Bool.or_false]
  rw [related.protocol.ctx]
  simp only [bind_pure_comp]
  exact relTriple_map_same _ _ _ _ (fun read _ => Or.inl ⟨rfl, fun invariant =>
    EntryRel.context setup context Q j prk left right related read.2 invariant⟩)

/-- Public HMAC evaluations outside the approved zero-salt 192-byte Extract domain remain literal real evaluations in both complete runs. -/
theorem hmac_outside_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (key : HmacBlock) (message : Pqxdh.Bytes)
    (outside : ¬ (key = zeroSalt ∧ message.length = 192))
    (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.hmac key message))).run left)
      ((hiddenHandler setup codec checks context Q j services (.inr (.hmac key message))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  rw [hiddenHandler_good setup codec checks context Q j services (.inr (.hmac key message)) right related.good]
  simp only [prefetchedHandler, once, StateT.run, designated, hiddenDesignated,
    Bool.false_eq_true, ↓reduceIte, ite_self, latch, skeleton, hmacStep, outside, map_pure, Bool.or_false]
  exact relTriple_pure_pure (Or.inl ⟨rfl, related⟩)

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The literal ghost update made by an actual public Extract-table query. -/
def publicTouched (state : GameState KemSK) (message : Pqxdh.Bytes) : GameState KemSK :=
  { state with ghost := { state.ghost with touches := state.ghost.touches ++ [.adversary message] } }

/-- A public read away from the selected entry retains every relation clause, including literal marked-session provenance and the source touch that was just appended. -/
theorem EntryRel.publicTable (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (message : Pqxdh.Bytes) (next : HiddenTable)
    (hidden : next.hidden = right.1.2.2.hidden) (bad : next.bad = right.1.2.2.bad) (clean : next.Clean)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      (publicTouched left.1.1 message, left.1.2.1, next.fill prk)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      ((publicTouched left.1.1 message, left.1.2.1, next.fill prk), left.2)
      ((publicTouched right.1.1 message, right.1.2.1, next), right.2) := by
  refine ⟨invariant, ProtocolRel.touch _ _ _ _ related.protocol _ _ rfl, rfl, related.flag,
    (fun flag => hidden.trans (related.unselected flag)), ?_, related.below, ?_, bad.trans related.good, clean⟩
  · intro bytes found
    exact selectedAt_prefix setup context.seed context.scalar Q j left.1.1.ghost _ bytes ⟨_, rfl⟩
      (related.selected bytes (hidden ▸ found))
  · intro index marked
    obtain ⟨message', reply, bytes, touched, selected, rooted⟩ := related.marked index marked
    exact ⟨message', reply, bytes, List.mem_append_left _ touched, hidden.trans selected, rooted⟩

/-- An actual public Extract query is coupled through the retained real table, or both complete runs enter the refusal branch at the omitted input. -/
theorem hmac_inside_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (table : services.table = hiddenPublic)
    (key : HmacBlock) (message : Pqxdh.Bytes) (inside : key = zeroSalt ∧ message.length = 192)
    (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.hmac key message))).run left)
      ((hiddenHandler setup codec checks context Q j services (.inr (.hmac key message))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  apply close_query_coupling setup codec checks context Q j prk services (.inr (.hmac key message)) left right related.source
  rw [hiddenHandler_good setup codec checks context Q j services (.inr (.hmac key message)) right related.good]
  simp only [prefetchedHandler, once, StateT.run, designated, hiddenDesignated,
    Bool.false_eq_true, ↓reduceIte, ite_self, latch, skeleton, hmacStep, inside, realServices,
    Bool.or_false]
  rw [table, related.cache]
  simp only [and_self, ↓reduceIte, map_bind, map_pure]
  by_cases away : right.1.2.2.hidden ≠ some message
  · have reconstructed := hiddenPublic_source prk message right.1.2.2 away
    simp only [StateT.run] at reconstructed
    rw [← reconstructed]
    simp only [bind_pure_comp, Functor.map_map]
    apply relTriple_map_same
    intro read supported
    have kept := hiddenPublic_keeps message right.1.2.2 related.clean away read supported
    exact Or.inl ⟨rfl, fun invariant => EntryRel.publicTable setup context Q j prk left right related
      message read.2 kept.1 kept.2.1 kept.2.2 invariant⟩
  · have selected : right.1.2.2.hidden = some message := not_ne_iff.mp away
    have hit : right.1.2.2.fill prk message = some prk := by
      simp only [HiddenTable.fill, selected, QueryCache.cacheQuery_self]
    have read := randomOracle.run_eq message (right.1.2.2.fill prk)
    simp only [StateT.run, hit] at read
    rw [read]
    simp only [hiddenPublic, selected, ↓reduceIte, pure_bind]
    apply relTriple_pure_pure
    refine Or.inr ⟨?_, rfl⟩
    exact ⟨message, selectedAt_prefix setup context.seed context.scalar Q j left.1.1.ghost _ message
      ⟨_, rfl⟩ (related.selected message selected), Or.inr (List.mem_append_right _ (List.mem_singleton_self _))⟩

/-- Every public HMAC query uses either the unchanged real evaluation or the checked omitted-entry table coupling. -/
theorem hmac_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (services : Services Response HiddenTable) (table : services.table = hiddenPublic)
    (key : HmacBlock) (message : Pqxdh.Bytes) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.hmac key message))).run left)
      ((hiddenHandler setup codec checks context Q j services (.inr (.hmac key message))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  by_cases inside : key = zeroSalt ∧ message.length = 192
  · exact hmac_inside_step_coupling setup codec checks context Q j prk services table key message inside left right related
  · exact hmac_outside_step_coupling setup codec checks context Q j prk services key message inside left right related

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Actual build settlement consumes the same pending handle and retains the exact seal trailer and cache; all omitted-table provenance is unchanged. -/
theorem EntryRel.build (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (session : Nat)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response × ServerState) × SealState)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      ((afterBuild session left.1.1 result).2, left.1.2)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      (((afterBuild session left.1.1 result).2, left.1.2), left.2)
      (((afterBuild session right.1.1 result).2, right.1.2), right.2) := by
  exact ⟨invariant, (ProtocolRel.build _ _ _ _ related.protocol session result).2,
    related.cache, related.flag, related.unselected, related.selected, related.below,
    related.marked, related.good, related.clean⟩

/-- The complete source build query uses the actual selected root only in the mathematical continuation, preserving the original optional response, native state and common cache. -/
theorem build_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (session : Nat) (payload : Option Pqxdh.Bytes) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.build session payload))).run left)
      ((hiddenHandler setup codec checks context Q j
        (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))
        (.inr (.build session payload))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  apply close_query_coupling setup codec checks context Q j prk _ (.inr (.build session payload)) left right related.source
  rw [hiddenHandler_good setup codec checks context Q j _ (.inr (.build session payload)) right related.good]
  simp only [prefetchedHandler, once, StateT.run, designated, hiddenDesignated,
    Bool.false_eq_true, ↓reduceIte, ite_self, latch, skeleton, buildStep]
  rw [related.source.2.1, related.protocol.pending session]
  cases pending : right.1.1.pending session with
  | none =>
      simp only [Option.map_none, map_pure, Bool.or_false]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, fun _ => related⟩
  | some token =>
      simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, Bool.or_false,
        related.protocol.server, related.protocol.ctx]
      cases marked : right.1.2.1 session <;>
        simp only [restoreToken, Bool.false_eq_true, ↓reduceIte, sourceHiddenServices,
          bind_pure_comp, Functor.map_map]
      all_goals
        apply relTriple_map_same
        intro result _
        exact Or.inl ⟨(ProtocolRel.build _ _ _ _ related.protocol session result).1,
          fun invariant => EntryRel.build setup context Q j prk left right related session result invariant⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.coin_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.coin_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.reveal_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.reveal_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.context
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hash_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hash_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_outside_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_outside_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.publicTable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.publicTable
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_inside_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_inside_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hmac_step_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.build
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.build_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.build_step_coupling
