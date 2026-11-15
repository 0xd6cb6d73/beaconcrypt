-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence
import BeaconcryptCore.Computational.PqxdhEnvironmentForward

/-! Support-only refinement of environment hash replies by a cache reached in the same actual CTX execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects
open PqxdhRecordLiftInterface (EnvEffects Capability)
open PqxdhRecordLiftProtocol (Control)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open CtxRomAuth
variable {n : Nat}

/-- Only hash replies carry an additional cache receipt. -/
abbrev Restricted (cache : CtxRO.QueryCache) (n : Nat) : OracleSpec (EnvEffects n).Domain
  | .inr (.hash bytes) => { digest : CtxDigest // cache ((), bytes) = some digest }
  | query => (EnvEffects n).Range query

/-- The original reply of every restricted query. -/
def reply (cache : CtxRO.QueryCache) : (query : (EnvEffects n).Domain) →
    (Restricted cache n).Range query → (EnvEffects n).Range query
  | .inr (.hash _), digest => digest.val
  | .inl _, value => value
  | .inr (.peerPresent _), value => value
  | .inr (.ownerPresent _), value => value
  | .inr (.appendOwner _ _ _), value => value
  | .inr (.advanceOwner _ _), value => value
  | .inr (.installServer _ _ _), value => value
  | .inr (.installBeacon _ _ _), value => value

/-- Forward every effect at its original address and project its reply. -/
def project (cache : CtxRO.QueryCache) : QueryImpl (EnvEffects n) (OracleComp (Restricted cache n)) :=
  fun query => reply cache query <$> ((Restricted cache n).query query)

/-- The original environment program with only its hash reply range restricted. -/
def restricted (cache : CtxRO.QueryCache) {X : Type} (work : OracleComp (EnvEffects n) X) :
    OracleComp (Restricted cache n) X := simulateQ (project cache) work

/-- The cache condition on an original reply. -/
def Fits (cache : CtxRO.QueryCache) : (query : (EnvEffects n).Domain) → (EnvEffects n).Range query → Prop
  | .inr (.hash bytes), digest => cache ((), bytes) = some digest
  | _, _ => True

/-- Later caches retain every admissible reply of an earlier cache. -/
theorem fits_mono {before after : CtxRO.QueryCache} (grows : before ≤ after)
    (query : (EnvEffects n).Domain) (value : (EnvEffects n).Range query) (fits : Fits before query value) :
    Fits after query value := by
  rcases query with coin | request
  · trivial
  · cases request <;> first | trivial | exact grows fits

/-- The refinement admits precisely the original replies consistent with the chosen cache. -/
theorem project_support (cache : CtxRO.QueryCache) (query : (EnvEffects n).Domain)
    (value : (EnvEffects n).Range query) : value ∈ support (project cache query) ↔ Fits cache query value := by
  rcases query with coin | request
  · simp [project, reply, Fits]
  · cases request <;> simp [project, reply, Fits]

section Generic
variable {S X : Type}

/-- An actual supported execution can be replayed in the restricted reply tree at any extension of its final cache. This is a support statement, with no distributional substitution. -/
theorem restricted_support (handler : QueryImpl (EnvEffects n) (StateT S ProbComp))
    (cacheOf : S → CtxRO.QueryCache)
    (grows : ∀ query before result, result ∈ support ((handler query).run before) →
      cacheOf before ≤ cacheOf result.2)
    (cached : ∀ query before result, result ∈ support ((handler query).run before) →
      Fits (cacheOf result.2) query result.1)
    (work : OracleComp (EnvEffects n) X) (before : S) (result : X × S)
    (supported : result ∈ support ((simulateQ handler work).run before)) (cache : CtxRO.QueryCache)
    (extended : cacheOf result.2 ≤ cache) : result.1 ∈ support (restricted cache work) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      simp [restricted]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, final⟩ := supported
      have later : cacheOf middle.2 ≤ cacheOf result.2 :=
        PqxdhRecordLiftFlat.support_keep_oracle handler (fun state => cacheOf middle.2 ≤ cacheOf state)
          (fun request state held output member => held.trans (grows request state output member))
          (next middle.1) middle.2 le_rfl result final
      have allowed := fits_mono (later.trans extended) query middle.1 (cached query before middle first)
      simp only [restricted, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
      exact ⟨middle.1, (project_support cache query middle.1).mpr allowed,
        ih middle.1 middle.2 final⟩

/-- A zero bad-query bound on the restricted tree preserves the complete actual handler-state invariant along every supported execution. -/
theorem keep_restricted (handler : QueryImpl (EnvEffects n) (StateT S ProbComp))
    (cacheOf : S → CtxRO.QueryCache)
    (grows : ∀ query before result, result ∈ support ((handler query).run before) → cacheOf before ≤ cacheOf result.2)
    (cached : ∀ query before result, result ∈ support ((handler query).run before) → Fits (cacheOf result.2) query result.1)
    (bad : (EnvEffects n).Domain → Prop) [DecidablePred bad] (inv : S → Prop)
    (keep : ∀ query before, ¬ bad query → inv before → ∀ result ∈ support ((handler query).run before), inv result.2)
    (work : OracleComp (EnvEffects n) X) (cache : CtxRO.QueryCache)
    (bounded : (restricted cache work).IsQueryBoundP bad 0) (before : S) (held : inv before) (result : X × S)
    (supported : result ∈ support ((simulateQ handler work).run before)) (extended : cacheOf result.2 ≤ cache) :
    inv result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact supported ▸ held
  | query_bind query next ih =>
      simp only [restricted, simulateQ_bind, simulateQ_spec_query, project, bind_map_left] at bounded
      rw [isQueryBoundP_query_bind_iff] at bounded
      have queryQuiet : ¬ bad query := bounded.1.resolve_right (lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, final⟩ := supported
      have later : cacheOf middle.2 ≤ cacheOf result.2 :=
        PqxdhRecordLiftFlat.support_keep_oracle handler (fun state => cacheOf middle.2 ≤ cacheOf state)
          (fun request state previous output member => previous.trans (grows request state output member))
          (next middle.1) middle.2 le_rfl result final
      have allowed := (project_support cache query middle.1).mpr
        (fits_mono (later.trans extended) query middle.1 (cached query before middle first))
      rw [project, support_map] at allowed
      obtain ⟨refined, _, same⟩ := allowed
      have tailBound := bounded.2 refined
      simp only [queryQuiet, ite_false] at tailBound
      rw [same] at tailBound
      exact ih middle.1 tailBound middle.2 (keep query before queryQuiet held middle first) final

end Generic

section Replay
open PqxdhRecordLiftInterface (CapabilitySpec effectKind EffectKind)
open PqxdhDeploymentEnvironment (ctxEffects)

/-- A nonadministrative effect admitted by the restricted tree can be replayed against the same cache without changing it. -/
theorem replay_query (cache : CtxRO.QueryCache)
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRO.QueryCache ProbComp))
    (query : (EnvEffects n).Domain) (value : (EnvEffects n).Range query)
    (quiet : effectKind query ≠ .administrative) (supported : value ∈ support (project cache query)) :
    (value, cache) ∈ support ((ctxEffects admin query).run cache) := by
  have fitted := (project_support cache query value).mp supported
  rcases query with coin | request
  · simp [ctxEffects, StateT.run_lift]
  · cases request <;> simp [effectKind] at quiet
    rename_i bytes
    change cache ((), bytes) = some value at fitted
    change (value, cache) ∈ support ((uniformSampleImpl.withCaching ((), bytes)).run cache)
    rw [QueryImpl.withCaching_run_some _ fitted]
    simp

/-- A supported nonadministrative restricted source continuation replays against the fixed cache, with the exact same result and unchanged cache. -/
theorem replay_noAdmin {X : Type} (cache : CtxRO.QueryCache)
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRO.QueryCache ProbComp))
    (work : OracleComp (EnvEffects n) X)
    (quiet : work.IsQueryBoundP (fun query => effectKind query = .administrative) 0)
    (value : X) (supported : value ∈ support (restricted cache work)) :
    (value, cache) ∈ support ((simulateQ (ctxEffects admin) work).run cache) := by
  induction work using OracleComp.inductionOn with
  | pure original =>
      simpa only [restricted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, and_true] using supported
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have queryQuiet : effectKind query ≠ .administrative := quiet.1.resolve_right (lt_irrefl 0)
      simp only [restricted, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨answer, first, final⟩ := supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      refine ⟨(answer, cache), replay_query cache admin query answer queryQuiet first, ?_⟩
      exact ih answer (by simpa only [queryQuiet, ite_false] using quiet.2 answer) final

end Replay

section Actual
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)

/-- Interpret the literal environment effects on the actual control and CTX private state. -/
noncomputable def actual (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (EnvEffects n) (StateT (Control n × CtxPrivate n) ProbComp) := fun query state =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec)
      ((PqxdhRecordLiftProtocol.effects query).run state.1)).run state.2


/-- Flattening the two actual state layers preserves the full returned control and private state exactly. -/
theorem actual_run {X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (work : OracleComp (EnvEffects n) X)
    (control : Control n) (secret : CtxPrivate n) :
    (simulateQ (actual modes replace setup codec) work).run (control, secret) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec)
          ((simulateQ PqxdhRecordLiftProtocol.effects work).run control)).run secret := by
  have implementation : actual modes replace setup codec =
      ((PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec).mapStateTBase
        PqxdhRecordLiftProtocol.effects).flattenStateT := rfl
  rw [implementation, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change _ = id <$> _
  exact (id_map _).symm

/-- Actual effects preserve all earlier public hash receipts. -/
theorem actual_grows (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (EnvEffects n).Domain) (before : Control n × CtxPrivate n)
    (result : (EnvEffects n).Range query × (Control n × CtxPrivate n))
    (supported : result ∈ support ((actual modes replace setup codec query).run before)) :
    before.2.base.primitive.2 ≤ result.2.2.base.primitive.2 := by
  simp only [actual, StateT.run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact PqxdhRecordFactsBindingEvidence.program_cache_grows modes replace setup codec _ before.2 inner member

/-- A public hash effect returns a digest retained in the actual final shared cache. -/
theorem actual_hash_cached (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (bytes : Pqxdh.Bytes)
    (before : Control n × CtxPrivate n) (result : CtxDigest × (Control n × CtxPrivate n))
    (supported : result ∈ support ((actual modes replace setup codec (.inr (.hash bytes))).run before)) :
    result.2.2.base.primitive.2 ((), bytes) = some result.1 := by
  simp only [actual, StateT.run, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  change inner ∈ support ((simulateQ (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec)
    ((PqxdhRecordLiftProtocol.effects (.inr (.hash bytes))).run before.1)).run before.2) at member
  simp only [PqxdhRecordLiftProtocol.effects, PqxdhRecordLiftProtocol.capability,
    StateT.run_bind, StateT.run_lift, simulateQ_bind, simulateQ_map, StateT.run_map, simulateQ_spec_query,
    PqxdhRecordLiftIdeal.ctxInterpreter,
    PqxdhRecordLiftProtocol.interpreter, bind_pure_comp] at member
  simp only [PqxdhRecordLiftIdeal.onBase, StateT.run, map_pure, pure_bind, Functor.map_map,
    PqxdhRecordLiftProtocol.sampled, bind_pure_comp, support_map] at member
  obtain ⟨counted, reached, rfl⟩ := member
  exact PqxdhRecordFactsBindingEvidence.hash_cached ((), bytes) before.2.base.primitive.2 counted.1
    (PqxdhRecordLiftFlat.support_run_fst PqxdhRecordLiftWorld.countCoin _
      before.2.base.primitive.1.uniform counted reached)

/-- Every actual query reply is admissible at the cache of the same returned state. -/
theorem actual_fits (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (EnvEffects n).Domain) (before : Control n × CtxPrivate n)
    (result : (EnvEffects n).Range query × (Control n × CtxPrivate n))
    (supported : result ∈ support ((actual modes replace setup codec query).run before)) :
    Fits result.2.2.base.primitive.2 query result.1 := by
  rcases query with coin | request
  · trivial
  · cases request <;> first | trivial | exact actual_hash_cached modes replace setup codec _ before result supported

/-- Restricting hash replies to an extension of the actual final cache retains every supported environment result, with no assumption on the source program's hash replies. -/
theorem actual_support {X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (work : OracleComp (EnvEffects n) X)
    (before : Control n × CtxPrivate n) (result : X × (Control n × CtxPrivate n))
    (supported : result ∈ support ((simulateQ (actual modes replace setup codec) work).run before))
    (cache : CtxRO.QueryCache) (extended : result.2.2.base.primitive.2 ≤ cache) :
    result.1 ∈ support (restricted cache work) :=
  restricted_support (actual modes replace setup codec) (fun state => state.2.base.primitive.2)
    (actual_grows modes replace setup codec) (actual_fits modes replace setup codec) work before result supported cache extended

/-- A zero bad-query bound on the refined source tree preserves a complete actual CTX invariant whenever its admitted original steps preserve it. -/
theorem actual_keep {X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (bad : (EnvEffects n).Domain → Prop) [DecidablePred bad] (inv : Control n × CtxPrivate n → Prop)
    (keep : ∀ query before, ¬ bad query → inv before →
      ∀ result ∈ support ((actual modes replace setup codec query).run before), inv result.2)
    (work : OracleComp (EnvEffects n) X) (cache : CtxRO.QueryCache)
    (bounded : (restricted cache work).IsQueryBoundP bad 0)
    (before : Control n × CtxPrivate n) (held : inv before) (result : X × (Control n × CtxPrivate n))
    (supported : result ∈ support ((simulateQ (actual modes replace setup codec) work).run before))
    (extended : result.2.2.base.primitive.2 ≤ cache) : inv result.2 :=
  keep_restricted (actual modes replace setup codec) (fun state => state.2.base.primitive.2)
    (actual_grows modes replace setup codec) (actual_fits modes replace setup codec) bad inv keep work cache
    bounded before held result supported extended

end Actual
end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.fits_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.fits_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.project_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.project_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.restricted_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.restricted_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.keep_restricted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.keep_restricted

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.replay_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.replay_query

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.replay_noAdmin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.replay_noAdmin

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_hash_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_hash_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEffects.actual_keep
