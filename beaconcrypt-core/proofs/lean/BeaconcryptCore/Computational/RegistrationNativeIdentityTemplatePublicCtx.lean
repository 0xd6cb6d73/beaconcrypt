-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateFirstOmitted
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperationalPrefix

/-! Public hash prefixes populate exactly the public side of the executable template table, retaining the entire warm cache, chronological journal and true draw costs. No selected signature or private address is an installation argument. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx
open RegistrationNativeIdentityReindexedCtx (ByteCache Cache State unitCache)
open RegistrationNativeIdentityTemplateAddress (Key)
open RegistrationNativeIdentitySymbolicRom (cached counted)
variable {Value : Type}

def publicCache (cache : ByteCache) : Cache Key :=
  (RegistrationNativeIdentityTemplateCtx.install cache []).1

def install (before : RegistrationNativePlatformCtxBackend.State) : State Key :=
  RegistrationNativeIdentityTemplateCtx.install (RegistrationNativeIdentityTemplateFirstOmitted.byteCache before.1) before.2

private theorem update (cache : ByteCache) (input : Pqxdh.Bytes) (digest : CtxRomAuth.CtxDigest) :
    publicCache (cache.cacheQuery input digest) = (publicCache cache).cacheQuery (.inl input) digest := by
  apply QueryCache.ext
  intro key
  cases key with
  | inl bytes =>
    change Function.update cache input (some digest) bytes = Function.update (publicCache cache) (.inl input) (some digest) (.inl bytes)
    by_cases same : bytes = input
    · subst bytes
      simp only [Function.update_self]
    · rw [Function.update_of_ne same, Function.update_of_ne (fun equal => same (Sum.inl.inj equal))]
      rfl
  | inr frame =>
    change none = Function.update (publicCache cache) (.inl input) (some digest) (.inr frame)
    rw [Function.update_of_ne (by intro equal; cases equal)]
    rfl

private theorem cached_source (input : Pqxdh.Bytes) (cache : ByteCache) :
    Prod.map id publicCache <$> (cached RegistrationNativeIdentityReindexedCtx.sampler input).run cache =
      (cached RegistrationNativeIdentityReindexedCtx.sampler (Sum.inl input : Key)).run (publicCache cache) := by
  have lookup : publicCache cache (.inl input) = cache input := rfl
  unfold cached
  cases found : cache input with
  | none =>
    rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ (lookup.trans found)]
    simp only [Functor.map_map, Prod.map_def, id_eq]
    congr 1
    funext digest
    rw [update]
  | some digest =>
    rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ (lookup.trans found), map_pure]
    rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem counted_source (input : Pqxdh.Bytes) (cache : ByteCache) :
    Prod.map id publicCache <$> (counted RegistrationNativeIdentityReindexedCtx.sampler input).run cache =
      (counted RegistrationNativeIdentityReindexedCtx.sampler (Sum.inl input : Key)).run (publicCache cache) := by
  have interpreted := congrArg (fun work => (simulateQ PqxdhRecordLiftWorld.countCoin work).run 0) (cached_source input cache)
  have observed := congrArg (fun distribution => (fun result => ((result.1.1, result.2), result.1.2)) <$> distribution) interpreted
  simpa only [counted, StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq] using observed

private theorem byte_query (input : Pqxdh.Bytes) (before : State Pqxdh.Bytes) :
    Prod.map id (fun current => RegistrationNativeIdentityTemplateCtx.install current.1 current.2) <$>
      (RegistrationNativeIdentityReindexedCtx.implementation input).run before =
      (RegistrationNativeIdentityReindexedCtx.implementation (Sum.inl input : Key)).run
        (RegistrationNativeIdentityTemplateCtx.install before.1 before.2) := by
  have law := congrArg (fun distribution => (fun result => (result.1,
    (result.2, before.2.map (fun bytes => (Sum.inl bytes : Key)) ++ [Sum.inl input]))) <$> distribution) (counted_source input before.1)
  simpa only [RegistrationNativeIdentityReindexedCtx.implementation, StateT.run, Functor.map_map,
    Prod.map_def, id_eq, RegistrationNativeIdentityTemplateCtx.install, publicCache,
    List.map_append, List.map_cons, List.map_nil] using law

private theorem install_realize (before : State Pqxdh.Bytes) :
    install (RegistrationNativeIdentityReindexedCtx.realize id id before) =
      RegistrationNativeIdentityTemplateCtx.install before.1 before.2 := by
  change RegistrationNativeIdentityTemplateCtx.install
    (RegistrationNativeIdentityTemplateFirstOmitted.byteCache (unitCache before.1)) (before.2.map id) = _
  rw [List.map_id]
  rfl

private theorem restore (before : RegistrationNativePlatformCtxBackend.State) :
    RegistrationNativeIdentityReindexedCtx.realize id id
      (RegistrationNativeIdentityTemplateFirstOmitted.byteCache before.1, before.2) = before := by
  have cache : unitCache (RegistrationNativeIdentityTemplateFirstOmitted.byteCache before.1) = before.1 := by
    apply QueryCache.ext
    rintro ⟨tag, input⟩
    cases tag
    rfl
  change (unitCache (RegistrationNativeIdentityTemplateFirstOmitted.byteCache before.1), before.2.map id) = _
  rw [cache, List.map_id]

/-- A literal public physical hash updates exactly the public symbolic key, with identical digest, full warm cache/journal and true draw count. -/
theorem query (input : Pqxdh.Bytes) (before : RegistrationNativePlatformCtxBackend.State) :
    Prod.map id install <$> (RegistrationNativePlatformCtxBackend.physical input).run before =
      (RegistrationNativeIdentityReindexedCtx.implementation (Sum.inl input : Key)).run (install before) := by
  have physical := RegistrationNativeIdentityReindexedCtx.query id id (fun _ => rfl) input
    (RegistrationNativeIdentityTemplateFirstOmitted.byteCache before.1, before.2) rfl
  rw [restore] at physical
  have mapped := congrArg (fun distribution => Prod.map id install <$> distribution) physical
  simp only [Functor.map_map] at mapped
  have functions : (fun result : (CtxRomAuth.CtxDigest × Nat) × State Pqxdh.Bytes =>
      Prod.map id install (Prod.map id (RegistrationNativeIdentityReindexedCtx.realize id id) result)) =
      Prod.map id (fun current : State Pqxdh.Bytes => RegistrationNativeIdentityTemplateCtx.install current.1 current.2) := by
    funext result
    exact congrArg (fun state => (result.1, state)) (install_realize result.2)
  rw [functions] at mapped
  exact mapped.symm.trans (byte_query input (RegistrationNativeIdentityTemplateFirstOmitted.byteCache before.1, before.2))

/-- Arbitrary adaptive public hash prefixes reach exactly the same executable template table without receiving a selected signature or address realization. -/
theorem program (work : OracleComp RegistrationNativePlatformCtxBackend.HashSpec Value)
    (before : RegistrationNativePlatformCtxBackend.State) :
    Prod.map id install <$> (simulateQ RegistrationNativePlatformCtxBackend.physical work).run before =
      (simulateQ (fun input => RegistrationNativeIdentityReindexedCtx.implementation (Sum.inl input : Key)) work).run (install before) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ install query work before

/-- The raw physical field is represented only by the separate public-keyed table. This is still a private source-oracle state; its key rows are not executable adversary data. -/
def sourceInstall (before : RegistrationNativeIdentityCensorSource.State) : RegistrationNativeIdentityTemplateSource.State :=
  ({before with hash := (∅, [])}, install before.hash)

def PublicAllowed : RegistrationNativeIdentityCensorOperational.Spec.Domain → Prop
  | .inl (.inr described) => described.input.isSome = true
  | .inr (.template _ _ _ _) => False
  | _ => True

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem source_hash_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (described : RegistrationNativeIdentityCensorCompiler.HashInput)
    (before : RegistrationNativeIdentityTemplateSource.State) :
    (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder (.inl (.inr described))).run before =
      (RegistrationNativeIdentityTemplateSource.hash (match described.input with | some input => .inl input | none => .inl [])).run before := rfl

/-- The actual source prefix, including selectors and failed protocol operations, populates precisely the public table and retains every other private source field. -/
theorem source_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (request : RegistrationNativeIdentityCensorOperational.Spec.Domain) (allowed : PublicAllowed request)
    (before : RegistrationNativeIdentityCensorSource.State) :
    Prod.map id sourceInstall <$> (RegistrationNativeIdentityCensorSource.censored joint selected placeholder request).run before =
      (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run (sourceInstall before) := by
  rcases request with (((protocol | message) | scan) | described) | marker
  · simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, StateT.run, Functor.map_map, Prod.map_def, id_eq, sourceInstall]
  · simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.select, StateT.run, sourceInstall]
    split <;> simp only [map_pure, Prod.map_def, id_eq] <;> rfl
  · change Prod.map id sourceInstall <$> (pure ((), before) : ProbComp _) =
      (fun result => (result.1, (result.2, (sourceInstall before).2))) <$>
        (pure ((), (sourceInstall before).1) : ProbComp _)
    simp only [map_pure]
    rfl
  · cases indexed : described.input with
    | none => simp only [PublicAllowed, indexed, Option.isSome_none, Bool.false_eq_true] at allowed
    | some input =>
      rw [source_hash_run, indexed]
      have law := congrArg (fun distribution => (fun result => (result.1,
        ({before with hash := (∅, [])}, result.2))) <$> distribution) (query input before.hash)
      simpa only [RegistrationNativeIdentityTemplateSource.hash,
        RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.physical, StateT.run, indexed, Functor.map_map,
        Prod.map_def, id_eq, sourceInstall] using law
  · cases marker with
    | template handle message leading trailing => exact False.elim allowed
    | omitted handle message =>
      simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
        RegistrationNativeIdentityCensorSource.censored, bind_apply, RegistrationNativeIdentityCensorSource.omitted,
        StateT.run, map_bind, bind_map_left, pure_apply, map_pure, Prod.map_def, id_eq, sourceInstall]

/-- Every adaptive pre-template source prefix has this exact full-state public-table interpretation, including its real warm cache and all source audit entries. -/
theorem source_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec Value) (scope : work.AllQueriesSatisfy PublicAllowed)
    (before : RegistrationNativeIdentityCensorSource.State) :
    Prod.map id sourceInstall <$> (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run before =
      (simulateQ (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder) work).run (sourceInstall before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp scope
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← source_query joint selected placeholder request first before]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)

private theorem record_query_scope (request : RegistrationNativeIdentityCensorPrefix.SourceSpec.Domain)
    (mode : RegistrationNativeIdentityCensorCompiler.Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      ((RegistrationNativeIdentityCensorPrefix.record request).run mode)).AllQueriesSatisfy PublicAllowed := by
  cases request <;>
    simp only [RegistrationNativeIdentityCensorPrefix.record, StateT.run, simulateQ_bind, simulateQ_pure,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed] <;>
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨by first | exact True.intro | rfl, fun _ => trivial⟩

private theorem record_scope (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec Value)
    (mode : RegistrationNativeIdentityCensorCompiler.Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      ((simulateQ RegistrationNativeIdentityCensorPrefix.record work).run mode)).AllQueriesSatisfy PublicAllowed := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind request next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind]
    exact allQueriesSatisfy_bind (record_query_scope request mode) (fun result => ih result.1 result.2)

/-- The actual unarmed source lowering has this complete public-table marginal with no supplied hash-admission or source-frame premise. The value may retain the entire current frontend and platform state. -/
theorem unarmed (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec Value) (mode : RegistrationNativeIdentityCensorCompiler.Mode)
    (prior : RegistrationNativeIdentityCensorPrefix.Unarmed mode) (before : RegistrationNativeIdentityCensorSource.State) :
    Prod.map id sourceInstall <$> (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before =
      (simulateQ (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run (sourceInstall before) := by
  rw [RegistrationNativeIdentityCensorOperationalPrefix.program selected placeholder work mode prior]
  exact source_program joint selected placeholder _ (record_scope work mode) before

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.source_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.source_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.unarmed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx.unarmed
