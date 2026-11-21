-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient

/-! The raw symbolic key domain is finite: its head has160 bytes and its word is either one32-byte literal or an atom. Completing that actual lazy table gives a stateless outer interpreter for each fixed table and real suffix-key oracle. The full client result, including protocol state, original ledger and chronological events, is retained; only the external lazy table cache is omitted. These source laws concern the raw symbolic side of the alias comparison, not a pointwise source claim about the byte-cache side. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable
open RegistrationNativeSecretWord (Word Key Cache Spec)
open RegistrationNativeSecretWordService (Combined)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhServerAuthKeySchedule (Output)
open LazyOracleDiscard (LawEq)
variable {Value : Type}
attribute [local irreducible] RegistrationNativeSuffixKeyPrf.value

private instance word_finite : Finite Word :=
  Finite.of_injective (fun word => match word with
    | .literal value => some value
    | .atom => none)
    (by intro first second equal; cases first <;> cases second <;> simp_all)

private instance key_finite : Finite Key :=
  Finite.of_injective (fun key : Key => (key.head, key.word))
    (by intro first second equal; cases first; cases second; simpa only [Prod.mk.injEq, Key.mk.injEq] using equal)

private noncomputable instance key_fintype : Fintype Key := Fintype.ofFinite _
private noncomputable instance output_fintype : Fintype Output := Fintype.ofFinite _

abbrev Table := Key → Output
private noncomputable instance table_sampleable : SampleableType Table := SampleableType.ofFintype _

noncomputable def tableSample : ProbComp Table := $ᵗ Table

def opened (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined (OracleComp Spec)
  | .inl query => Spec.query query
  | .inr head => pure (RegistrationNativeSuffixKeyPrf.value source candidate head)

noncomputable def fixed (table : Table) (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined ProbComp := RegistrationNativeG3CellEager.fixed table ∘ₛ opened source candidate

/-- Closing the raw symbolic table is the actual lazy-table interpretation of the opened combined program; the complete reached cache remains literal in this equation. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (cache : Cache) :
    (simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed source candidate) work).run cache =
      (simulateQ RegistrationNativeG3CellEager.lazy (simulateQ (opened source candidate) work)).run cache := by
  have same : RegistrationNativeG3CellEager.lazy ∘ₛ opened source candidate =
      RegistrationNativeSecretWordRecoveryCompiler.closed source candidate := by
    funext query
    cases query with
    | inl query => simp only [QueryImpl.compose, opened, simulateQ_spec_query,
        RegistrationNativeSecretWordRecoveryCompiler.closed, RegistrationNativeSecretWord.symbolic]
    | inr head => simp only [QueryImpl.compose, opened, simulateQ_pure,
        RegistrationNativeSecretWordRecoveryCompiler.closed]; rfl
  rw [← QueryImpl.simulateQ_compose, same]

/-- One complete uniform raw symbolic table retains every client outcome, with initial cached answers overlaid and the real suffix-key oracle left literal. -/
theorem cached_eager (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (cache : Cache) :
    LawEq ((simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed source candidate) work).run' cache)
      (do let table ← tableSample
          simulateQ (fixed (OracleComp.completeTable cache table) source candidate) work) := by
  have sourceEq := congrArg (Functor.map Prod.fst) (program_source source candidate work cache)
  simp only [StateT.run'_eq] at sourceEq ⊢
  rw [sourceEq]
  simpa only [RegistrationNativeG3CellEager.lazyRun, RegistrationNativeG3CellEager.fixedRun,
    StateT.run'_eq, fixed, QueryImpl.simulateQ_compose, tableSample] using
    RegistrationNativeG3CellEager.cached_eager (simulateQ (opened source candidate) work) cache

/-- The actual empty-cache raw symbolic experiment is a mixture of stateless fixed-table executions, retaining the entire client result. -/
theorem empty_eager (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) :
    LawEq ((simulateQ (RegistrationNativeSecretWordRecoveryCompiler.closed source candidate) work).run' ∅)
      (do let table ← tableSample; simulateQ (fixed table source candidate) work) := by
  simpa only [OracleComp.completeTable_empty] using cached_eager source candidate work ∅

def normalizedOpened (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined (OracleComp Spec)
  | .inl (.inl coin) => Spec.query (.inl coin)
  | .inl (.inr key) => Spec.query (.inr (RegistrationNativeSecretWord.normalize candidate key))
  | .inr head => pure (RegistrationNativeSuffixKeyPrf.value source candidate head)

noncomputable def normalizedFixed (table : Table) (source : FixedHkdfSha512NoSaltSource) (candidate : Secret) :
    QueryImpl Combined ProbComp := RegistrationNativeG3CellEager.fixed table ∘ₛ normalizedOpened source candidate

private theorem normalized_source (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (cache : Cache) :
    (simulateQ (RegistrationNativeSecretWordRecoveryBound.normalized source candidate) work).run cache =
      (simulateQ RegistrationNativeG3CellEager.lazy (simulateQ (normalizedOpened source candidate) work)).run cache := by
  have same : RegistrationNativeG3CellEager.lazy ∘ₛ normalizedOpened source candidate =
      RegistrationNativeSecretWordRecoveryBound.normalized source candidate := by
    funext query
    cases query with
    | inl query => cases query <;> simp only [QueryImpl.compose, normalizedOpened, simulateQ_spec_query,
        RegistrationNativeSecretWordRecoveryBound.normalized, RegistrationNativeSecretWord.actual, RegistrationNativeSecretWord.symbolic]
    | inr head => simp only [QueryImpl.compose, normalizedOpened, simulateQ_pure,
        RegistrationNativeSecretWordRecoveryBound.normalized]; rfl
  rw [← QueryImpl.simulateQ_compose, same]

/-- At each fixed mathematical candidate, the normalized symbolic execution also has a stateless completed-table source. The running frontend still receives no candidate. -/
theorem normalized_cached_eager (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (cache : Cache) :
    LawEq ((simulateQ (RegistrationNativeSecretWordRecoveryBound.normalized source candidate) work).run' cache)
      (do let table ← tableSample
          simulateQ (normalizedFixed (OracleComp.completeTable cache table) source candidate) work) := by
  have sourceEq := congrArg (Functor.map Prod.fst) (normalized_source source candidate work cache)
  simp only [StateT.run'_eq] at sourceEq ⊢
  rw [sourceEq]
  simpa only [RegistrationNativeG3CellEager.lazyRun, RegistrationNativeG3CellEager.fixedRun,
    StateT.run'_eq, normalizedFixed, QueryImpl.simulateQ_compose, tableSample] using
    RegistrationNativeG3CellEager.cached_eager (simulateQ (normalizedOpened source candidate) work) cache

/-- The actual stateful byte-oracle experiment has an exact mixture of stateless normalized-table executions for every fixed candidate, retaining the entire client/ledger/private/chronological result. No alias or independence premise is needed for this source equality. -/
theorem bytes_eager (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) :
    LawEq ((simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes source candidate) work).run' ∅)
      (do let table ← tableSample; simulateQ (normalizedFixed table source candidate) work) := by
  have projected := congrArg (Functor.map Prod.fst)
    (RegistrationNativeSecretWordRecoveryBound.program_source source candidate work ∅)
  have empty : RegistrationNativeSecretWordSource.byteCache candidate ∅ = ∅ := by
    apply QueryCache.ext
    intro point
    change (RegistrationNativeSecretWord.decode candidate point).bind (fun _ => none) = none
    cases RegistrationNativeSecretWord.decode candidate point <;> rfl
  rw [empty] at projected
  have values : (simulateQ (RegistrationNativeSecretWordRecoveryBound.normalized source candidate) work).run' ∅ =
      (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes source candidate) work).run' ∅ := by
    simpa only [StateT.run'_eq, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using projected
  rw [← values]
  simpa only [OracleComp.completeTable_empty] using normalized_cached_eager source candidate work ∅

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.cached_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.cached_eager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.empty_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.empty_eager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.normalized_cached_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.normalized_cached_eager
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.bytes_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasTable.bytes_eager
