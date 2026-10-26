import BeaconcryptCore.Computational.RawCtxSelectedParentEntry

/-!
The selected predecessor response overrides only its exact original address in a retained prior lookup. Every other prior response remains unchanged. The concrete finite-cache view after recording that response equals the same retained-entry lookup, so previous bindings and fallback values are not reset. Both hidden requests and known predecessor retries reconstruct this same complete response without chain or address injectivity.

The uniform memo handler is an explicit comparison sampler. Its hit equation returns the original response and cache; a miss draws and records one full76 response in that cache, with a proved 76-byte query cap. No theorem here replaces publicly evaluable HKDF by this sampler or assumes that native source outputs are uniform. The actual reached chronological hybrid must derive the prior lookup and selected miss, preserve previous knowledge and prove its source/input exposure conditions. Prior lookup, cache and entry are private protocol/coupling context, not new adversary capabilities. Local lookup, conversion and KDF work remains computation. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentTable
open RawCtxSelectedParentEntry RawCtxSelectedChain
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Prior := JointKdfAddress → FullOutput

noncomputable def lookup (prior : Prior) (entry : Entry) (target : RootOutput)
    (address : JointKdfAddress) : FullOutput :=
  if address = entry.address then realize entry target else prior address

noncomputable def nativeStep (prior : Prior) (entry : Entry) (target : RootOutput)
    (chain : RatchetChain) : RatchetChain × RatchetMaterial :=
  RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
    (lookup prior entry target (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain))))

noncomputable def step (prior : Prior) (entry : Entry) (challenge : RatchetKdfResponse) :
    Slot → Slot × RatchetMaterial
  | .hidden => let decoded := RawCtxInterpretedReceive.decodeResponse challenge
      (.known decoded.1, decoded.2)
  | .known chain =>
      if RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain) = entry.address then
        (.hidden, RawCtxFreshChainCut.concreteMaterial entry.material)
      else let decoded := RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
        (prior (RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest chain))))
        (.known decoded.1, decoded.2)

/-- The exact prior stream is retained at every other address; the selected predecessor response is shared on both hidden and known aliases. -/
theorem step_table (prior : Prior) (entry : Entry) (target : RootOutput) (slot : Slot) :
    nativeStep prior entry target (interpret (RawCtxFreshChainCut.concreteChain target) slot) =
      Prod.map (interpret (RawCtxFreshChainCut.concreteChain target)) id
        (step prior entry (RawCtxKdfRequestTable.fullResponse
          (lookup prior entry target (RawCtxKdfRequestTable.address
            (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target))))) slot) := by
  cases slot <;> simp only [nativeStep, step, interpret, Prod.map, id_eq]
  split_ifs <;> simp_all [lookup, decoded_response]

/-- Specializing the prior stream to the original fixed source recovers every original complete response. -/
theorem lookup_source (source : FixedHkdfSha512NoSaltSource) (address request : JointKdfAddress) :
    lookup (productionStream source.crypto) (fromOutput address (productionStream source.crypto address))
      (PqxdhOrderedChainHybrids.nextChain (productionStream source.crypto address)) request =
      productionStream source.crypto request :=
  stream_source source address request

noncomputable def view (fallback : Prior) (cache : RawCtxKdfRequestTable.Table) : Prior :=
  fun address => (cache address).getD (fallback address)

/-- Recording the selected complete output preserves every other prior cache binding and fallback value; only its unavailable coordinate is represented separately. -/
theorem view_recorded (fallback : Prior) (cache : RawCtxKdfRequestTable.Table)
    (address request : JointKdfAddress) (output : FullOutput) :
    view fallback (cache.cacheQuery address output) request =
      lookup (view fallback cache) (fromOutput address output)
        (PqxdhOrderedChainHybrids.nextChain output) request := by
  simp only [lookup, realize_fromOutput]
  by_cases same : request = address <;> simp [view, fromOutput, same, QueryCache.cacheQuery_of_ne]
  subst request
  simp

/-- A comparison sampler only: no source-to-uniform replacement is assumed by this definition. -/
noncomputable def uniformMemo : QueryImpl JointKdfRO (StateT RawCtxKdfRequestTable.Table ProbComp) :=
  QueryImpl.withCaching (spec := JointKdfRO) (fun _ => ($ᵗ FullOutput))

/-- At an actual miss, this comparison handler draws exactly one complete response and records it in the same prior cache. -/
theorem memo_miss (cache : RawCtxKdfRequestTable.Table) (address : JointKdfAddress)
    (miss : cache address = none) :
    (uniformMemo address).run cache =
      (do let output ← $ᵗ FullOutput; pure (output, cache.cacheQuery address output)) := by
  simp [uniformMemo, miss]

/-- An actual hit returns the recorded response and whole unchanged cache, with no fresh draw. -/
theorem memo_hit (cache : RawCtxKdfRequestTable.Table) (address : JointKdfAddress) (output : FullOutput)
    (hit : cache address = some output) :
    (uniformMemo address).run cache = pure (output, cache) := by
  simp [uniformMemo, hit]

set_option maxRecDepth 4096 in
/-- Every comparison-table query pays at most the complete 76-byte miss draw; hits retain their exact zero-draw equation. -/
theorem memo_uniform_bound (cache : RawCtxKdfRequestTable.Table) (address : JointKdfAddress) :
    ((uniformMemo address).run cache).IsTotalQueryBound 76 := by
  cases found : cache address with
  | none =>
      rw [memo_miss cache address found]
      exact OracleComp.isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
        (fun output => show (pure (output, cache.cacheQuery address output) :
          ProbComp (FullOutput × RawCtxKdfRequestTable.Table)).IsTotalQueryBound 0 from trivial)
  | some output =>
      simp only [memo_hit cache address output found]
      trivial

end BeaconcryptCore.Computational.RawCtxSelectedParentTable

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentTable.step_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentTable.step_table

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentTable.lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentTable.lookup_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentTable.view_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentTable.view_recorded

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentTable.memo_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentTable.memo_miss

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentTable.memo_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentTable.memo_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentTable.memo_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentTable.memo_uniform_bound
