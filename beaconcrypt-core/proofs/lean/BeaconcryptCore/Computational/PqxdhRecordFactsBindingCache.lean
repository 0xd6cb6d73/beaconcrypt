-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvidence
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheWorld

/-! Commitment witnesses in actual erased-world private suffix caches. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay
open PqxdhRecordFactsBindingEvidence
open PqxdhRecordFactsPrivateCache
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Exact decoded payload equality fixes the complete commitment digest. -/
theorem matches_commit (frame : RawCtxReceive.DecodedFrame) (first second : CtxSuccessfulSeal)
    (left : Matches frame first) (right : Matches frame second) :
    first.record.commit = second.record.commit := by
  have decoded := congrArg Pqxdh.decodeRecord (left.2.2.symm.trans right.2.2)
  simp only [decodeRecord_romRecord, Option.some.injEq] at decoded
  exact List.Vector.toList_injective (congrArg Pqxdh.RecordCipher.commit decoded)

/-- A matching hidden seal and a caller-known commitment witness identify one actual shared digest equality. -/
theorem matches_shared (frame : RawCtxReceive.DecodedFrame) (entry : CtxSuccessfulSeal)
    (matching : Matches frame entry) (cache : CtxRO.QueryCache) (shared : SharedCommit frame cache) :
    ∃ bytes, cache ((), bytes) = some entry.record.commit := by
  obtain ⟨record, digest, bytes, decoded, commitment, cached⟩ := shared
  rw [matching.2.2, decodeRecord_romRecord, Option.some.injEq] at decoded
  refine ⟨bytes, ?_⟩
  exact (List.Vector.toList_injective ((congrArg Pqxdh.RecordCipher.commit decoded).trans commitment)).symm ▸ cached

/-- Every successful local seal is represented at its literal private commitment input. -/
def SealsCached (keyState : KeyEntry) : Prop :=
  ∀ entry ∈ keyState.1.successfulSeals,
    keyState.2 (outerSuffix entry.input.nonce entry.input.context entry.record.tag) = some entry.record.commit

/-- All coordinates retain their actual seal commitments in their respective suffix dictionaries. -/
def AllCached (state : CtxPrivate n) : Prop := ∀ label, SealsCached (state.keys label)

/-- Actual lazy suffix lookup retains every old answer and caches the returned digest at its exact input. -/
theorem private_lookup_cached (suffix : Pqxdh.Bytes) (before : CtxSuffixRO.QueryCache)
    (result : CtxDigest × CtxSuffixRO.QueryCache)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.privateLookup suffix before)) :
    before ≤ result.2 ∧ result.2 suffix = some result.1 := by
  rw [privateLookup_exact] at supported
  refine ⟨QueryImpl.withCaching_cache_le _ suffix before result supported, ?_⟩
  cases old : before suffix
  case none =>
    rw [QueryImpl.withCaching_run_none _ old, support_map] at supported
    obtain ⟨digest, reached, rfl⟩ := supported
    exact QueryCache.cacheQuery_self before suffix digest
  case some digest =>
    rw [QueryImpl.withCaching_run_some _ old, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ old

/-- Private commitment access preserves existing seals and retains both old and newly queried suffix answers. -/
theorem local_private_cached (suffix : Pqxdh.Bytes) (before : KeyEntry) (result : CtxDigest × KeyEntry)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.localPrivate suffix before)) :
    before.2 ≤ result.2.2 ∧ result.2.1.successfulSeals = before.1.successfulSeals ∧
      result.2.2 suffix = some result.1 := by
  simp only [AdaptiveCtxSharedReplay.localPrivate, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have cached := private_lookup_cached suffix before.2 inner
    (OracleComp.mem_support_of_mem_support_liftComp _ _ _ reached)
  exact ⟨cached.1, rfl, cached.2⟩

/-- Retaining the seal list and extending its suffix cache preserves all commitment witnesses. -/
theorem sealsCached_of_grows (before after : KeyEntry) (valid : SealsCached before)
    (seals : after.1.successfulSeals = before.1.successfulSeals) (cache : before.2 ≤ after.2) :
    SealsCached after := fun entry member => cache (valid entry (seals ▸ member))

/-- The literal source replay seal leaves every stored commitment represented in the private suffix cache. -/
theorem replay_seal_cached (crypto : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (before : KeyEntry) (valid : SealsCached before) (result : Option CtxRomRecord × KeyEntry)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.localSeal crypto key input before)) :
    SealsCached result.2 := by
  unfold AdaptiveCtxSharedReplay.localSeal at supported
  split at supported <;> simp only [support_pure, Set.mem_singleton_iff, bind_pure_comp, support_map] at supported
  · exact supported ▸ valid
  · obtain ⟨inner, reached, rfl⟩ := supported
    have cached := local_private_cached _ before inner reached
    intro entry member
    rcases List.mem_cons.mp member with equal | old
    · subst entry; exact cached.2.2
    · exact cached.1 (valid entry (cached.2.1 ▸ old))

/-- Random-ciphertext sealing caches the commitment of the actual sampled body and tag. -/
theorem random_seal_cached (input : CtxSealInput) (before : KeyEntry) (valid : SealsCached before)
    (result : Option CtxRomRecord × KeyEntry) (supported : result ∈ support (randomSeal input before)) :
    SealsCached result.2 := by
  unfold randomSeal at supported
  split at supported <;> simp only [support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at supported
  · exact supported ▸ valid
  · obtain ⟨body, _, tag, _, inner, reached, rfl⟩ := supported
    have cached := local_private_cached _ before inner reached
    intro entry member
    rcases List.mem_cons.mp member with equal | old
    · subst entry; exact cached.2.2
    · exact cached.1 (valid entry (cached.2.1 ▸ old))

/-- Actual parsed and rejected replay openings preserve all previously cached seal commitments. -/
theorem replay_raw_cached (decode : RawDecoder) (raw : Pqxdh.Bytes) (before : KeyEntry)
    (valid : SealsCached before) (result : Option Pqxdh.Bytes × KeyEntry)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.localRaw decode raw before)) :
    SealsCached result.2 := by
  unfold AdaptiveCtxSharedReplay.localRaw at supported
  cases decoded : decode raw <;> simp only [decoded, support_pure, Set.mem_singleton_iff,
    bind_pure_comp, support_map] at supported
  · exact supported ▸ valid
  · obtain ⟨inner, reached, rfl⟩ := supported
    have cached := local_private_cached _ ({ before.1 with rawAttempts := before.1.rawAttempts + 1 }, before.2) inner reached
    exact sealsCached_of_grows before inner.2 valid cached.2.1 cached.1

/-- Every ideal one-key callback retains all dictionary commitment witnesses through its actual local state. -/
theorem key_cached (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (query : ReceiveSpec.Domain)
    (before : KeyEntry) (valid : SealsCached before) (result : ReceiveSpec.Range query × KeyEntry)
    (supported : result ∈ support ((keyImpl decode crypto key mode query).run before)) :
    SealsCached result.2 := by
  cases mode with
  | real => exact False.elim (ideal rfl)
  | replay | random =>
    rcases query with ((coin | (hash | input)) | raw)
    all_goals first
    | exact replay_seal_cached crypto key _ before valid result supported
    | exact random_seal_cached _ before valid result supported
    | exact replay_raw_cached decode _ before valid result supported
    | skip
    all_goals simp only [keyImpl, StateT.run, AdaptiveCtxSharedModes.localImpl, Bool.false_eq_true,
      ite_false, AdaptiveCtxSharedReplay.localImpl, randomImpl, bind_pure_comp, support_map] at supported
    all_goals obtain ⟨reply, reached, rfl⟩ := supported
    all_goals exact valid

/-- Installing the actual shared-hash interpreter preserves local private-cache commitment provenance. -/
theorem linked_cached (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (query : ReceiveSpec.Domain)
    (before : State) (valid : SealsCached before.1) (result : ReceiveSpec.Range query × State)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheRandom.linked decode crypto key mode query).run before)) :
    SealsCached result.2.1 := by
  simp only [PqxdhRecordFactsPrivateCacheRandom.linked, QueryImpl.flattenStateT,
    QueryImpl.mapStateTBase, StateT.run, StateT.mk, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact key_cached decode crypto key mode ideal query before.1 valid inner.1
    (PqxdhRecordLiftFlat.support_run_fst AdaptiveCtxSharedHash.hashImpl _ before.2 inner reached)

/-- Omitting only discarded raw suffix completion retains every successful seal's actual private-cache commitment. -/
theorem erased_local_cached (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (query : ReceiveSpec.Domain)
    (before : State) (valid : SealsCached before.1) (result : ReceiveSpec.Range query × State)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode query).run before)) :
    SealsCached result.2.1 := by
  cases query with
  | inl query =>
    simp only [PqxdhRecordFactsPrivateCacheRandom.erased, PqxdhRecordFactsPrivateCacheRandom.modePointed,
      StateT.run_map, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact linked_cached decode crypto key mode ideal (.inl query) before valid inner reached
  | inr raw =>
    rw [show PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inr raw) =
      Prod.fst <$> rawBase decode raw from rfl, StateT.run_map] at supported
    cases decoded : decode raw <;>
      simp only [rawBase, StateT.run, decoded, map_pure, support_pure, Set.mem_singleton_iff] at supported
    all_goals exact supported ▸ valid

/-- Every actual erased keyed request preserves the commitment-cache invariant at all coordinates. -/
theorem erased_keyed_cached (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (before : CtxPrivate n) (valid : AllCached before)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto query).run before)) :
    AllCached result.2 := by
  rw [PqxdhRecordFactsPrivateCacheFamily.erasedKeyed, StateT.run_map,
    PqxdhRecordFactsPrivateCacheFamily.keyedPointed_run] at supported
  simp only [LazyOracleDiscard.StateLens.lift, StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have localValid := erased_local_cached decode crypto (materialAt before.base.chain query.1).1
    (modes query.1) (ideal query.1) query.2
    ((PqxdhRecordFactsPrivateCacheFamily.localLens query.1).get before) (valid query.1)
    (inner.1.1, inner.2) (by
      rw [PqxdhRecordFactsPrivateCacheRandom.erased, StateT.run_map, support_map]
      exact ⟨inner, reached, rfl⟩)
  intro label
  by_cases same : label = query.1
  · simpa only [PqxdhRecordFactsPrivateCacheFamily.localLens, same, Function.update_self] using localValid
  · simpa only [PqxdhRecordFactsPrivateCacheFamily.localLens, Function.update_of_ne same] using valid label

/-- Exact internal keyed/base scheduling preserves cached seal commitments without any restriction on base-only effects. -/
theorem erased_mixed_cached (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (query : (PqxdhRecordFactsPrivateCacheServices.MixedSpec n baseSpec).Domain)
    (before : CtxPrivate n) (valid : AllCached before)
    (result : (PqxdhRecordFactsPrivateCacheServices.MixedSpec n baseSpec).Range query × CtxPrivate n)
    (supported : result ∈ support ((PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto baseImpl query).run before)) :
    AllCached result.2 := by
  cases query with
  | inl query => exact erased_keyed_cached modes ideal decode crypto query before valid result supported
  | inr query =>
    rw [PqxdhRecordFactsPrivateCacheServices.erased, StateT.run_map,
      PqxdhRecordFactsPrivateCacheServices.pointed, StateT.run_map] at supported
    simp only [onBase, StateT.run, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact valid

/-- The actual internal adaptive compiler client retains the invariant through every possible reply. -/
theorem erased_mixed_program_cached {X : Type} (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (baseImpl : QueryImpl baseSpec (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (program : OracleComp (PqxdhRecordFactsPrivateCacheServices.MixedSpec n baseSpec) X)
    (before : CtxPrivate n) (valid : AllCached before) (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto baseImpl) program).run before)) :
    AllCached result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordFactsPrivateCacheServices.erased modes decode crypto baseImpl)
    AllCached (fun query state previous output reached => erased_mixed_cached modes ideal decode crypto baseImpl query state previous output reached)
    program before valid result supported

/-- The complete erased source-service program retains every dictionary commitment at its actual private suffix address. -/
theorem erased_program_cached {X : Type} (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (program : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X)
    (before : CtxPrivate n) (valid : AllCached before) (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) program).run before)) :
    AllCached result.2 :=
  erased_mixed_program_cached modes ideal _ _ _ _ before valid result
    (by simpa only [PqxdhRecordFactsPrivateCacheWorld.erased,
      PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.simulateQ_compose] using supported)

/-- The literal source initialization has no successful seals requiring a cache witness. -/
theorem initial_cached : AllCached (PqxdhRecordFactsCounter.zeroCtx (CtxPrivate.initial (n := n))) := by
  intro label entry member
  exact False.elim (List.not_mem_nil member)

/-- The actual initialized erased protocol run supplies every hidden seal commitment's private-cache witness, under arbitrary source scheduling and adversarial replies. -/
theorem erased_run_cached {E X : Type} (modes : PqxdhRecordLiftWorldCompiler.Label n → KeyMode)
    (ideal : ∀ label, modes label ≠ .real) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary)) :
    AllCached result.2 :=
  erased_program_cached modes ideal replace setup codec _ _ initial_cached result supported

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.matches_commit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.matches_commit

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.matches_shared' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.matches_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.private_lookup_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.private_lookup_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.local_private_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.local_private_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.sealsCached_of_grows' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.sealsCached_of_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.replay_seal_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.replay_seal_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.random_seal_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.random_seal_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.replay_raw_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.replay_raw_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.key_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.key_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.linked_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.linked_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_local_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_local_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_keyed_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_keyed_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_mixed_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_mixed_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_mixed_program_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_mixed_program_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_program_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_program_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.initial_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.initial_cached

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_run_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingCache.erased_run_cached
