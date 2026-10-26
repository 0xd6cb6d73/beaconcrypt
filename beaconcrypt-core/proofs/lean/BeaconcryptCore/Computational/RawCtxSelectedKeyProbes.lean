import BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds

/-!
Known reveal and alias candidates are probed only after the original source continuation stops. Each exact32 candidate becomes a public shared-ROM input and its answer is ignored. This retains the original stopped-result distribution while making every adaptive key hit an ordinary CTX secret-prefix event. No independence of the candidate list from earlier ciphertexts or plaintext replies is asserted.

The probes add one public hash call per candidate and no selected seal, raw opening or explicit random call. Their ROM implementation still pays its ordinary digest-sampling cost. The stopped candidate list is internal reduction state, not a new network disclosure.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedKeyProbes
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxQueryBounds

noncomputable def probes : List CtxKey → OracleComp ReceiveSpec Unit
  | [] => pure ()
  | candidate :: rest => do
      let _ ← ReceiveSpec.query (.inl (.inr (.inl ((), candidate.toList))))
      probes rest

/-- Instrument the actual stopped candidate list, after all original adaptive calls. -/
noncomputable def finish {Result : Type}
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) :
    OracleComp ReceiveSpec (Result × List CtxKey) := do
  let result ← client
  probes result.2
  pure result

/-- Stopped-result instrumentation preserves the entire original output distribution, even when candidates depend on all prior replies. -/
theorem finish_result {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) (state : CanonicalState) :
    EvalDistEq (Prod.fst <$> (simulateQ (canonicalImpl decode c key) (finish client)).run state)
      (Prod.fst <$> (simulateQ (canonicalImpl decode c key) client).run state) := by
  simp only [finish, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right _ fun result => ?_
  exact OracleComp.EvalDistEq.bind_const
    ((simulateQ (canonicalImpl decode c key) (probes result.1.2)).run result.2) (pure result.1)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual candidate is retained in the selected challenger's public-input history, including repeated candidates. -/
theorem probes_public (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (candidates : List CtxKey) (state : CanonicalState) (result : Unit × CanonicalState)
    (supported : result ∈ support ((simulateQ (canonicalImpl decode c key) (probes candidates)).run state)) :
    result.2.ctx.publicInputs = candidates.reverse.map List.Vector.toList ++ state.ctx.publicInputs := by
  induction candidates generalizing state result with
  | nil =>
    simp only [probes, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    rfl
  | cons candidate rest ih =>
    simp only [probes, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, tail⟩ := supported
    simp only [canonicalImpl, canonicalCtx, ctxAdversaryImpl, QueryImpl.add_apply_inl,
      ctxPublicOracle, StateT.run, bind_assoc, pure_bind, sealPrivateInputs] at step
    change (answer, next) ∈ support (do
      let response ← (ctxRandomOracle ((), candidate.toList)).run state.ctx.cache
      pure (response.1, (⟨state.ctx.addPublic candidate.toList response.2,
        state.rawAttempts, state.privateInputs⟩ : CanonicalState))) at step
    rw [mem_support_bind_iff] at step
    obtain ⟨response, _, equality⟩ := step
    simp only [mem_support_pure_iff, Prod.mk.injEq] at equality
    rcases equality with ⟨_, rfl⟩
    rw [ih _ _ tail]
    simp [List.reverse_cons, List.map_append, List.append_assoc, CtxHandlerState.addPublic]

set_option backward.isDefEq.respectTransparency false in
/-- Each candidate spends its explicit classified cost; no public probe is hidden in local computation. -/
theorem probes_bound (candidates : List CtxKey) (classify : ReceiveSpec.Domain → Prop)
    [DecidablePred classify] (cost : Nat)
    (charged : ∀ candidate ∈ candidates,
      classify (.inl (.inr (.inl ((), candidate.toList)))) → 0 < cost) :
    (probes candidates).IsQueryBoundP classify (candidates.length * cost) := by
  induction candidates with
  | nil => trivial
  | cons candidate rest ih =>
    simp only [probes, List.length_cons, Nat.succ_mul]
    rw [Nat.add_comm]
    apply isQueryBoundP_bind
    · exact (isQueryBoundP_query_iff classify _ _).mpr (charged candidate (List.mem_cons_self ..))
    · intro _ _
      exact ih (fun next member => charged next (List.mem_cons_of_mem _ member))

/-- Instrumentation adds only the charged public hashes, without selected encryption, raw verification or explicit random calls. -/
theorem probes_bills (candidates : List CtxKey) :
    (probes candidates).IsQueryBoundP SourceHash candidates.length ∧
      (probes candidates).IsQueryBoundP SourceSeal 0 ∧
      (probes candidates).IsQueryBoundP IsRawQuery 0 ∧
      (probes candidates).IsQueryBoundP SourceUniform 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using probes_bound candidates SourceHash 1 (by intros; omega)
  · simpa using probes_bound candidates SourceSeal 0 (by simp [SourceSeal])
  · simpa using probes_bound candidates IsRawQuery 0 (by simp [IsRawQuery])
  · simpa using probes_bound candidates SourceUniform 0 (by simp [SourceUniform])

/-- Every stopped key candidate is a public probe in every supported complete instrumented execution. -/
theorem finish_candidates {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) (state : CanonicalState)
    (result : (Result × List CtxKey) × CanonicalState)
    (supported : result ∈ support ((simulateQ (canonicalImpl decode c key) (finish client)).run state)) :
    ∀ candidate ∈ result.1.2, candidate.toList ∈ result.2.ctx.publicInputs := by
  simp only [finish, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨value, middle⟩, _, ⟨⟨ignored, last⟩, probed, equality⟩⟩ := supported
  cases equality
  have history := probes_public decode c key value.2 middle (ignored, last) probed
  intro candidate member
  rw [history]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨candidate, List.mem_reverse.mpr member, rfl⟩)

/-- An adaptive candidate equal to the selected key is an exact secret-prefix hit, regardless of its dependence on earlier ciphertexts. -/
theorem finish_hit {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) (state : CanonicalState)
    (result : (Result × List CtxKey) × CanonicalState)
    (supported : result ∈ support ((simulateQ (canonicalImpl decode c key) (finish client)).run state))
    (hit : key ∈ result.1.2) :
    ∃ input ∈ result.2.ctx.publicInputs, CtxPrefixIsolation.SecretPrefixQuery key input := by
  refine ⟨key.toList, finish_candidates decode c key client state result supported key hit, ?_⟩
  simp [CtxPrefixIsolation.SecretPrefixQuery]

/-- The exact adaptive client retains its source hash budget plus every final candidate probe. -/
theorem finish_hash {Result : Type} (client : OracleComp ReceiveSpec (Result × List CtxKey))
    (qHash qCandidates : Nat) (hashBound : client.IsQueryBoundP SourceHash qHash)
    (lengthBound : ∀ result ∈ support client, result.2.length ≤ qCandidates) :
    (finish client).IsQueryBoundP SourceHash (qHash + qCandidates) := by
  unfold finish
  apply isQueryBoundP_bind hashBound
  intro result supported
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
    ((probes_bills result.2).1.mono (lengthBound result supported))

/-- Terminal probes preserve every source allowance whose category excludes public hash calls. -/
theorem finish_uncharged {Result : Type} (client : OracleComp ReceiveSpec (Result × List CtxKey))
    (classify : ReceiveSpec.Domain → Prop) [DecidablePred classify] (bound : Nat)
    (sourceBound : client.IsQueryBoundP classify bound)
    (noProbe : ∀ candidate : CtxKey, ¬classify (.inl (.inr (.inl ((), candidate.toList))))) :
    (finish client).IsQueryBoundP classify bound := by
  unfold finish
  rw [← Nat.add_zero bound]
  apply isQueryBoundP_bind sourceBound
  intro result _
  simp only [bind_pure_comp, isQueryBoundP_map_iff]
  simpa using probes_bound result.2 classify 0 (by
    intro candidate _ hit
    exact (noProbe candidate hit).elim)

/-- The real shared-ROM key-hit event keeps the same retained analysis key and full original public history. -/
def CanonicalPrefix {Result : Type} (result : CtxKey × (Result × CanonicalState)) : Prop :=
  ∃ input ∈ result.2.2.ctx.publicInputs, CtxPrefixIsolation.SecretPrefixQuery result.1 input

/-- Real adaptive key hits reduce to conventional validation IND$ and every indexed raw forgery attempt; the additional factor two explicitly pays for transferring the hit event itself. -/
theorem canonical_prefix_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (client : OracleComp ReceiveSpec Result)
    (qHash qSeal qRaw : Nat) (hashBound : client.IsQueryBoundP SourceHash qHash)
    (sealBound : client.IsQueryBoundP SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP IsRawQuery qRaw) (small : qSeal < 2 ^ 96) :
    Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c client}[CanonicalPrefix x] ≤
      2 * (ENNReal.ofReal (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c client qHash)) +
        (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
        ∑ index ∈ Finset.range qRaw, CtxNonceAeadIntCtxt.modifiedNonceAeadINTCTXTAdvantage c
          (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode client) index)) := by
  have exactPrefix :
      Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c client}[CanonicalPrefix x] =
        Pr{let x ← AdaptiveCtxPrefix.retainedRoutedGame decode c client}[AdaptiveCtxPrefix.RetainedPrefix x] := by
    rw [← AdaptiveCtxPrefixValidation.retainedCanonicalGame_eq_routed, prEvent_map]
    exact prEvent_congr _ _ _ fun _ => Iff.rfl
  rw [exactPrefix]
  calc
    _ ≤ Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c client}[AdaptiveCtxPrefix.RetainedPrefix x] +
        ENNReal.ofReal (discreteDistance (AdaptiveCtxPrefix.retainedRoutedGame decode c client)
          (AdaptiveCtxRetainedKey.retainedIndependentGame decode c client)) :=
      AdaptiveCtxPrefixValidation.probEvent_le_add_ofReal_tvDist _ _ _
    _ ≤ Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c client}[AdaptiveCtxPrefix.RetainedPrefix x] +
        Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c client}[AdaptiveCtxPrefix.RetainedPrefix x] := by
      apply add_le_add le_rfl
      exact (ENNReal.ofReal_le_ofReal (AdaptiveCtxPrefix.retainedRoutedGame_distance_le_prefix decode c client)).trans_eq
        (ENNReal.ofReal_toReal (prEvent_ne_top _))
    _ = 2 * Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c client}[AdaptiveCtxPrefix.RetainedPrefix x] := (two_mul _).symm
    _ ≤ _ := mul_le_mul_right (AdaptiveCtxPrefixValidation.independent_prefix_le_indDollar_add_intctxt
      decode c fallback client qHash qSeal qRaw hashBound sealBound rawBound small) 2

/-- Candidate equality is tested only as a retained-key analysis event. -/
def CandidateHit {Result : Type} (result : CtxKey × ((Result × List CtxKey) × CanonicalState)) : Prop :=
  result.1 ∈ result.2.1.2

/-- Adding terminal probes preserves the actual selected-key/candidate correlation and its probability. -/
theorem candidate_probability_finish {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) :
    Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c (finish client)}[CandidateHit x] =
      Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c client}[CandidateHit x] := by
  simp only [AdaptiveCtxPrefixValidation.retainedCanonicalGame]
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun key => ?_
  congr 1
  rw [bind_pure_comp _ (canonicalGame decode c key (finish client)),
    bind_pure_comp _ (canonicalGame decode c key client), prEvent_map, prEvent_map]
  have exactEvent := (finish_result decode c key client canonicalInitial).prEvent_eq
    (fun result : Result × List CtxKey => key ∈ result.2)
  rw [prEvent_map, prEvent_map] at exactEvent
  simpa only [CandidateHit, canonicalGame] using exactEvent

/-- Every instrumented candidate hit is a public-prefix event on that same complete run. -/
theorem candidate_le_prefix {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) :
    Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c (finish client)}[CandidateHit x] ≤
      Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c (finish client)}[CanonicalPrefix x] := by
  apply prEvent_mono_of_support
  rintro ⟨key, result⟩ supported hit
  simp only [AdaptiveCtxPrefixValidation.retainedCanonicalGame, mem_support_bind_iff,
    mem_support_pure_iff] at supported
  obtain ⟨draw, _, reached, complete, equality⟩ := supported
  cases equality
  exact finish_hit decode c key client canonicalInitial result complete hit

/-- The original adaptive known-candidate hit has concrete ordinary reductions and an explicit complete probe ledger. -/
theorem candidate_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (client : OracleComp ReceiveSpec (Result × List CtxKey))
    (qHash qCandidates qSeal qRaw : Nat) (hashBound : client.IsQueryBoundP SourceHash qHash)
    (lengthBound : ∀ result ∈ support client, result.2.length ≤ qCandidates)
    (sealBound : client.IsQueryBoundP SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP IsRawQuery qRaw) (small : qSeal < 2 ^ 96) :
    Pr{let x ← AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c client}[CandidateHit x] ≤
      2 * (ENNReal.ofReal (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c (finish client) (qHash + qCandidates))) +
        ((qHash + qCandidates : Nat) : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
        ∑ index ∈ Finset.range qRaw, CtxNonceAeadIntCtxt.modifiedNonceAeadINTCTXTAdvantage c
          (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
            (wrapped decode (finish client)) index)) := by
  rw [← candidate_probability_finish]
  apply (candidate_le_prefix decode c client).trans
  exact canonical_prefix_bound decode c fallback (finish client) (qHash + qCandidates) qSeal qRaw
    (finish_hash client qHash qCandidates hashBound lengthBound)
    (finish_uncharged client SourceSeal qSeal sealBound (by simp [SourceSeal]))
    (finish_uncharged client IsRawQuery qRaw rawBound (by simp [IsRawQuery])) small

/-- The actual validation reduction pays one additional seal and all source/probe digest randomness; its challenger samples its own separate 32-byte key. -/
theorem candidate_validation_bills {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) (qUniform qHash qCandidates qSeal qRaw : Nat)
    (coinBound : client.IsQueryBoundP SourceUniform qUniform)
    (hashBound : client.IsQueryBoundP SourceHash qHash)
    (lengthBound : ∀ result ∈ support client, result.2.length ≤ qCandidates)
    (sealBound : client.IsQueryBoundP SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP IsRawQuery qRaw) :
    (AdaptiveCtxPrefixValidation.validationReduction decode c (finish client) (qHash + qCandidates)).main.IsQueryBoundP
      CtxNonceAeadIntCtxt.IsModifiedNonceAeadSealQuery (qSeal + 1) ∧
    (AdaptiveCtxPrefixValidation.validationReduction decode c (finish client) (qHash + qCandidates)).main.IsQueryBoundP
      AdaptiveRawNonceAead.IsPrimitiveUniformQuery (qUniform + 64 * (qHash + qCandidates + qSeal + qRaw)) ∧
    (CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarRealExp c
      (AdaptiveCtxPrefixValidation.validationReduction decode c (finish client) (qHash + qCandidates))).IsTotalQueryBound
      (32 + (qUniform + 64 * (qHash + qCandidates + qSeal + qRaw))) := by
  have coins := finish_uncharged client SourceUniform qUniform coinBound (by simp [SourceUniform])
  have hashes := finish_hash client qHash qCandidates hashBound lengthBound
  have seals := finish_uncharged client SourceSeal qSeal sealBound (by simp [SourceSeal])
  have raws := finish_uncharged client IsRawQuery qRaw rawBound (by simp [IsRawQuery])
  exact ⟨AdaptiveCtxPrefixValidation.validationReduction_seal_bound decode c (finish client) (qHash + qCandidates) qSeal seals,
    AdaptiveCtxPrefixValidation.validationReduction_uniform_bound decode c (finish client)
      qUniform (qHash + qCandidates) qSeal qRaw coins hashes seals raws,
    AdaptiveCtxPrefixValidation.validationReal_uniform_bound decode c (finish client)
      qUniform (qHash + qCandidates) qSeal qRaw coins hashes seals raws⟩

/-- Every indexed integrity reduction retains the complete source/probe digest cost and the original selected sealing allowance. -/
theorem candidate_integrity_bills {Result : Type} (decode : RawDecoder)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (client : OracleComp ReceiveSpec (Result × List CtxKey)) (qUniform qHash qCandidates qSeal qRaw index : Nat)
    (coinBound : client.IsQueryBoundP SourceUniform qUniform)
    (hashBound : client.IsQueryBoundP SourceHash qHash)
    (lengthBound : ∀ result ∈ support client, result.2.length ≤ qCandidates)
    (sealBound : client.IsQueryBoundP SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP IsRawQuery qRaw) :
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode (finish client)) index).main.IsQueryBoundP
      AdaptiveRawNonceAead.IsPrimitiveUniformQuery (qUniform + 64 * (qHash + qCandidates + qSeal + qRaw)) ∧
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode (finish client)) index).MakesAtMostSealQueries qSeal :=
  AdaptiveCtxQueryBounds.indexedReduction_bounds decode fallback (finish client)
    qUniform (qHash + qCandidates) qSeal qRaw index
    (finish_uncharged client SourceUniform qUniform coinBound (by simp [SourceUniform]))
    (finish_hash client qHash qCandidates hashBound lengthBound)
    (finish_uncharged client SourceSeal qSeal sealBound (by simp [SourceSeal]))
    (finish_uncharged client IsRawQuery qRaw rawBound (by simp [IsRawQuery]))

end BeaconcryptCore.Computational.RawCtxSelectedKeyProbes

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_result

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.probes_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.probes_public

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.probes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.probes_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.probes_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.probes_bills

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_hit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_hash

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_uncharged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.finish_uncharged

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.canonical_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.canonical_prefix_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_probability_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_probability_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_le_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_le_prefix

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_validation_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_validation_bills

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_integrity_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedKeyProbes.candidate_integrity_bills
