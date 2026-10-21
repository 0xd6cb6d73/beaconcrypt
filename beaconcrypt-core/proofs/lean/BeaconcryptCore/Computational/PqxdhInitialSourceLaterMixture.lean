import BeaconcryptCore.Computational.PqxdhInitialSourceLaterEndpoints

/-! The complete prepared source sampler connects both endpoint simulations to the same original source games and pays the actual prior-input collision event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhInitialSourcePreparedSecrecy
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}


/-- A source-supported distributional simulation charges the explicit bad event once; forward proof annotation changes neither source syntax nor sampling. -/
theorem supported_event_bound {Context : Type} (sampler : ProbComp Context)
    (left right : Context → ProbComp Bool) (bad : Context → Prop)
    (agree : ∀ context ∈ support sampler, ¬ bad context → 𝒟[left context] = 𝒟[right context]) :
    ENNReal.ofReal ((sampler >>= left).boolDistAdvantage (sampler >>= right)) ≤ Pr{let x ← sampler}[bad x] := by
  let annotation := RawCtxSupportedSample.certify sampler (fun context => context ∈ support sampler) (fun _ supported => supported)
  have bound := ofReal_tvDist_bind_left_event_le annotation (fun context => left context.val) (fun context => right context.val)
    (fun context => bad context.val) (fun context good =>
      (VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).2 (EvalDistEq.of_evalDist_eq (agree context.val context.property good)))
  have erased : Subtype.val <$> annotation = sampler := RawCtxSupportedSample.erase sampler _ _
  have leftSame : (annotation >>= fun context => left context.val) = sampler >>= left := RawCtxSupportedSample.run sampler _ _ left
  have rightSame : (annotation >>= fun context => right context.val) = sampler >>= right := RawCtxSupportedSample.run sampler _ _ right
  rw [leftSame, rightSame] at bound
  have probability : Pr{let context ← annotation}[bad context.val] = Pr{let x ← sampler}[bad x] := by
    have mapped := prEvent_map annotation Subtype.val bad
    rw [erased] at mapped
    exact mapped.symm
  have bridged := bound.trans ((VCVioLegacy.probEvent_eq_prEvent annotation fun context => bad context.val).le.trans
    probability.le)
  simpa only [ProbComp.boolDistAdvantage, VCVioLegacy.evalDist_singleton_eq_probOutput] using
    (ENNReal.ofReal_le_ofReal (abs_probOutput_toReal_sub_le_tvDist (sampler >>= left) (sampler >>= right))).trans bridged

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
  (ancestors disclosed : List RatchetChain)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
  (depth remaining : Nat)

local notation "initial" => PqxdhInitialNativeInitializer.initial source selectedMessage previousRoot response64
local notation "mark" => PqxdhInitialSelectedOrigin.mark source selectedMessage
local notation "execution" => PqxdhInitialSourceExperiment.execution response64 index metadata ready post before
local notation "root" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "state" => (PqxdhInitialSourceExperiment.initialState root shared privateState cache, ([] : List RootOutput))
local notation "sourceRun" => PqxdhInitialNativeAuditCarried.carried source writer (pre other) (application other) initial (selector other) (aux other)
  mark sender route decode execution depth (depth + 1) state
local notation "sourceView" => view source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
local notation "sourceSample" => sample source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "sourceAddress" => address source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth
local notation "external" => PqxdhInitialNativeAudit.external (pre other) (application other) initial (selector other) (aux other)




noncomputable def resumed (stage : Nat) (context : Bool ⊕ PqxdhInitialSupportedCertificate.Supported sourceRun)
    (parent : FullOutput) : ProbComp Bool :=
  match context with
  | .inl decision => pure decision
  | .inr input => PqxdhInitialSourceLaterEndpoints.afterParent source writer selectedMessage previousRoot response64 other
      sender route decode index metadata ready post before selected number ancestors disclosed shared privateState cache depth
      stage input parent

local notation "continuation" => resumed source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "observation" => observe source previousRoot response64 selected number ancestors disclosed
local notation "resume" => PqxdhInitialPreparedParent.resume source writer (pre other) (application other) initial (selector other) (aux other)
  mark sender route decode observation

/-- The actual supported prepared sampler resumes with precisely its original full76 parent draw; a common completed bit merely ignores the reduction's separately counted comparison draw. -/
theorem resumed_prepared (stage : Nat) (afterDepth : depth < stage) :
    𝒟[sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation stage context] =
    𝒟[PqxdhInitialPreparedParent.prepare source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode observation execution depth state >>= resume stage] := by
  apply EvalDistEq.evalDist_eq
  rw [← PqxdhInitialPreparedResources.sample_run source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode observation execution depth state (resume stage)]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun context supported => ?_
  cases context with
  | inl decision =>
    exact OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure decision)
  | inr input =>
    have original : Sum.inr input.val ∈ support
        (PqxdhInitialPreparedParent.prepare source writer (pre other) (application other) initial (selector other) (aux other)
          mark sender route decode observation execution depth state) := by
      rw [← PqxdhInitialPreparedResources.sample_erase source writer (pre other) (application other) initial (selector other) (aux other)
        mark sender route decode observation execution depth state, support_map]
      exact ⟨Sum.inr input, supported, rfl⟩
    have drawn := PqxdhInitialPreparedParent.pending_draw source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode observation execution depth stage afterDepth state input.val.2
      (PqxdhInitialSourceExperiment.initial_valid root shared privateState cache depth).1.1 input.val.1 original
    simp only [Sum.map_inr, PqxdhInitialPreparedParent.resume, PqxdhInitialPreparedParent.finish,
      PqxdhInitialNativeAdjacent.continued, RawCtxForwardScan.pack, RawCtxPendingMixedPrefix.finish,
      drawn, bind_map_left, bind_assoc]
    refine EvalDistEq.bind_right ($ᵗ FullOutput) fun parent => ?_
    unfold resumed PqxdhInitialSourceLaterEndpoints.afterParent PqxdhInitialSourcePreparedSecrecy.observe
    rw [bind_pure_comp]

/-- The earlier prepared experiment is exactly the original stage with its unchanged source decision. -/
theorem resumed_real :
    𝒟[sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation (depth + 1) context] =
    𝒟[PqxdhInitialSourceExperiment.game source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected number ancestors disclosed shared privateState cache (depth + 1)] := by
  rw [resumed_prepared source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth (depth + 1) (by omega)]
  rw [PqxdhInitialPreparedParent.prepare_real]
  rw [external_source source selectedMessage previousRoot response64 other]
  unfold PqxdhInitialSourcePreparedSecrecy.observe PqxdhInitialSourceExperiment.game
  rw [bind_pure_comp, PqxdhInitialSourceExperiment.run_source]

/-- The later prepared experiment is exactly the original cached-branch normalization, with the same full source final observation. -/
theorem resumed_normalized :
    𝒟[sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation (depth + 2) context] =
    𝒟[PqxdhInitialNativeAdjacent.normalized source writer mark sender route decode execution
      (PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) depth state.1 >>= observation] := by
  rw [resumed_prepared source writer selectedMessage previousRoot response64 other sender route decode
    index metadata ready post before selected number ancestors disclosed shared privateState cache depth (depth + 2) (by omega)]
  rw [PqxdhInitialPreparedParent.prepare_normalized, external_source source selectedMessage previousRoot response64 other]

noncomputable def parents : ProbComp ((Bool ⊕ PqxdhInitialSupportedCertificate.Supported sourceRun) × FullOutput) := do
  let context ← sourceSample
  let parent ← $ᵗ FullOutput
  pure (context, parent)

noncomputable def bad (pair : (Bool ⊕ PqxdhInitialSupportedCertificate.Supported sourceRun) × FullOutput) : Prop :=
  RawCtxSelectedParentPrivatePatch.targetAddress (nextChain pair.2) ∈
    PqxdhInitialPreparedRisk.addresses source writer (pre other) (application other) initial (selector other) (aux other)
      mark sender route decode execution depth state pair.1

local notation "parentSample" => parents source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected number ancestors disclosed shared privateState cache depth
local notation "badEvent" => bad source writer selectedMessage previousRoot response64 other sender route decode
  index metadata ready post before selected shared privateState cache depth

/-- The same full parent sampler charges the entire prior private-input list and current parent address with its exact source callback allowance. -/
theorem collision_bound (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    Pr{let x ← parentSample}[badEvent x] ≤ ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  have bound := PqxdhInitialPreparedRisk.collision_bound source writer (pre other) (application other) initial (selector other) (aux other)
    mark sender route decode execution depth state observation qPost bounded
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  refine (le_of_eq ?_).trans (bound.trans_eq ?_)
  · unfold parents RawCtxSelectedParentCandidates.sample PqxdhInitialSourcePreparedSecrecy.sample
    refine bindCongr _ _ _ _ _ fun context => ?_
    generalize ($ᵗ FullOutput : ProbComp FullOutput) = block
    rw [bind_pure_comp _ block, bind_pure_comp _ block, prEvent_map, prEvent_map]
    exact prEvent_congr _ _ _ fun _ => Iff.rfl
  · simp only [PqxdhInitialSourceExperiment.initialState, List.length_nil, Nat.zero_add,
      show 7 + qPost * 67 + 1 = 8 + qPost * 67 by omega]

/-- The same original earlier source game differs from its constructed cryptographic observer by at most one explicitly counted prior-input collision event. -/
theorem real_bound (position : number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation (depth + 1) context).boolDistAdvantage
      (PqxdhInitialSourcePreparedSecrecy.actual source writer selectedMessage previousRoot response64 other sender route decode
        index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining)) ≤
      Pr{let x ← parentSample}[badEvent x] := by
  have bound := supported_event_bound parentSample
    (fun pair => continuation (depth + 1) pair.1 pair.2)
    (fun pair => PqxdhInitialCommonSecrecy.native source writer mark sender route decode sourceView
      (pair.1, RawCtxSelectedParentEntry.fromOutput (sourceAddress pair.1) pair.2) (nextChain pair.2)
      (productionStream source.crypto (FixedHkdfDomain.ratchet.address (nextChain pair.2).toList))) badEvent (by
        intro pair supported safe
        rcases pair with ⟨context, parent⟩
        have contextSupported : context ∈ support sourceSample := by
          simp only [parents, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at supported
          obtain ⟨original, reached, output, _, same, _⟩ := supported
          exact same ▸ reached
        cases context with
        | inl decision => rfl
        | inr input =>
          exact congrArg evalDist (PqxdhInitialSourceLaterEndpoints.real_endpoint source writer selectedMessage previousRoot response64 other
            sender route decode index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
            input contextSupported parent safe position))
  simpa only [parents, bind_assoc, pure_bind, PqxdhInitialSourcePreparedSecrecy.actual,
    PqxdhInitialCommonSecrecy.actual, RawCtxSelectedParentCandidates.sample] using bound

/-- The same original normalized later source game differs from its constructed cryptographic observer by at most one explicitly counted prior-input collision event. -/
theorem random_bound (position : number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceSample >>= fun context => ($ᵗ FullOutput) >>= continuation (depth + 2) context).boolDistAdvantage
      (PqxdhInitialSourcePreparedSecrecy.random source writer selectedMessage previousRoot response64 other sender route decode
        index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining)) ≤
      Pr{let x ← parentSample}[badEvent x] := by
  have bound := supported_event_bound parentSample
    (fun pair => continuation (depth + 2) pair.1 pair.2)
    (fun pair => ($ᵗ FullOutput) >>= fun output => PqxdhInitialCommonSecrecy.native source writer mark sender route decode sourceView
      (pair.1, RawCtxSelectedParentEntry.fromOutput (sourceAddress pair.1) pair.2) (nextChain pair.2)
      output) badEvent (by
        intro pair supported safe
        rcases pair with ⟨context, parent⟩
        have contextSupported : context ∈ support sourceSample := by
          simp only [parents, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at supported
          obtain ⟨original, reached, output, _, same, _⟩ := supported
          exact same ▸ reached
        cases context with
        | inl decision =>
          exact (OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure decision)).symm.evalDist_eq
        | inr input =>
          exact PqxdhInitialSourceLaterEndpoints.random_endpoint source writer selectedMessage previousRoot response64 other
            sender route decode index metadata ready post before selected number ancestors disclosed shared privateState cache depth remaining
            input contextSupported parent safe position)
  simpa only [parents, bind_assoc, pure_bind, PqxdhInitialSourcePreparedSecrecy.random,
    PqxdhInitialCommonSecrecy.random, RawCtxSelectedParentCandidates.sample] using bound

end BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.supported_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.supported_event_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.resumed_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.resumed_prepared
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.resumed_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.resumed_real
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.resumed_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.resumed_normalized
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.collision_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.real_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture.random_bound
