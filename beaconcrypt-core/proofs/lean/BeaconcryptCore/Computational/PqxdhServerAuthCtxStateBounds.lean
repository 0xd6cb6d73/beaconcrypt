import BeaconcryptCore.Computational.PqxdhServerAuthCtxState
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceHandlers
import BeaconcryptCore.Computational.PqxdhServerAuthStopSource

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthSourceCosts PqxdhServerAuthGapDh
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhServerAuthPendingBudget
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse Result : Type}

/-- Forwarding the original uniform oracle preserves its full syntactic output support for every adaptive continuation. -/
theorem coin_support (work : ProbComp Result) :
    support (simulateQ PqxdhServerAuthCtxAmbient.coin work) = support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, support_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhServerAuthCtxAmbient.coin, support_bind, support_query, ih]

/-- The flat-state coin forwarding preserves every source-supported result and its complete private flat state, with the existing designation flag retained. -/
theorem flat_support (work : StateT (FlatState KemSK HiddenTable) ProbComp Result) (state : Local KemSK) :
    support ((flatCoins work).run state) =
      (fun result => (result.1, (result.2, state.2))) '' support (work.run state.1) := by
  simp only [flatCoins, localCoins, StateT.run, coin_support, support_map]

/-- The actual omitted-table services supply their full uniform caps; unused response callbacks are literal pure computations. -/
theorem table_services_uniform (setup : Setup baseSpec KemSK) (context : Context KemSK) (select : Bool) :
    ServiceUniform (tableServices (WireResponse := WireResponse) setup context select) := by
  refine ⟨?_, hidden_public_uniform, ?_, ?_⟩
  · intro message state
    cases select with
    | false => exact hidden_derive_uniform setup.hmac setup.joint setup.dh context.seed context.scalar message state
    | true => exact (select_hidden_uniform setup.joint setup.dh context.seed context.scalar message state).mono (by decide)
  · intros; trivial
  · intros; trivial

/-- Every accept attempt retains the actual source scalar, complete direct/base encapsulation cost and possible table miss, including rejected prefixes and derivations. -/
theorem accept_total (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (caps : KemCaps)
    (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (state : Local KemSK) :
    ((accept setup codec checks context select raw).run state).IsTotalQueryBound (32 + caps.encapsCost + 64) := by
  apply localCoins_bound
  simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    accept_step_uniform setup codec checks (context.publicValue setup) _
      (table_services_uniform setup context select) caps bounded raw state.1

/-- Public HMAC retains its real off-domain computation and pays the actual on-domain omitted-table miss. -/
theorem hmac_total (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (hmacKey : HmacBlock) (message : Pqxdh.Bytes) (state : Local KemSK) :
    ((hmac setup context hmacKey message).run state).IsTotalQueryBound
      (if hmacKey = zeroSalt ∧ message.length = 192 then 64 else 0) := by
  apply localCoins_bound
  simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    hmac_step_uniform setup _ (table_services_uniform (WireResponse := Unit) setup context false) hmacKey message state.1

/-- Complete acceptance has only explicit uniform-route work; no selected record or shared commitment operation is silently hidden in its prefix. -/
theorem accept_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (caps : KemCaps)
    (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (state : Local KemSK) :
    ((accept setup codec checks context select raw).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (32 + caps.encapsCost + 64) ∧
    ((accept setup codec checks context select raw).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
    ((accept setup codec checks context select raw).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    ((accept setup codec checks context select raw).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) ((isQueryBoundP_true_iff _ _).2
    (accept_total setup codec checks context select caps bounded raw state)), localCoins_other _ state⟩

/-- The literal public-HMAC compiler contributes its complete uniform table cost and zero record/hash routes. -/
theorem hmac_bills (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (hmacKey : HmacBlock) (message : Pqxdh.Bytes) (state : Local KemSK) :
    ((hmac setup context hmacKey message).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (if hmacKey = zeroSalt ∧ message.length = 192 then 64 else 0) ∧
    ((hmac setup context hmacKey message).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
    ((hmac setup context hmacKey message).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    ((hmac setup context hmacKey message).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  exact ⟨IsQueryBoundP.of_imp (fun _ _ => True.intro) ((isQueryBoundP_true_iff _ _).2
    (hmac_total setup context hmacKey message state)), localCoins_other _ state⟩

/-- Every dynamic acceptance reply has the actual source allocation/token footprint and changes marks only at its original attempt index; designation remains unchanged. -/
theorem accept_footprint (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (select : Bool) (raw : Pqxdh.Bytes)
    (state : Local KemSK) (result : Option Nat × Local KemSK)
    (supported : result ∈ support ((accept setup codec checks context select raw).run state)) :
    ResourceStep (.inr (.accept raw)) state.1.1 result.2.1.1 ∧
      MarkStep (.inr (.accept raw)) state.1 result.2.1 ∧ result.2.2 = state.2 := by
  simp only [accept, flat_support, Set.mem_image] at supported
  obtain ⟨output, original, rfl⟩ := supported
  exact ⟨acceptStep_resources setup codec checks (context.publicValue setup) _ raw state.1 output original,
    accept_marks setup codec checks (context.publicValue setup) _ raw state.1 output original, rfl⟩

/-- Every possible public-HMAC reply retains the original allocation, Beacon, pending-token and mark footprint, including an omitted-entry table hit. -/
theorem hmac_footprint (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (hmacKey : HmacBlock) (message : Pqxdh.Bytes) (state : Local KemSK) (result : HmacBlock × Local KemSK)
    (supported : result ∈ support ((hmac setup context hmacKey message).run state)) :
    ResourceStep (.inr (.hmac hmacKey message)) state.1.1 result.2.1.1 ∧
      MarkStep (.inr (.hmac hmacKey message)) state.1 result.2.1 ∧ result.2.2 = state.2 := by
  simp only [hmac, flat_support, Set.mem_image] at supported
  obtain ⟨output, original, rfl⟩ := supported
  simp only [hmacStep, StateT.run] at original
  split_ifs at original
  · obtain ⟨read, _, original⟩ := (mem_support_bind_iff _ _ _).1 original
    simp only [support_pure, Set.mem_singleton_iff] at original
    subst original
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at original
    subst original
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-- The original adversary coin request forwards one explicit uniform query and no commitment or record query. -/
theorem coin_bills (query : unifSpec.Domain) (state : Local KemSK) :
    ((coins (unifSpec.query query)).run state).IsTotalQueryBound 1 ∧
    ((coins (unifSpec.query query)).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 1 ∧
    ((coins (unifSpec.query query)).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
    ((coins (unifSpec.query query)).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    ((coins (unifSpec.query query)).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  simp [coins, StateT.run_lift, PqxdhServerAuthCtxAmbient.coin, IsTotalQueryBound,
    AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxDynamicKnownBounds.HashRoute,
    AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceUniform,
    AdaptiveCtxQueryBounds.SourceHash, AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxReceive.IsRawQuery]

/-- Public commitment requests forward their one shared hash, with zero selected seal, raw opening or explicit uniform calls. The interpreter's digest samples are charged separately. -/
theorem hash_bills (bytes : Pqxdh.Bytes) (state : Local KemSK) :
    ((PqxdhServerAuthCtxState.hash bytes).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 1 ∧
    ((PqxdhServerAuthCtxState.hash bytes).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    ((PqxdhServerAuthCtxState.hash bytes).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
    ((PqxdhServerAuthCtxState.hash bytes).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  simp [PqxdhServerAuthCtxState.hash, StateT.run_lift, PqxdhServerAuthCtxAmbient.hash,
    AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxDynamicKnownBounds.HashRoute,
    AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxQueryBounds.SourceUniform,
    AdaptiveCtxQueryBounds.SourceHash, AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxReceive.IsRawQuery]

/-- The actual installed-kernel reveal performs its original local lookup without a component query. -/
theorem reveal_total (keyId : Std.U64) (state : Local KemSK) :
    ((reveal keyId).run state).IsTotalQueryBound 0 := by
  trivial

/-- Forwarded source coins preserve the entire executable protocol state for every returned sample. -/
theorem coins_state (work : ProbComp Result) (state : Local KemSK) (result : Result × Local KemSK)
    (supported : result ∈ support ((coins work).run state)) : result.2 = state := by
  simp only [coins, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨value, _, rfl⟩ := supported
  rfl

/-- Public hashing preserves all executable protocol fields; its actual shared cache remains in the separate component interpreter. -/
theorem hash_state (bytes : Pqxdh.Bytes) (state : Local KemSK) (result : CtxRomAuth.CtxDigest × Local KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxState.hash bytes).run state)) : result.2 = state := by
  simp only [PqxdhServerAuthCtxState.hash, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨value, _, rfl⟩ := supported
  rfl

/-- The actual installed-kernel reveal returns its source lookup and preserves the complete executable state. -/
theorem reveal_state (keyId : Std.U64) (state : Local KemSK)
    (result : Option ratchet.concrete.ConcreteRatchetKernel × Local KemSK)
    (supported : result ∈ support ((reveal keyId).run state)) : result.2 = state := by
  simp only [reveal, StateT.run, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  rfl

end BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.coin_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.coin_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.flat_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.flat_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.table_services_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.table_services_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.accept_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.accept_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hmac_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hmac_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.accept_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.accept_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hmac_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hmac_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.accept_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.accept_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hmac_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hmac_footprint
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.coin_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.coin_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hash_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hash_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.reveal_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.reveal_total
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.coins_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.coins_state
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hash_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.hash_state
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.reveal_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxStateBounds.reveal_state
