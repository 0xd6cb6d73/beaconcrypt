-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills

/-! Explicit finite-coin accounting; random plaintext bytes remain a separate source bill. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Explicit finite-coin requests in the combined source compiler. -/
def coinQuery : (Spec n).Domain → Bool
  | .inr _ => true
  | _ => false

/-- Explicit finite-coin requests of the native compiler's shared interface. -/
def sharedCoin : AdaptiveCtxSharedHash.HashSpec.Domain → Bool
  | .inl _ => true
  | _ => false

/-- Literal native callbacks retain their original charge and introduce no finite-coin query. -/
theorem counted_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (counts : PqxdhRecordLiftWorld.Counts) :
    ((PqxdhRecordFactsHashNative.counted setup codec query).run counts).IsQueryBoundP
      (fun query => sharedCoin query) 0 := by
  rcases query with request | input | input | bytes | frame
  all_goals simp [PqxdhRecordFactsHashNative.counted, PqxdhRecordFactsHashNative.native,
    StateT.run, IsQueryBoundP, sharedCoin]

/-- Every adaptive native program retains all its callbacks while emitting zero explicit finite queries. -/
theorem counted_program_coins {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (counts : PqxdhRecordLiftWorld.Counts) :
    ((simulateQ (PqxdhRecordFactsHashNative.counted setup codec) client).run counts).IsQueryBoundP
      (fun query => sharedCoin query) 0 := by
  induction client using OracleComp.inductionOn generalizing counts with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact isQueryBoundP_bind (counted_coins setup codec query counts) (fun result _ => ih result.1 result.2)

/-- Literal frame logging preserves the native compiler's zero finite-query count. -/
theorem logged_coins {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X)
    (state : PqxdhRecordLiftWorld.Counts × PqxdhRecordLiftLoggedAdapters.Frames) :
    (PqxdhRecordFactsHashNative.loggedProgram setup codec client state).IsQueryBoundP
      (fun query => sharedCoin query) 0 := by
  rw [PqxdhRecordFactsHashNative.loggedProgram, isQueryBoundP_map_iff]
  exact counted_program_coins setup codec _ state.1

/-- Shared compilation forwards each literal finite query and emits no finite query for a digest request. -/
theorem shared_coins {X : Type} (client : OracleComp AdaptiveCtxSharedHash.HashSpec X)
    (cap : Nat) (bounded : client.IsQueryBoundP (fun query => sharedCoin query) cap) (state : CtxPrivate n) :
    ((simulateQ PqxdhRecordFactsHashShared.compile client).run state).IsQueryBoundP
      (fun query => coinQuery query) cap := by
  apply bounded.simulateQ_run_StateT_of_step
  intro query before
  cases query with
  | inl coin => simp [PqxdhRecordFactsHashShared.compile, StateT.run, IsQueryBoundP, sharedCoin, coinQuery]
  | inr address =>
      rcases address with ⟨⟨⟩, bytes⟩
      simp [PqxdhRecordFactsHashShared.compile, StateT.run, IsQueryBoundP, sharedCoin, coinQuery]

/-- Complete caller-known native work contributes zero explicit finite queries; ordinary digest draws and native charges remain separate. -/
theorem native_coins {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : CtxPrivate n) :
    (PqxdhRecordFactsHashShared.nativeProgram setup codec client state).IsQueryBoundP
      (fun query => coinQuery query) 0 := by
  rw [PqxdhRecordFactsHashShared.nativeProgram, isQueryBoundP_map_iff]
  exact shared_coins _ 0 (logged_coins setup codec client (state.base.primitive.1, state.base.pending)) state

/-- Lifting a complete finite sampler preserves its full finite-query cap. -/
theorem coins_bound {X : Type} (work : ProbComp X) (cap : Nat) (bounded : work.IsTotalQueryBound cap) :
    (OracleComp.liftComp work (Spec n)).IsQueryBoundP (fun query => coinQuery query) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => trivial
  | query_bind coin next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).IsQueryBoundP _ cap
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

open CtxRomAuth AdaptiveCtxReceive

/-- A random seal samples exactly its complete body and sixteen tag bytes; its explicit digest request has a separate bill. -/
theorem seal_coins (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (label : Label n) (input : CtxSealInput) (state : PqxdhRecordFactsPrivateCache.State) :
    (PqxdhRecordFactsPrivateCacheSourceDraw.compileSeal crypto key mode label input state).IsQueryBoundP
      (fun query => coinQuery query) (if mode = .random then input.plaintext.length + 16 else 0) := by
  unfold PqxdhRecordFactsPrivateCacheSourceDraw.compileSeal
  split
  · apply isQueryBoundP_bind (coins_bound _ _ (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound input.plaintext.length))
    intro body _
    apply isQueryBoundP_bind (n := 16) (m := 0)
      (coins_bound _ _ (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 16))
    intro tag _
    simp [IsQueryBoundP, coinQuery]
  · simp [IsQueryBoundP, coinQuery]

/-- Full hidden sealing retains its exact random body/tag cap through width rejection, local updates and every writer outcome. -/
theorem hidden_coins (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    (PqxdhRecordFactsPrivateCacheSourceDraw.compileHiddenSeal modes crypto writer replace pending state).IsQueryBoundP
      (fun query => coinQuery query)
      (if modes pending.material = .random then (replace pending.context.plaintext).length + 16 else 0) := by
  unfold PqxdhRecordFactsPrivateCacheSourceDraw.compileHiddenSeal
  split
  · have keyed := seal_coins crypto (PqxdhRecordLiftIdeal.materialAt state.base.chain pending.material).1
      (modes pending.material) pending.material
      (RawCtxSelectedMessageSealing.selectedInput (PqxdhRecordLiftIdeal.materialAt state.base.chain pending.material).2
        pending.sequence (PqxdhRecordLiftIdeal.replaceContext replace pending.context) (by assumption))
      (state.keys pending.material, state.base.primitive.2)
    apply (show _ = _ + 0 from (Nat.add_zero _).symm) ▸ isQueryBoundP_bind (p := fun query : (Spec n).Domain => coinQuery query) ?_ ?_
    · unfold PqxdhRecordFactsPrivateCacheSourceDraw.compileKeyedSeal
      rw [isQueryBoundP_map_iff]
      exact keyed
    · intro result _
      cases result.1 <;> trivial
  · trivial

/-- The actual lazy allocator spends at most 64 byte queries on a miss and none on a hit, retaining the whole directional-seed pair. -/
theorem allocate_coins (slot : PqxdhRecordLiftInterface.Slot n) (state : CtxPrivate n) :
    (PqxdhRecordFactsHashBase.allocate slot state).IsQueryBoundP (fun query => coinQuery query) 64 := by
  rw [PqxdhRecordFactsHashBase.allocate, isQueryBoundP_map_iff]
  apply coins_bound
  cases hit : state.base.seeds.1 slot with
  | none =>
      rw [PqxdhRecordLiftLazyTable.run_miss slot state.base.seeds hit]
      simp only [IsTotalQueryBound, isQueryBound_map_iff]
      exact PqxdhRecordLiftSeedCut.seed_bound
  | some seed =>
      rw [PqxdhRecordLiftLazyTable.run_hit slot state.base.seeds seed hit]
      trivial

/-- Actual random-mode plaintext bytes at each hidden sealing request; no byte bound is inferred from a command-count budget. -/
def randomBodyCost (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    PqxdhRecordLiftProtocol.Service n → Nat
  | .sealing pending => if modes pending.material = .random then (replace pending.context.plaintext).length else 0
  | _ => 0

/-- Existing explicit uniform service costs plus actual random body bytes and a conservative sixteen tag bytes per hidden seal. -/
def coinCost (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : PqxdhRecordLiftProtocol.Service n) : Nat :=
  PqxdhRecordLiftCtxProtocolBounds.categoryCost .uniform query + randomBodyCost modes replace query +
    16 * PqxdhRecordFactsHashSealBills.sealCost query

/-- Every concrete service's explicit finite queries fit its stated uniform, body-byte and tag-byte bill. -/
theorem query_coins (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) :
    ((PqxdhRecordFactsHashSource.compiler modes replace setup codec query).run state).IsQueryBoundP
      (fun query => coinQuery query) (coinCost modes replace query) := by
  cases query with
  | allocate slot => exact allocate_coins slot state
  | coin coin =>
      simp [PqxdhRecordFactsHashSource.compiler, PqxdhRecordFactsHashBase.coin, StateT.run, IsQueryBoundP,
        coinQuery, coinCost, randomBodyCost, PqxdhRecordLiftCtxProtocolBounds.categoryCost,
        PqxdhRecordFactsHashSealBills.sealCost]
  | hash bytes =>
      simp [PqxdhRecordFactsHashSource.compiler, PqxdhRecordFactsHashShared.compile, StateT.run, IsQueryBoundP,
        coinQuery, coinCost, randomBodyCost, PqxdhRecordLiftCtxProtocolBounds.categoryCost,
        PqxdhRecordFactsHashSealBills.sealCost]
  | charge kind => trivial
  | lookup coordinate =>
      apply IsQueryBoundP.of_imp (p' := fun _ => True) (fun _ _ => True.intro)
      rw [isQueryBoundP_true_iff]
      exact PqxdhRecordFactsHashLocal.lookup_queries coordinate state
  | opening pending => trivial
  | sealing pending =>
      apply (hidden_coins modes setup.source.crypto codec.frameWrite replace pending state).mono
      simp only [coinCost, randomBodyCost, PqxdhRecordLiftCtxProtocolBounds.categoryCost,
        PqxdhRecordFactsHashSealBills.sealCost, Nat.zero_add, Nat.mul_one]
      split <;> omega
  | knownSend kernel context => exact native_coins setup codec _ state
  | knownReceive kernel target context => exact native_coins setup codec _ state
  | publish tag => trivial

open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_add)

/-- Scaling an actual weighted source bill preserves every residual budget and typed reply continuation. -/
theorem weighted_scale {κ X : Type} {spec : OracleSpec κ} (cost : spec.Domain → Nat)
    (client : OracleComp spec X) (cap coefficient : Nat) (bounded : Weighted cost client cap) :
    Weighted (fun query => coefficient * cost query) client (coefficient * cap) := by
  unfold Weighted at bounded ⊢
  apply IsQueryBound.proj (fun current => coefficient * current) (h := bounded)
  · intro query current allowed
    exact Nat.mul_le_mul_left coefficient allowed
  · intro query current allowed
    exact Nat.mul_sub_left_distrib coefficient current (cost query)

/-- A complete adaptive source service bill transports to its explicit finite-coin compiler queries with coefficient one. -/
theorem program_coins {X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (cap : Nat)
    (bounded : Weighted (coinCost modes replace) client cap) (state : CtxPrivate n) :
    ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec) client).run state).IsQueryBoundP
      (fun query => coinQuery query) cap :=
  PqxdhRecordLiftCtxBills.run_bound _ (fun query => coinQuery query) (coinCost modes replace)
    (query_coins modes replace setup codec) client cap bounded state

open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)

/-- The whole initialized compiler's finite-query cap keeps actual random plaintext bytes explicit beside existing source uniform and send bills. -/
theorem source_coins {E X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost qBody : Nat)
    (bodyBound : Weighted (randomBodyCost modes replace)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) qBody) :
    ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)).IsQueryBoundP
      (fun query => coinQuery query)
      (PqxdhRecordLiftCtxBills.programBill .uniform ⟨budget, startup, allowance, bounds, n, decisionCost⟩ +
        qBody + 16 * budget.sends) := by
  apply program_coins
  have uniform := PqxdhRecordLiftCtxBills.program_categories .uniform env startup allowance framed
    setup.source.crypto codec route serverKid bounds mode budget adversary respects decisionCost
  have tags := weighted_scale PqxdhRecordFactsHashSealBills.sealCost _ budget.sends 16
    (PqxdhRecordFactsHashSealBills.program_seals env setup.source.crypto codec route serverKid bounds mode
      budget adversary respects)
  exact weighted_add _ _ _ _ _ (weighted_add _ _ _ _ _ uniform bodyBound) tags

/-- Interpreting a logical digest query needs at most 64 uniform byte draws; a literal finite query costs one. -/
def plainCost : (Spec n).Domain → Nat
  | .inl _ => 64
  | .inr _ => 1

-- Instantiating the exact 64-byte sampler bound needs extra elaboration depth.
set_option maxRecDepth 1024 in
/-- Actual lazy digest interpretation charges complete miss sampling and reuses hits without a fresh draw. -/
theorem plain_query_total (query : (Spec n).Domain) (cache : PqxdhRecordFactsDigestCache.Cache n) :
    ((PqxdhRecordFactsPrivateCacheSourceDrawMemo.plain query).run cache).IsTotalQueryBound (plainCost query) := by
  cases query with
  | inl input =>
      exact QueryImpl.isTotalQueryBound_run_withCaching
        (spec := (PqxdhRecordFactsPrivateCacheSourceDraw.HashInput n →ₒ CtxDigest)) (n := 64)
        uniformSampleImpl input
        (by
          change ($ᵗ CtxDigest : ProbComp CtxDigest).IsTotalQueryBound 64
          exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) cache
  | inr coin =>
      simp [PqxdhRecordFactsPrivateCacheSourceDrawMemo.plain, PqxdhRecordFactsCollisionOracle.plain,
        StateT.run, plainCost, IsTotalQueryBound]

/-- Three same-client scalar ledgers pay for every actual finite draw of the memoizing digest experiment. -/
theorem interpreted_total {X : Type} (client : OracleComp (Spec n) X) (qCoins qPrivate qOrdinary : Nat)
    (coins : client.IsQueryBoundP (fun query => coinQuery query) qCoins)
    (privates : client.IsQueryBoundP (fun query => PqxdhRecordFactsHashPrivateBills.privateQuery query) qPrivate)
    (ordinary : client.IsQueryBoundP (fun query => PqxdhRecordFactsHashOrdinaryBills.ordinaryQuery query) qOrdinary)
    (cache : PqxdhRecordFactsDigestCache.Cache n) :
    ((simulateQ PqxdhRecordFactsPrivateCacheSourceDrawMemo.plain client).run cache).IsTotalQueryBound
      (qCoins + 64 * qPrivate + 64 * qOrdinary) := by
  have joint := weighted_add _ _ _ _ _
    (weighted_add _ _ _ _ _
      (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ 1 client qCoins coins)
      (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ 64 client qPrivate privates))
    (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ 64 client qOrdinary ordinary)
  have billed : Weighted plainCost client (qCoins + 64 * qPrivate + 64 * qOrdinary) := by
    convert joint using 1
    · funext query
      rcases query with (address | bytes) | coin <;>
        simp [plainCost, coinQuery, PqxdhRecordFactsHashPrivateBills.privateQuery,
          PqxdhRecordFactsHashOrdinaryBills.ordinaryQuery]
    · simp
  rw [← isQueryBoundP_true_iff]
  apply PqxdhRecordLiftCtxBills.run_bound _ (fun _ => True) plainCost _ client _ billed cache
  intro query before
  rw [isQueryBoundP_true_iff]
  exact plain_query_total query before

/-- The initialized source's complete digest-interpreted sampler keeps body bytes, tag bytes, both digest classes and ordinary source coins explicit. -/
theorem source_interpreted_total {E X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost qBody : Nat)
    (bodyBound : Weighted (randomBodyCost modes replace)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) qBody) :
    ((simulateQ PqxdhRecordFactsPrivateCacheSourceDrawMemo.plain
      ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
          (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅).IsTotalQueryBound
      (PqxdhRecordLiftCtxBills.programBill .uniform ⟨budget, startup, allowance, bounds, n, decisionCost⟩ +
        qBody + 16 * budget.sends + 64 * (budget.sends +
          PqxdhRecordLiftIdeal.sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩)) := by
  simpa only [Nat.mul_add, Nat.add_assoc] using interpreted_total _ _ _ _
    (source_coins modes replace setup codec route env startup allowance framed serverKid bounds mode budget
      adversary respects decisionCost qBody bodyBound)
    (PqxdhRecordFactsHashPrivateBills.source_private modes replace setup codec route env serverKid bounds mode
      budget adversary respects)
    (PqxdhRecordFactsHashOrdinaryBills.source_ordinary modes replace setup codec route env startup allowance framed
      serverKid bounds mode budget adversary respects decisionCost) ∅

/-- A permitted final decision pays its own explicit finite-coin budget after the complete source sampler. -/
theorem source_decision_total {E X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost qBody : Nat)
    (bodyBound : Weighted (randomBodyCost modes replace)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary) qBody)
    (decision : PqxdhRecordLiftIdeal.View n E X → ProbComp Bool)
    (decisionBound : ∀ view, (decision view).IsTotalQueryBound decisionCost) :
    (((simulateQ PqxdhRecordFactsPrivateCacheSourceDrawMemo.plain
      ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
          (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅) >>=
      fun result => decision (PqxdhRecordLiftIdeal.ctxView result.1)).IsTotalQueryBound
      (PqxdhRecordLiftCtxBills.programBill .uniform ⟨budget, startup, allowance, bounds, n, decisionCost⟩ +
        qBody + 16 * budget.sends + 64 * (budget.sends +
          PqxdhRecordLiftIdeal.sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩) + decisionCost) :=
  isTotalQueryBound_bind
    (source_interpreted_total modes replace setup codec route env startup allowance framed serverKid bounds mode
      budget adversary respects decisionCost qBody bodyBound)
    (fun result => decisionBound (PqxdhRecordLiftIdeal.ctxView result.1))

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.counted_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms counted_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.counted_program_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms counted_program_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.logged_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms logged_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.shared_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shared_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.native_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms native_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.coins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms coins_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.seal_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms seal_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.hidden_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms hidden_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.allocate_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms allocate_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.query_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms query_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.weighted_scale' depends on axioms: [propext] -/
#guard_msgs in
#print axioms weighted_scale
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.program_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.source_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.plain_query_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms plain_query_total
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.interpreted_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms interpreted_total
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.source_interpreted_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_interpreted_total
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills.source_decision_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_decision_total

end BeaconcryptCore.Computational.PqxdhRecordFactsHashFiniteBills
