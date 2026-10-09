-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle

/-! Complete private/shared lazy-cache coherence for the actual hidden sealing compiler. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate materialAt)
open PqxdhRecordFactsPrivateCacheSourceDraw (HashInput Spec compileSeal compileKeyedSeal compileHiddenSeal evaluate)
open PqxdhRecordFactsPrivateCacheFresh (sealResult)
open PqxdhRecordFactsDigestCache (Cache cacheOf sealedState)
variable {n : Nat}

/-- The existing ordinary memoizing oracle on exactly the combined digest interface. -/
noncomputable abbrev plain : QueryImpl (Spec n) (StateT (Cache n) ProbComp) :=
  PqxdhRecordFactsCollisionOracle.plain

private theorem apply_bind {S X Y : Type} (work : StateT S ProbComp X)
    (next : X → StateT S ProbComp Y) (state : S) :
    (work >>= next) state = work state >>= fun result => next result.1 result.2 := rfl

private theorem apply_pure {S X : Type} (value : X) (state : S) :
    (pure value : StateT S ProbComp X) state = pure (value, state) := rfl

private theorem apply_map {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]; rfl

/-- Every finite coin is forwarded without changing either half of the combined cache. -/
theorem coins_exact {X : Type} (work : ProbComp X) (cache : Cache n) :
    (simulateQ plain (OracleComp.liftComp work (Spec n))) cache =
      (fun reply => (reply, cache)) <$> work := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [OracleComp.liftComp_pure, simulateQ_pure, apply_pure, map_pure]
  | query_bind coin next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change (simulateQ plain ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>=
        fun reply => OracleComp.liftComp (next reply) (Spec n))) cache = _
      simp only [simulateQ_bind, simulateQ_spec_query, apply_bind, plain,
        PqxdhRecordFactsCollisionOracle.plain, bind_map_left, map_bind]
      exact bind_congr fun reply => ih reply cache

/-- A virgin private address is a literal miss in the combined memoizing oracle. -/
theorem private_query (state : CtxPrivate n) (label : Label n) (suffix : Pqxdh.Bytes)
    (missing : (state.keys label).2 suffix = none) :
    plain (.inl (.inl (label, suffix))) (cacheOf state) =
      (fun digest : CtxDigest => (digest, (cacheOf state).cacheQuery (.inl (label, suffix)) digest)) <$>
        ($ᵗ CtxDigest) := by
  change (((HashInput n →ₒ CtxDigest).randomOracle (.inl (label, suffix))).run (cacheOf state)) = _
  rw [randomOracle.run_eq, show cacheOf state (.inl (label, suffix)) = none from missing]
  rw [bind_pure_comp]

/-- Retain the complete source result and its exact combined cache together. -/
def packed {X : Type} (result : X × CtxPrivate n) : (X × CtxPrivate n) × Cache n :=
  (result, cacheOf result.2)

/-- The generic keyed seal compiler, under its source missing-point premise, retains exactly the combined cache of its complete poststate. -/
theorem keyed_memo (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (label : Label n) (input : CtxSealInput) (state : CtxPrivate n)
    (empty : (state.keys label).2 = ∅) :
    (simulateQ plain (compileKeyedSeal modes crypto label input state)).run (cacheOf state) =
      packed <$> simulateQ (evaluate ordinary) (compileKeyedSeal modes crypto label input state) := by
  unfold compileKeyedSeal compileSeal
  by_cases random : modes label = .random
  · simp only [random, ↓reduceIte, simulateQ_map, simulateQ_bind, simulateQ_spec_query,
      PqxdhRecordFactsPrivateCacheSourceDraw.evaluate_coins,
      evaluate, StateT.run, apply_map, apply_bind, coins_exact]
    simp only [bind_map_left, map_bind, simulateQ_pure, apply_pure]
    refine bind_congr fun body => ?_
    refine bind_congr fun tag => ?_
    rw [private_query state label _ (by simp [empty])]
    simp only [map_pure, bind_pure_comp, Functor.map_map]
    apply congrArg (fun f => f <$> ($ᵗ CtxDigest))
    funext digest
    apply Prod.ext
    · rfl
    · exact (PqxdhRecordFactsDigestCache.cacheOf_sealed state label input body.toList tag.toList
        tag.toList_length digest).symm
  · simp only [random, ↓reduceIte, simulateQ_map, simulateQ_bind, simulateQ_spec_query,
      evaluate, StateT.run, apply_map, apply_bind]
    rw [private_query state label _ (by simp [empty])]
    simp only [simulateQ_pure, apply_pure, bind_pure_comp, Functor.map_map]
    apply congrArg (fun f => f <$> ($ᵗ CtxDigest))
    funext digest
    apply Prod.ext
    · rfl
    · exact (PqxdhRecordFactsDigestCache.cacheOf_sealed state label input _ _
        (crypto.aeadSeal_tag_length _ _ _ _) digest).symm

/-- The memoizing private address interpretation is exactly the original erased keyed step and its canonical combined post-cache. -/
theorem keyed_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (label : Label n) (input : CtxSealInput) (state : CtxPrivate n)
    (supported : modes label ≠ .real) (empty : (state.keys label).2 = ∅)
    (unused : (state.keys label).1.usedNonces = []) :
    (simulateQ plain (compileKeyedSeal modes crypto label input state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto
        (label, .inl (.inr (.inr input)))).run state := by
  rw [keyed_memo ordinary modes crypto label input state empty,
    PqxdhRecordFactsPrivateCacheSourceDraw.keyedSeal_exact ordinary modes decode crypto label input state
      supported empty unused]

/-- Width rejection, writer success and writer failure preserve the complete memoizing cache/result equality. -/
theorem hidden_memo (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (empty : (state.keys pending.material).2 = ∅) :
    (simulateQ plain (compileHiddenSeal modes crypto writer replace pending state)).run (cacheOf state) =
      packed <$> simulateQ (evaluate ordinary) (compileHiddenSeal modes crypto writer replace pending state) := by
  unfold compileHiddenSeal
  split
  · simp only [simulateQ_bind, StateT.run_bind]
    rw [keyed_memo ordinary modes crypto _ _ state empty]
    simp only [bind_map_left, map_bind, packed]
    refine bind_congr fun result => ?_
    cases result.1 <;>
      simp only [simulateQ_pure, StateT.run_pure, map_pure, packed, PqxdhRecordFactsDigestCache.cacheOf_pending]
  · simp only [simulateQ_pure, StateT.run_pure, map_pure, packed]

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual hidden service is reproduced with both complete source state and exact ordinary/private combined cache retained. -/
theorem hidden_exact (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (supported : modes pending.material ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state (.sealing pending)) :
    (simulateQ plain
      (compileHiddenSeal modes setup.source.crypto codec.frameWrite replace pending state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run state := by
  rw [hidden_memo ordinary modes setup.source.crypto codec.frameWrite replace pending state fresh.1,
    PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_exact ordinary modes replace setup codec pending state supported fresh]

/-- The complementary ordinary/base compiler is used precisely outside the hidden sealing constructor. -/
def NonSealing : PqxdhRecordLiftProtocol.Service n → Prop
  | .sealing _ => False
  | _ => True

/-- Combine an explicit ambient compiler with the proved hidden sealing compiler; no source work is omitted. -/
noncomputable def compiled
    (ambient : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n))))
    (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n)))
  | .sealing pending => compileHiddenSeal modes crypto writer replace pending
  | query => ambient query

/-- The exact operational interface required of the complementary compiler, including its full source result and combined cache. This is a consuming equality obligation, not a primitive or security contract. -/
def AmbientExact
    (ambient : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n))))
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) : Prop :=
  ∀ query, NonSealing query → ∀ state,
    (simulateQ plain ((ambient query).run state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run state

/-- With the ordinary/base operational equations discharged, every source service agrees jointly with the combined memoizing cache. -/
theorem query_compile (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (ambient : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n))))
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ambientExact : AmbientExact ambient modes replace setup codec)
    (supported : ∀ label, modes label ≠ .real)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state query) :
    (simulateQ plain ((compiled ambient modes setup.source.crypto codec.frameWrite replace query).run state)).run
      (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec query).run state := by
  cases query with
  | sealing pending => exact hidden_exact ordinary modes replace setup codec pending state (supported _) fresh
  | _ => apply ambientExact; trivial

/-- Complete adaptive compiler/cache equality, transporting the original history invariant over supported source replies. The ambient premise is the explicit complementary operational join. -/
theorem program_compile (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (ambient : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n))))
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ambientExact : AmbientExact ambient modes replace setup codec)
    (supported : ∀ label, modes label ≠ .real) {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (state : CtxPrivate n) (past : List (Label n))
    (good : PqxdhRecordFactsPrivateCacheSource.Virgin state past)
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated client past).AllQueriesSatisfy
      PqxdhRecordLiftProtocolHistory.Fresh) :
    (simulateQ plain ((simulateQ (compiled ambient modes setup.source.crypto codec.frameWrite replace) client).run state)).run
      (cacheOf state) =
      packed <$> (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) client).run state := by
  induction client using OracleComp.inductionOn generalizing state past with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, packed]
  | query_bind query next ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_compile ordinary ambient modes replace setup codec ambientExact supported query state
        (PqxdhRecordFactsPrivateCacheSource.freshPoint query state past good fresh.1)]
      simp only [bind_map_left, map_bind, packed]
      apply bind_congr_of_forall_mem_support
      intro result reached
      exact ih result.1 result.2 _
        (PqxdhRecordFactsPrivateCacheSource.query_virgin modes replace setup codec query state past good result reached)
        (fresh.2 result.1)

open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)

/-- The initialized source discharges the private freshness and history conditions; only the explicitly separated ordinary/base compiler equations remain as a consuming obligation. -/
theorem source_compile {E X : Type} (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (ambient : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (CtxPrivate n) (OracleComp (Spec n))))
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ambientExact : AmbientExact ambient modes replace setup codec)
    (supported : ∀ label, modes label ≠ .real)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    (simulateQ plain ((simulateQ (compiled ambient modes setup.source.crypto codec.frameWrite replace)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅ =
      packed <$> PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary := by
  rw [← PqxdhRecordFactsDigestCache.cacheOf_initial (n := n)]
  exact program_compile ordinary ambient modes replace setup codec ambientExact supported _ _ []
    PqxdhRecordFactsPrivateCacheSource.initial_virgin
    (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary)

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.coins_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.coins_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.private_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.private_query
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.keyed_memo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.keyed_memo
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.keyed_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.keyed_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.hidden_memo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.hidden_memo
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.hidden_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.hidden_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.query_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.query_compile
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.program_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.program_compile
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.source_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo.source_compile
