-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashShared
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDrawMemo

/-! Source allocation, finite coins, public hashes and bookkeeping in the combined digest experiment. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashBase
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhRecordFactsDigestCache (cacheOf)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (plain packed coins_exact)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Public hash evaluation uses the same shared address and full source-cache poststate as the ordinary native interface. -/
theorem hash_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (bytes : Pqxdh.Bytes) (state : CtxPrivate n) :
    (simulateQ plain ((PqxdhRecordFactsHashShared.compile (.inr ((), bytes))).run state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.hash bytes)).run state := by
  rw [PqxdhRecordFactsHashShared.query_exact]
  simp only [PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordFactsCounterProtocol.sampled, PqxdhRecordLiftIdeal.onBase, StateT.run,
    bind_pure_comp, Functor.map_map, packed, PqxdhRecordFactsHashShared.source]
  rfl

/-- Literal finite-coin query, with every source state field retained. -/
def coin (query : unifSpec.Domain) (state : CtxPrivate n) :
    OracleComp (Spec n) (unifSpec.Range query × CtxPrivate n) :=
  (fun reply => (reply, state)) <$> (Spec n).query (.inr query)

/-- The coin branch has the exact source reply and complete state under the combined interpreter. -/
theorem coin_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : unifSpec.Domain) (state : CtxPrivate n) :
    (simulateQ plain (coin query state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.coin query)).run state := by
  simp only [coin, simulateQ_map, simulateQ_spec_query, plain,
    PqxdhRecordFactsCollisionOracle.plain, PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordFactsCounterProtocol.sampled, PqxdhRecordLiftIdeal.onBase, StateT.run,
    Functor.map_map, packed]
  rfl

/-- Retain the exact source effect charge while issuing no cryptographic query. -/
def charge (kind : PqxdhRecordLiftInterface.EffectKind) (state : CtxPrivate n) :
    OracleComp (Spec n) (Unit × CtxPrivate n) :=
  pure ((), { state with base := { state.base with primitive :=
    ({ state.base.primitive.1 with effects := Function.update state.base.primitive.1.effects kind (state.base.primitive.1.effects kind + 1) }, state.base.primitive.2) } })

/-- Explicit effect accounting is preserved exactly in the combined experiment. -/
theorem charge_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kind : PqxdhRecordLiftInterface.EffectKind) (state : CtxPrivate n) :
    (simulateQ plain (charge kind state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.charge kind)).run state := by
  simp only [charge, simulateQ_pure, map_pure,
    PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordLiftIdeal.onBase, StateT.run, map_pure, packed]
  congr 1

/-- Publish the literal source writer buffer under its actual tag and clear that buffer. -/
def publish (tag : PqxdhDeploymentInterface.FrameTag) (state : CtxPrivate n) :
    OracleComp (Spec n) (Unit × CtxPrivate n) :=
  pure ((), { state with base := PqxdhRecordLiftProtocol.publish tag state.base })

/-- Actual publication retains both cache halves and its exact produced-record log. -/
theorem publish_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (tag : PqxdhDeploymentInterface.FrameTag) (state : CtxPrivate n) :
    (simulateQ plain (publish tag state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.publish tag)).run state := by
  simp only [publish, simulateQ_pure, map_pure,
    PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordLiftIdeal.onBase, StateT.run, map_pure, packed]
  congr 1

/-- Run the actual correlated directional-seed allocator with its literal lookup/draw counters. -/
noncomputable def allocate (slot : PqxdhRecordLiftInterface.Slot n) (state : CtxPrivate n) :
    OracleComp (Spec n) (Unit × CtxPrivate n) :=
  (fun result => ((), { state with base := { state.base with seeds := result.2 } })) <$>
    OracleComp.liftComp ((PqxdhRecordLiftLazyTable.impl slot).run state.base.seeds) (Spec n)

/-- Allocation retains its full actual sampler distribution and seed state while framing both commitment caches. -/
theorem allocate_exact (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (slot : PqxdhRecordLiftInterface.Slot n) (state : CtxPrivate n) :
    (simulateQ plain (allocate slot state)).run (cacheOf state) =
      packed <$> (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.allocate slot)).run state := by
  rw [allocate, simulateQ_map, StateT.run_map, StateT.run, coins_exact]
  simp only [PqxdhRecordFactsPrivateCacheWorld.erased,
    PqxdhRecordFactsPrivateCacheCompiler.erasedInterpreter, QueryImpl.apply_compose,
    PqxdhRecordFactsPrivateCacheCompiler.compile, simulateQ_spec_query,
    PqxdhRecordFactsPrivateCacheSource.erased_base, PqxdhRecordFactsPrivateCacheCompiler.base,
    PqxdhRecordFactsPrivateCacheWorld.baseInterpreter, PqxdhRecordFactsCounterProtocol.interpreter,
    PqxdhRecordFactsCounterProtocol.sampled, PqxdhRecordLiftIdeal.onBase, StateT.run,
    bind_pure_comp, Functor.map_map, packed]
  congr 1

end BeaconcryptCore.Computational.PqxdhRecordFactsHashBase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.hash_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.hash_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.coin_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.coin_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.charge_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.charge_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.publish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.publish_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.allocate_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashBase.allocate_exact
