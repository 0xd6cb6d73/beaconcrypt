-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCounterProtocol

/-! The source's actual native primitives with shared hash queries exposed and other operations retained. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashNative
open PqxdhRecordLiftWorld (Counts Primitive)
open PqxdhServerAuthExperiment (Setup Codec)
open AdaptiveCtxSharedHash (HashSpec hashImpl)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X)
    (state : S) : (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state :=
  StateT.run_map f work state

/-- Functional source HKDF/AEAD and optional frame writing remain real; only the actual shared commitment hash is exposed as an oracle query. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp HashSpec)
  | .inl request => pure (RawCtxSourceHkdf.response setup.source.crypto request)
  | .inr (.inl input) => pure (some (setup.source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inr (.inl input)) => pure (RawCtxSourceOpen.baseOpen setup.source.crypto input)
  | .inr (.inr (.inr (.inl bytes))) =>
      (fun digest => some digest.toList) <$> HashSpec.query (.inr ((), bytes))
  | .inr (.inr (.inr (.inr frame))) => pure (codec.frameWrite frame)

/-- Interpreting the exposed hash query reproduces the exact source native reply and shared cache. -/
theorem native_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (q : RawCtxMixedOwner.NativeSpec.Domain) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (fun result => (result.1, ((), result.2))) <$> (simulateQ hashImpl (native setup codec q)).run cache =
      (PqxdhDeploymentNative.primitives setup codec q).run ((), cache) := by
  rcases q with request | input | input | bytes | frame
  all_goals simp [native, hashImpl, PqxdhDeploymentNative.primitives, RawCtxMixedShared.sharedImpl,
    RawCtxMixedShared.sharedAdapter, QueryImpl.compose, StateT.run_pure,
    StateT.run_map, Functor.map_map]
  all_goals first | rfl | skip
  change ((fun result => (some result.1.toList, ((), result.2))) <$>
    (CtxRomAuth.ctxRandomOracle ((), bytes)).run cache) =
      ((CtxRomAuth.ctxRandomOracle ((), bytes)).run cache >>= fun result =>
        pure (some result.1.toList, ((), result.2)))
  exact (bind_pure_comp _ _).symm

/-- Charge the same native call category without changing either other counter family. -/
def charge (counts : Counts) (q : RawCtxMixedOwner.NativeSpec.Domain) : Counts :=
  { counts with native := Function.update counts.native (RawCtxMixedOwner.callKind q) (counts.native (RawCtxMixedOwner.callKind q) + 1) }

/-- Source native compilation retains every native charge; the actual shared cache belongs to the hash interpreter. -/
noncomputable def counted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Counts (OracleComp HashSpec)) :=
  fun q counts => (fun reply => (reply, charge counts q)) <$> native setup codec q

/-- Exact complete reply, counts and shared cache after one compiled primitive call. -/
theorem counted_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (q : RawCtxMixedOwner.NativeSpec.Domain) (state : Primitive) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((counted setup codec q).run state.1)).run state.2 =
        (PqxdhRecordFactsCounter.primitives setup codec q).run state := by
  have same := congrArg (fun work =>
    (fun result : RawCtxMixedOwner.NativeSpec.Range q × (Unit × CtxRomAuth.CtxRO.QueryCache) =>
      (result.1, (charge state.1 q, result.2.2))) <$> work) (native_exact setup codec q state.2)
  simpa only [counted, PqxdhRecordFactsCounter.primitives, StateT.run, simulateQ_map,
    StateT.run_map, map_apply, bind_pure_comp, Functor.map_map, charge] using same

/-- Interpreting the counted native compiler gives exactly the original interpreter with uniform instrumentation projected away. -/
theorem counted_interpreter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    (hashImpl.mapStateTBase (counted setup codec)).flattenStateT =
      PqxdhRecordFactsCounter.primitives setup codec := by
  ext q state
  exact counted_exact setup codec q state

/-- The complete adaptive native program retains all primitive results, call counts and shared-cache correlations. -/
theorem program_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {X : Type}
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : Primitive) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((simulateQ (counted setup codec) client).run state.1)).run state.2 =
        (simulateQ (PqxdhRecordFactsCounter.primitives setup codec) client).run state := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, counted_interpreter]
  simp only [Functor.map_map, Prod.eta]
  exact id_map _

/-- Retain the actual frame logger around the native compiler, including failed writes. -/
noncomputable def logged (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec
      (StateT (Counts × PqxdhRecordLiftLoggedAdapters.Frames) (OracleComp HashSpec)) :=
  fun q state => PqxdhRecordLiftLoggedAdapters.swapResult <$>
    (simulateQ (counted setup codec) ((PqxdhDeploymentNative.frameLog q).run state.2)).run state.1

/-- Compiling the actual logger retains the literal reply, call counters, shared cache and every submitted frame. -/
theorem logged_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (q : RawCtxMixedOwner.NativeSpec.Domain)
    (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    (fun result => (result.1.1, ((result.1.2.1, result.2), result.1.2.2))) <$>
      (simulateQ hashImpl ((logged setup codec q).run (state.1.1, state.2))).run state.1.2 =
        (PqxdhRecordLiftLoggedAdapters.loggedNative
          (PqxdhRecordFactsCounter.primitives setup codec) q).run state := by
  have same := congrArg (fun work => PqxdhRecordLiftLoggedAdapters.swapResult <$> work)
    (program_exact setup codec ((PqxdhDeploymentNative.frameLog q).run state.2) state.1)
  simpa only [logged, PqxdhRecordLiftLoggedAdapters.loggedNative, StateT.run, simulateQ_map,
    map_apply, Functor.map_map, PqxdhRecordLiftLoggedAdapters.swapResult] using same

/-- Compile a complete native client with its literal per-command writer log. -/
noncomputable def loggedProgram (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {X : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec X)
    (state : Counts × PqxdhRecordLiftLoggedAdapters.Frames) :
    OracleComp HashSpec (X × (Counts × PqxdhRecordLiftLoggedAdapters.Frames)) :=
  PqxdhRecordLiftLoggedAdapters.swapResult <$>
    (simulateQ (counted setup codec)
      ((simulateQ PqxdhDeploymentNative.frameLog client).run state.2)).run state.1

/-- All adaptive native continuations retain their complete evaluated distribution, cache and failed-writer logs. -/
theorem loggedProgram_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {X : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec X)
    (state : Primitive × PqxdhRecordLiftLoggedAdapters.Frames) :
    (fun result => (result.1.1, ((result.1.2.1, result.2), result.1.2.2))) <$>
      (simulateQ hashImpl (loggedProgram setup codec client (state.1.1, state.2))).run state.1.2 =
        (simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative
          (PqxdhRecordFactsCounter.primitives setup codec)) client).run state := by
  rw [PqxdhRecordLiftLoggedAdapters.program_logged]
  have same := congrArg (fun work => PqxdhRecordLiftLoggedAdapters.swapResult <$> work)
    (program_exact setup codec ((simulateQ PqxdhDeploymentNative.frameLog client).run state.2) state.1)
  simpa only [loggedProgram, simulateQ_map, StateT.run_map,
    Functor.map_map, PqxdhRecordLiftLoggedAdapters.swapResult] using same

/-- Exact explicit hash allowance for a native request; the digest interpreter's finite draws are charged separately. -/
def hashCost : RawCtxMixedOwner.NativeSpec.Domain → Nat
  | .inr (.inr (.inr (.inl _))) => 1
  | _ => 0

/-- No native call introduces extra hash queries or free finite randomness. -/
theorem native_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (q : RawCtxMixedOwner.NativeSpec.Domain) :
    (native setup codec q).IsTotalQueryBound (hashCost q) := by
  rcases q with request | input | input | bytes | frame
  all_goals simp [native, hashCost, IsTotalQueryBound]

/-- Source native-counter instrumentation introduces no extra oracle requests. -/
theorem counted_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (q : RawCtxMixedOwner.NativeSpec.Domain) (counts : Counts) :
    ((counted setup codec q).run counts).IsTotalQueryBound (hashCost q) := by
  simpa only [counted, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using native_queries setup codec q

end BeaconcryptCore.Computational.PqxdhRecordFactsHashNative

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.native_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.counted_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.counted_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.counted_interpreter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.counted_interpreter

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.program_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.program_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.logged_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.logged_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.loggedProgram_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.loggedProgram_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.native_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.native_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.counted_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashNative.counted_queries
