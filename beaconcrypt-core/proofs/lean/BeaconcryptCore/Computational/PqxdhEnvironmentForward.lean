-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftInterface
import BeaconcryptCore.Computational.RawCtxSourceHkdf
import BeaconcryptCore.Computational.RawCtxMixedShared
import BeaconcryptCore.Computational.LazyOracleDiscard
/-! Exact generic environment coin/hash forwarding and cache factoring tools are shared independently of the legacy registration/start/installation model. The original Environment module reimports every declaration under its unchanged namespace; all its separate model/source obligations remain in that module and the final root. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentEnvironment
open PqxdhRecordLiftInterface (Capability CapabilitySpec EnvEffects)
variable {n : Nat}
/-- One coin of a registration computation as a coin effect of the record world. -/
def coinFx : QueryImpl unifSpec (OracleComp (EnvEffects n)) :=
  fun coin => ((EnvEffects n).query (.inl coin) : OracleComp (EnvEffects n) _)

/-- A probabilistic registration computation with its coins as coin effects. -/
def coins {α : Type} (work : ProbComp α) : OracleComp (EnvEffects n) α := simulateQ coinFx work

/-- One capability request. -/
def request (capability : Capability n) : OracleComp (EnvEffects n) ((CapabilitySpec n).Range capability) :=
  ((EnvEffects n).query (.inr capability) : OracleComp (EnvEffects n) _)

/-- A capability request whose reply is not used. -/
def issue (capability : Capability n) : OracleComp (EnvEffects n) Unit := do
  let _ ← request capability
  pure ()

/-- The source primitives (real HKDF, BLAKE2b, AEAD opening) with the BLAKE2b request forwarded to the world's shared cache as a `.hash` capability; HKDF and opening are the source's deterministic functions. -/
def primFwd (c : Pqxdh.Crypto) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp (EnvEffects n))
  | .inl request => pure (RawCtxSourceHkdf.response source.crypto request)
  | .inr (.inl bytes) => (fun digest : CtxRomAuth.CtxDigest => some digest.toList) <$> request (.hash bytes)
  | .inr (.inr input) => pure (RawCtxSourceOpen.baseOpen c input)

/-- The record primitives of the Server build (HKDF, AEAD seal, BLAKE2b, frame writer) with the BLAKE2b request forwarded. -/
def sharedFwd (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp (EnvEffects n)) :=
  primFwd c source ∘ₛ RawCtxMixedShared.sharedAdapter c writer


section Factoring
open LazyOracleDiscard (StateLens CacheLens)
/-- The CTX reading of the environment's effects on a cache: coins are uniform draws, `.hash` is the lazy CTX oracle on the cache, and the administrative capabilities are answered by `admin` (any interpretation; the forwarded primitives issue none). -/
noncomputable def ctxEffects (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp)) :
    QueryImpl (EnvEffects n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.hash bytes) => CtxRomAuth.ctxRandomOracle ((), bytes)
  | .inr capability => admin capability

variable (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))

/-- Coin effects read back as the original coins, with the cache unchanged. -/
theorem ctxEffects_coins {α : Type} (work : ProbComp α) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (ctxEffects admin) (coins (n := n) work)).run cache = (fun value => (value, cache)) <$> work := by
  unfold coins
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind, coinFx]
      simp only [ctxEffects, StateT.run_lift, bind_assoc, pure_bind]
      refine bind_congr fun coin => ?_
      exact ih coin

/-- A forwarded step that never reads or writes the focused cache coordinate of its state, at the program level. -/
theorem frame_program {σ ι' α : Type} {spec' : OracleSpec ι'} (lens : CacheLens CtxRomAuth.CtxRO σ)
    (fwd : QueryImpl spec' (StateT σ (OracleComp (EnvEffects n))))
    (frame : ∀ query state cache, (fwd query).run (lens.set state cache) =
      (fun result => (result.1, lens.set result.2 cache)) <$> (fwd query).run state)
    (work : OracleComp spec' α) (state : σ) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ fwd work).run (lens.set state cache) =
      (fun result => (result.1, lens.set result.2 cache)) <$> (simulateQ fwd work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind, frame, bind_map_left, ih]

/-- Generic capability-form factoring: if every native step is its forwarded step with the forwarded BLAKE2b queries answered by the lazy CTX oracle on the focused cache, and the forwarded steps never touch that coordinate, then every native program is its forwarded program read through `ctxEffects`. -/
theorem factor_program {σ ι' α : Type} {spec' : OracleSpec ι'} (lens : CacheLens CtxRomAuth.CtxRO σ)
    (native : QueryImpl spec' (StateT σ ProbComp)) (fwd : QueryImpl spec' (StateT σ (OracleComp (EnvEffects n))))
    (frame : ∀ query state cache, (fwd query).run (lens.set state cache) =
      (fun result => (result.1, lens.set result.2 cache)) <$> (fwd query).run state)
    (step : ∀ query state, (native query).run state =
      (fun result => (result.1.1, lens.set result.1.2 result.2)) <$>
        (simulateQ (ctxEffects admin) ((fwd query).run state)).run (lens.get state))
    (work : OracleComp spec' α) (state : σ) :
    (simulateQ native work).run state =
      (fun result => (result.1.1, lens.set result.1.2 result.2)) <$>
        (simulateQ (ctxEffects admin) ((simulateQ fwd work).run state)).run (lens.get state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure, lens.set_get]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, step, bind_map_left, ih, map_bind]
      refine bind_congr fun result => ?_
      rw [lens.get_set, frame_program lens fwd frame, simulateQ_map, StateT.run_map, Functor.map_map]
      congr 1
      funext final
      simp only [lens.set_set]

section Primitives
variable {Auxiliary : Type}

/-- The shared source primitives are the forwarded primitives read through `ctxEffects`, with the auxiliary state kept. -/
theorem primFwd_factor (c : Pqxdh.Crypto) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.kdfImpl source) query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (primFwd (n := n) c source query)).run cache := by
  rcases query with request | (bytes | input)
  · simp only [primFwd, simulateQ_pure, StateT.run_pure, map_pure]
    exact RawCtxSourceHkdf.kdf_step source request (auxiliary, cache)
  · change (do
        let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run cache
        pure (some result.1.toList, (auxiliary, result.2))) = _
    simp only [primFwd, simulateQ_map, request, simulateQ_spec_query, ctxEffects, StateT.run_map, Functor.map_map,
      bind_pure_comp]
  · simp only [primFwd, simulateQ_pure, StateT.run_pure, map_pure]
    rfl

/-- Generic stateless factoring: native steps on (auxiliary, cache) that are forwarded steps read through `ctxEffects` with the auxiliary state kept give the same for every program. -/
theorem factor_stateless {ι' α : Type} {spec' : OracleSpec ι'}
    (native : QueryImpl spec' (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (fwd : QueryImpl spec' (OracleComp (EnvEffects n)))
    (step : ∀ query auxiliary cache, (native query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$> (simulateQ (ctxEffects admin) (fwd query)).run cache)
    (work : OracleComp spec' α) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ native work).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$> (simulateQ (ctxEffects admin) (simulateQ fwd work)).run cache := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, step, bind_map_left, ih, map_bind]

end Primitives

end Factoring

/-- A stateless simulation only shrinks the support. -/
theorem support_simulateQ_subset {ι₁ ι₂ α : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (OracleComp spec₂)) (work : OracleComp spec₁ α) :
    support (simulateQ impl work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, support_pure, subset_refl]
  | query_bind query next ih =>
      intro result supported
      simp only [simulateQ_query_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, member⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply member⟩

end BeaconcryptCore.Computational.PqxdhDeploymentEnvironment

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ctxEffects_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ctxEffects_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.primFwd_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.primFwd_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_stateless' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_stateless

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.support_simulateQ_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.support_simulateQ_subset
