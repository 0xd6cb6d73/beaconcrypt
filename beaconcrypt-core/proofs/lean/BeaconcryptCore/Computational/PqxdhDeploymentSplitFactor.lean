-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironment

/-!
# Factoring the split hidden wrappers of the environment (CE-11a, increment 4)

The environment's split hidden build and finish in capability form (`PqxdhDeploymentEnvironment.buildSplitFwd`, `buildSplitEnv`, `finishSplitFwd` and `finishSplitEnv`, increment 3) are the CE-side split forms `PqxdhDeploymentHiddenSplit.buildSplit` and `finishSplit` (increment 2) with their BLAKE2b query forwarded. Read through `PqxdhDeploymentEnvironment.ctxEffects` (coins as coins, `.hash` as the lazy CTX oracle on a cache, the administrative capabilities by any interpretation `admin`), the forwarded forms run exactly as the CE-side forms on that cache (`buildSplit_factor`, `finishSplit_factor`), and the environment wrappers add only the settlement of the build, the source commit of the finish and the hidden install or abort request (`buildSplitEnv_factor`, `finishSplitEnv_factor`). This is the factoring that increment 3 left open.

**Build.** Both forms run the same factored Server build (`PqxdhServerAuthLoggedSendFactor.factored`), the CE-side form with the native logged response tail and the environment's form with the forwarded tail. The generic build commutes with simulation of its send and auxiliary callbacks (`continueRust_simulateQ`, `afterInitialization_simulateQ`, `candidate_simulateQ`, `genericBuild_simulateQ`, `sendLabels_simulateQ`, `factored_simulateQ`), so both forms are their tails run on one program `freeBuild` whose callbacks are left as queries (`factored_free`, `buildFactor_free`, `buildSplitFwd_free`), and `PqxdhDeploymentEnvironment.tail_factor` relates the two tails.

**Finish.** The native primitive interpreter is the ROM-level one (`PqxdhDeploymentHiddenEntry.romPrim`) run on the CTX coordinate with BLAKE2b answered by the lazy CTX oracle (`nativePrim_lift`); the finish body uses the primitives only through the labelled receive (`PqxdhDeploymentHiddenEntry.factoredBody_requests`), so the native erased finish is the ROM-level erased finish run the same way (`receiveLabels_rom`, `factoredBody_rom`, `finishErased_rom`, with the focused-run tools `lift_run`, `lift_pure`, `lift_map`, `lift_simulateQ`), and the forwarded `.hash` read through `ctxEffects` is that oracle (`hashFx_ctx`).

These are equalities of programs. No security, secrecy or authentication claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (EnvEffects CapabilitySpec)
open PqxdhServerRegistrationPublication (AuxSpec TailSpec)
open PqxdhServerAuthSendFactor (Kernel)

/-! ### Naturality of the generic Server build under simulation -/

section Build
variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} {m : Type → Type} [Monad m] [LawfulMonad m]
  (impl : QueryImpl spec₀ m) {Metadata PeerMetadata Consumed : Type}

omit [LawfulMonad m] in
/-- A Rust result continuation commutes with simulation. -/
theorem continueRust_simulateQ {α β : Type} (result : RustM α) (next : α → OracleComp spec₀ (RustM β)) :
    simulateQ impl (PqxdhInitialGenericBuilder.continueRust result next) =
      PqxdhInitialGenericBuilder.continueRust result fun value => simulateQ impl (next value) := by
  cases result <;> simp only [PqxdhInitialGenericBuilder.continueRust, simulateQ_pure]

/-- The first send and Phase 2 writing of a build commute with simulation when the callbacks do. -/
theorem afterInitialization_simulateQ (calls₀ : RawCtxChainOwner.Calls Kernel (OracleComp spec₀))
    (calls : RawCtxChainOwner.Calls Kernel m) (aux₀ : QueryImpl AuxSpec (OracleComp spec₀)) (aux : QueryImpl AuxSpec m)
    (send : ∀ entry context, calls.send entry context = simulateQ impl (calls₀.send entry context))
    (auxEq : ∀ query, aux query = simulateQ impl (aux₀ query))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state =
      simulateQ impl (PqxdhInitialGenericPublication.afterInitialization calls₀ aux₀ candidate authenticated kernel
        metadata state) := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  rw [send, simulateQ_bind]
  refine bind_congr fun sent => ?_
  rcases sent with ⟨advanced, encrypted⟩
  rw [auxEq, simulateQ_bind]
  refine bind_congr fun _ => ?_
  cases encrypted with
  | none => simp only [simulateQ_pure]
  | some encrypted =>
      simp only [auxEq, simulateQ_bind]
      refine bind_congr fun serialized => ?_
      cases serialized <;> simp only [simulateQ_pure]

/-- The candidate admission and first send of a build commute with simulation when the callbacks do. -/
theorem candidate_simulateQ (calls₀ : RawCtxChainOwner.Calls Kernel (OracleComp spec₀))
    (calls : RawCtxChainOwner.Calls Kernel m) (aux₀ : QueryImpl AuxSpec (OracleComp spec₀)) (aux : QueryImpl AuxSpec m)
    (send : ∀ entry context, calls.send entry context = simulateQ impl (calls₀.send entry context))
    (auxEq : ∀ query, aux query = simulateQ impl (aux₀ query))
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state =
      simulateQ impl (PqxdhInitialGenericBuilder.candidate calls₀ aux₀ initial candidate data metadata state) := by
  unfold PqxdhInitialGenericBuilder.candidate
  simp only [auxEq, simulateQ_bind, apply_ite (simulateQ impl), simulateQ_pure, continueRust_simulateQ, simulateQ_map,
    afterInitialization_simulateQ impl calls₀ calls aux₀ aux send auxEq]

/-- The generic Server build commutes with simulation when its send and auxiliary callbacks do. -/
theorem genericBuild_simulateQ (calls₀ : RawCtxChainOwner.Calls Kernel (OracleComp spec₀))
    (calls : RawCtxChainOwner.Calls Kernel m) (aux₀ : QueryImpl AuxSpec (OracleComp spec₀)) (aux : QueryImpl AuxSpec m)
    (send : ∀ entry context, calls.send entry context = simulateQ impl (calls₀.send entry context))
    (auxEq : ∀ query, aux query = simulateQ impl (aux₀ query))
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed) :
    PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state =
      simulateQ impl (PqxdhServerAuthSendFactor.genericBuild calls₀ aux₀ initial pending data metadata state) := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  rw [continueRust_simulateQ]
  congr 1
  funext next
  cases next with
  | Err error => simp only [simulateQ_pure]
  | Ok next =>
      dsimp only
      rw [continueRust_simulateQ]
      congr 1
      funext prepared
      cases prepared with
      | Err error => simp only [simulateQ_pure]
      | Ok candidate => exact candidate_simulateQ impl calls₀ calls aux₀ aux send auxEq _ _ _ _ _

/-- The labelled Server send primitives commute with simulation. -/
theorem sendLabels_simulateQ (prim₀ : QueryImpl RawCtxSourceSend.PrimitiveSpec (OracleComp spec₀))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) :
    PqxdhServerAuthSendFactor.primLabels (fun request => simulateQ impl (prim₀ request)) source challenge =
      impl ∘ₛ PqxdhServerAuthSendFactor.primLabels prim₀ source challenge := by
  funext query
  cases query with
  | inl slot => simp only [PqxdhServerAuthSendFactor.primLabels, QueryImpl.apply_compose, simulateQ_pure]
  | inr pending =>
      simp only [PqxdhServerAuthSendFactor.primLabels, QueryImpl.apply_compose]
      rw [← QueryImpl.simulateQ_compose]
      rfl

/-- The factored Server build commutes with simulation of its primitive and auxiliary callbacks. -/
theorem factored_simulateQ
    (receive₀ : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      OracleComp spec₀ (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (receive : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext → m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim₀ : QueryImpl RawCtxSourceSend.PrimitiveSpec (OracleComp spec₀)) (aux₀ : QueryImpl AuxSpec (OracleComp spec₀))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (value : PqxdhServerAuthSendFactor.Factor)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerAuthLoggedSendFactor.factored receive (fun request => simulateQ impl (prim₀ request)) source
        (fun request => simulateQ impl (aux₀ request)) value pending data metadata state =
      simulateQ impl (PqxdhServerAuthLoggedSendFactor.factored receive₀ prim₀ source aux₀ value pending data metadata
        state) := by
  unfold PqxdhServerAuthLoggedSendFactor.factored
  rw [simulateQ_map, genericBuild_simulateQ impl (PqxdhServerAuthLoggedSendFactor.calls receive₀ prim₀ source value.1)
    (PqxdhServerAuthLoggedSendFactor.calls receive (fun request => simulateQ impl (prim₀ request)) source value.1)
    aux₀ _ (fun entry context => ?_) (fun _ => rfl)]
  simp only [PqxdhServerAuthLoggedSendFactor.calls]
  rw [sendLabels_simulateQ, QueryImpl.simulateQ_compose]

end Build

/-! ### The split hidden build: factoring against `PqxdhDeploymentHiddenSplit.buildSplit` -/

/-- The factored Server build with every primitive and auxiliary callback left as a query of the registration tail. -/
noncomputable def freeBuild (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (value : PqxdhServerAuthSendFactor.Factor)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    OracleComp TailSpec (RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState)) :=
  PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
    (fun request => liftM (TailSpec.query (.inl request))) source (fun request => liftM (TailSpec.query (.inr request)))
    value pending data () server

/-- The factored Server build with the callbacks of a tail interpreter is that interpreter run on `freeBuild`. -/
theorem factored_free {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl TailSpec m)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (value : PqxdhServerAuthSendFactor.Factor)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None)) (fun request => impl (.inl request))
        source (fun request => impl (.inr request)) value pending data () server =
      simulateQ impl (freeBuild source value pending data server) := by
  have prim : (fun request => impl (.inl request)) =
      fun request => simulateQ impl (liftM (TailSpec.query (.inl request)) : OracleComp TailSpec _) := by
    funext request
    rw [simulateQ_spec_query]
  have aux : (fun request => impl (.inr request)) =
      fun request => simulateQ impl (liftM (TailSpec.query (.inr request)) : OracleComp TailSpec _) := by
    funext request
    rw [simulateQ_spec_query]
  rw [prim, aux]
  exact factored_simulateQ impl _ _ _ _ source value pending data () server

section BuildFactor
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))

/-- The factor-form hidden build is the native logged tail run on `freeBuild`. -/
theorem buildFactor_free (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    PqxdhDeploymentHiddenEntry.buildFactor setup codec checks material seed token payload server =
      simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
        (freeBuild setup.source (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material seed))
          token.pending payload server) :=
  factored_free (PqxdhServerAuthExperiment.tailImpl setup codec checks) _ _ _ _ _

/-- The forwarded split build, before its kernel replacement, is the forwarded logged tail run on `freeBuild`. -/
theorem buildSplitFwd_free (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    PqxdhDeploymentEnvironment.buildSplitFwd (n := n) setup codec checks material token payload server =
      Functor.map (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel) <$>
        simulateQ (PqxdhDeploymentEnvironment.tailFwd setup codec checks)
          (freeBuild setup.source (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material
            PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload server) := by
  unfold PqxdhDeploymentEnvironment.buildSplitFwd
  rw [factored_free (PqxdhDeploymentEnvironment.tailFwd setup codec checks)]

/-- Factoring of the split hidden build (open point of increment 3): the CE-side split build `PqxdhDeploymentHiddenSplit.buildSplit` on a seal log and a CTX cache is the environment's forwarded split build `buildSplitFwd` on the log, its forwarded BLAKE2b queries answered by the lazy CTX oracle on the cache (`ctxEffects`, any interpretation `admin` of the administrative capabilities, which it never issues). -/
theorem buildSplit_factor (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) (log : List RawCtxSourceSend.SealContext)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhDeploymentHiddenSplit.buildSplit setup codec checks material token payload server).run (log, cache) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin)
          ((PqxdhDeploymentEnvironment.buildSplitFwd (n := n) setup codec checks material token payload server).run
            log)).run cache := by
  unfold PqxdhDeploymentHiddenSplit.buildSplit
  rw [buildFactor_free, buildSplitFwd_free, StateT.run_map, StateT.run_map,
    PqxdhDeploymentEnvironment.tail_factor admin setup codec checks, simulateQ_map, StateT.run_map, Functor.map_map,
    Functor.map_map]

/-- The environment's split hidden build read through `ctxEffects` is the CE-side split build `buildSplit` on the seal log and the cache, settled as the native build settles it, followed by its hidden install request answered by `admin`. -/
theorem buildSplitEnv_factor (material : PqxdhDeploymentHiddenLayout.Material) (slot : PqxdhRecordLiftInterface.Slot n)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) (log : List RawCtxSourceSend.SealContext)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin)
        ((PqxdhDeploymentEnvironment.buildSplitEnv (n := n) setup codec checks material slot token payload server).run
          log)).run cache =
      (PqxdhDeploymentHiddenSplit.buildSplit setup codec checks material token payload server).run (log, cache) >>=
        fun result => (fun installed => ((PqxdhServerAuthExperiment.settle server result.1, result.2.1), installed.2)) <$>
          (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin) (PqxdhDeploymentEnvironment.hiddenServerEffect slot
            (PqxdhServerAuthExperiment.settle server result.1))).run result.2.2 := by
  rw [buildSplit_factor setup codec checks admin, bind_map_left]
  simp only [PqxdhDeploymentEnvironment.buildSplitEnv, StateT.run_bind, simulateQ_bind, bind_pure_comp]
  refine bind_congr fun result => ?_
  simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]

end BuildFactor

/-! ### The split hidden finish: factoring against `PqxdhDeploymentHiddenSplit.finishSplit` -/

section Lift
variable {σ ρ : Type} (E : LazyOracleDiscard.StateLens σ ρ)

/-- One run of a step on a focused coordinate. -/
theorem lift_run {α : Type} (step : StateT ρ ProbComp α) (state : σ) :
    (E.lift step).run state = (fun result => (result.1, E.set state result.2)) <$> step.run (E.get state) := rfl

/-- Running a pure step on a focused coordinate is pure. -/
theorem lift_pure {α : Type} (value : α) : E.lift (pure value : StateT ρ ProbComp α) = pure value := by
  apply StateT.ext
  intro state
  simp only [lift_run, StateT.run_pure, map_pure, E.set_get]

/-- Running a mapped step on a focused coordinate maps the run. -/
theorem lift_map {α β : Type} (f : α → β) (step : StateT ρ ProbComp α) : E.lift (f <$> step) = f <$> E.lift step := by
  apply StateT.ext
  intro state
  simp only [lift_run, StateT.run_map, Functor.map_map]

/-- Simulation by steps on a focused coordinate is the focused simulation. -/
theorem lift_simulateQ {ι' α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (StateT ρ ProbComp))
    (work : OracleComp spec' α) :
    simulateQ (fun query => E.lift (impl query) : QueryImpl spec' (StateT σ ProbComp)) work = E.lift (simulateQ impl work) := by
  apply StateT.ext
  intro state
  rw [PqxdhDeploymentFinishErasure.simulateQ_lift]
  rfl

end Lift

section FinishFactor
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
open PqxdhDeploymentHiddenKernels (ctxLens)

/-- The native primitive interpreter is the ROM-level interpreter run on the CTX coordinate with BLAKE2b answered by the lazy CTX oracle. -/
theorem nativePrim_lift : PqxdhServerAuthBeaconFactor.nativePrim setup codec =
    fun query => ctxLens.lift (simulateQ CtxRomAuth.ctxRandomOracle
      (PqxdhDeploymentHiddenEntry.romPrim setup.source.crypto query)) := by
  funext query
  exact PqxdhDeploymentHiddenEntry.nativePrim_rom setup codec query

/-- The labelled receive primitives over the native interpreter are the ROM-level ones run on the CTX coordinate. -/
theorem receiveLabels_rom (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) :
    PqxdhServerAuthBeaconFactor.primLabels (PqxdhServerAuthBeaconFactor.nativePrim setup codec) source challenge =
      fun query => ctxLens.lift (simulateQ CtxRomAuth.ctxRandomOracle (PqxdhServerAuthBeaconFactor.primLabels
        (PqxdhDeploymentHiddenEntry.romPrim setup.source.crypto) source challenge query)) := by
  funext query
  cases query with
  | inl slot => simp only [PqxdhServerAuthBeaconFactor.primLabels, simulateQ_pure, lift_pure]
  | inr pending =>
      simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, nativePrim_lift setup codec]
      rw [lift_simulateQ, ← QueryImpl.simulateQ_compose]
      rfl

/-- The finish body over the native interpreter is the ROM-level finish body run on the CTX coordinate (whatever the send callbacks, which the finish never calls). -/
theorem factoredBody_rom
    (sendNative : Kernel → RawCtxSourceSend.SealContext →
      PqxdhDeploymentHiddenKernels.NativeM (Kernel × Option RawCtxSourceSend.Encrypted))
    (sendRom : Kernel → RawCtxSourceSend.SealContext →
      OracleComp CtxRomAuth.CtxRO (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : PqxdhServerAuthSendFactor.Factor)
    (raw : Pqxdh.Bytes) :
    PqxdhDeploymentHiddenKernels.factoredBody (PqxdhServerAuthBeaconFactor.nativePrim setup codec) sendNative source
        decode prepared value raw =
      ctxLens.lift (simulateQ CtxRomAuth.ctxRandomOracle (PqxdhDeploymentHiddenKernels.factoredBody
        (PqxdhDeploymentHiddenEntry.romPrim setup.source.crypto) sendRom source decode prepared value raw)) := by
  rw [PqxdhDeploymentHiddenEntry.factoredBody_requests, PqxdhDeploymentHiddenEntry.factoredBody_requests, simulateQ_map,
    lift_map, receiveLabels_rom setup codec, lift_simulateQ, ← QueryImpl.simulateQ_compose]
  rfl

/-- The erased hidden finish over the native interpreter is the ROM-level erased finish run on the CTX coordinate, for a pure application getter. -/
theorem finishErased_rom
    (sendNative : Kernel → RawCtxSourceSend.SealContext →
      PqxdhDeploymentHiddenKernels.NativeM (Kernel × Option RawCtxSourceSend.Encrypted))
    (sendRom : Kernel → RawCtxSourceSend.SealContext →
      OracleComp CtxRomAuth.CtxRO (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (application : Response → Option Pqxdh.Bytes)
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : PqxdhServerAuthSendFactor.Factor) :
    PqxdhDeploymentHiddenKernels.finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec) sendNative source
        (fun response => pure (application response)) decode prepared value =
      ctxLens.lift (simulateQ CtxRomAuth.ctxRandomOracle (PqxdhDeploymentHiddenKernels.finishErased
        (PqxdhDeploymentHiddenEntry.romPrim setup.source.crypto) sendRom source
          (fun response => pure (application response)) decode prepared value)) := by
  unfold PqxdhDeploymentHiddenKernels.finishErased
  simp only [pure_bind]
  cases application prepared.response with
  | none => simp only [simulateQ_pure, lift_pure]
  | some raw =>
      dsimp only
      split
      · rw [simulateQ_map, lift_map, factoredBody_rom setup codec sendNative sendRom]
      · simp only [simulateQ_pure, lift_pure]

/-- The forwarded BLAKE2b request read through `ctxEffects` is the lazy CTX oracle. -/
theorem hashFx_ctx : PqxdhDeploymentEnvironment.ctxEffects admin ∘ₛ PqxdhDeploymentEnvironment.hashFx (n := n) =
    CtxRomAuth.ctxRandomOracle := by
  funext query
  simp only [QueryImpl.apply_compose, PqxdhDeploymentEnvironment.hashFx, PqxdhDeploymentEnvironment.request,
    simulateQ_spec_query, PqxdhDeploymentEnvironment.ctxEffects]

/-- Factoring of the split hidden finish (open point of increment 3): the CE-side split finish `PqxdhDeploymentHiddenSplit.finishSplit` on a CTX cache is the environment's forwarded split finish `finishSplitFwd`, its forwarded BLAKE2b query answered by the lazy CTX oracle on the cache (`ctxEffects`, any interpretation `admin` of the administrative capabilities, which it never issues). -/
theorem finishSplit_factor (material : PqxdhDeploymentHiddenLayout.Material)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhDeploymentHiddenSplit.finishSplit setup codec material pending).run ((), cache) =
      (fun result => (result.1, ((), result.2))) <$>
        (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin)
          (PqxdhDeploymentEnvironment.finishSplitFwd (n := n) setup codec material pending)).run cache := by
  unfold PqxdhDeploymentHiddenSplit.finishSplit PqxdhDeploymentHiddenEntry.finishErasedSvc
    PqxdhDeploymentHiddenEntry.finishPointed PqxdhDeploymentEnvironment.finishSplitFwd
  rw [← QueryImpl.simulateQ_compose, hashFx_ctx admin, finishErased_rom setup codec _ (fun entry _ => pure (entry, none)),
    simulateQ_map, simulateQ_map]
  simp only [StateT.run_map, lift_run, Functor.map_map]
  rfl

/-- The environment's split hidden finish read through `ctxEffects` is the CE-side split finish `finishSplit` on the cache, the source commit with its two pin checks, and the hidden install or abort request answered by `admin`. -/
theorem finishSplitEnv_factor (material : PqxdhDeploymentHiddenLayout.Material) (slot : PqxdhRecordLiftInterface.Slot n)
    (index : Nat) (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin)
        (PqxdhDeploymentEnvironment.finishSplitEnv (n := n) setup codec material slot index control before pending)).run
          cache =
      (PqxdhDeploymentHiddenSplit.finishSplit setup codec material pending).run ((), cache) >>= fun result =>
        (fun installed => (PqxdhBeaconPhase2Publication.finish control before result.1, installed.2)) <$>
          (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin) (PqxdhDeploymentEnvironment.hiddenOwnerEffect slot index
            before (PqxdhBeaconPhase2Publication.finish control before result.1).2)).run result.2.2 := by
  rw [finishSplit_factor setup codec admin, bind_map_left]
  simp only [PqxdhDeploymentEnvironment.finishSplitEnv, simulateQ_bind, StateT.run_bind, bind_pure_comp]
  refine bind_congr fun result => ?_
  simp only [simulateQ_map, StateT.run_map]

end FinishFactor

end BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.continueRust_simulateQ' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.continueRust_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.afterInitialization_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.afterInitialization_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.candidate_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.candidate_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.genericBuild_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.genericBuild_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.sendLabels_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.sendLabels_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.factored_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.factored_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.factored_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.factored_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildFactor_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildFactor_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildSplitFwd_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildSplitFwd_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildSplit_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildSplit_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildSplitEnv_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.buildSplitEnv_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_run' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_pure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_map' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_simulateQ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.lift_simulateQ

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.nativePrim_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.nativePrim_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.receiveLabels_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.receiveLabels_rom

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.factoredBody_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.factoredBody_rom

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.finishErased_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.finishErased_rom

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.hashFx_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.hashFx_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.finishSplit_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.finishSplit_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.finishSplitEnv_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSplitFactor.finishSplitEnv_factor
