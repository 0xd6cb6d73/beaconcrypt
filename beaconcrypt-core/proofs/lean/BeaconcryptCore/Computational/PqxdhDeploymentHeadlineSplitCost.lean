-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleResources
import BeaconcryptCore.Computational.PqxdhServerAuthTailCosts

/-!
# The per-step uniform bound of the anomaly guesser's split handler (CE-12 P2b, design-v2 section 9)

CE-11b's anomaly guesser (`PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser`) runs the adversary, behind the secrecy layer (`flat`), against the native handler of the final split game `PqxdhDeploymentBackend.handlerWith (PqxdhDeploymentIdealDefer.idealSplit …)` on its own coins. `idealStep_bound` and the other component bills of `PqxdhDeploymentIdealEnvCost` bound the ideal environment's step in capability form, which `PqxdhDeploymentIdealEnv.ideal_splits` relates to the split form only in law; query bounds do not transfer along equalities in law, so this module proves the per-step bound of the split handler itself (plan sections 89 and 93 (a)), from the same premise `KemBound setup caps` and with the same component lemmas (`acceptExposed_cost` behind `acceptSelected_bound`, `preparationCE_step` and `markedRoot_uniform` behind `finishChallenge_bound`, `createPool_uniform`, `lazyDummy_bound` through `slotRun_total`).

- `splitWeight caps`: the per-command uniform weight by native command class (`PqxdhDeploymentCompileBudget.commandKind`): coin 1, create `64 + keygenCost`, bundle 32, accept `140 + encapsCost`, build `108 + 64 + 64`, finish `69 · max 64 decapsCost + 64`, HMAC, BLAKE2b and the four record commands 64.
- `splitStep_uniform`: every step of `handlerWith (idealSplit …)` from every extended state draws at most `splitWeight caps` of its class.
- The pieces. Native steps: `record_uniform`, `serverStep_uniform`, `beaconStep_uniform` (a record command makes at most one BLAKE2b request, 64 coins), `native_uniform` (the native deployment handler, `nativeCost`, from `PqxdhRegistrationSchedule.handler_uniform`), `later_uniform` (the LQ-F run-phase handler with the logged accept). Hidden services of `erasedHidden`: `rom_uniform`, `nativePrim_uniform`, `finishErased_uniform`, `hiddenAfter_uniform` (the hidden finish continuation: at most one opening, 64 coins), `tailImpl_uniform`, `loggedSend_uniform`, `hiddenBuild_uniform`, `buildHidden_uniform` (the marked build's response tail: at most one seal, 64 coins). Slot steps, weighted by `wSlot` (1 per coin, 108 per slot read): `slotRunX_uniform` (a slot step against the allocator in front of the lazy material service), `realRegAt_uniform`, `createReg_uniform`, `acceptStep_cost` (`140 + encapsCost`), `buildStepC_cost` (`108 + 64`), `groupCE_cost` (`108 + 64`), `ownerCE_cost`, `finishChallenge_cost` (`decapsCost + 108 + 64`), `challenge_le` (which is at most `69 · max 64 decapsCost`), `finishStepC_cost`; the hidden installs draw one 64-byte seed (`seed_uniform`, `seedQuery_uniform`, `xInstall_uniform`, `serverInstall_uniform`, `beaconInstall_uniform`); `splitBuild_uniform`, `splitFinish_uniform`.

These are resource bounds in the existing cost model (`KemBound` caps the primitive programs and the base interpreter); no assumption is added and no security claim is made.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentBackend (XState handlerWith)

section Records
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- A record program with at most one BLAKE2b request, run on the shared CTX cache of the registration state with the real ratchet KDF, AEAD and frame writer, draws at most 64 coins (`RawCtxMixedShared.shared_uniform`). -/
theorem record_uniform {Result : Type} (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (qKdf : ℕ)
    (kdfs : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .kdf) qKdf)
    (hashes : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) 1)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    ((PqxdhDeploymentNative.record setup codec work).run state).IsTotalQueryBound 64 := by
  have bound := RawCtxMixedShared.shared_uniform setup.source.crypto codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) 0 (fun request current => RawCtxSourceHkdf.kdf_uniform setup.source request
      current) work qKdf 1 kdfs hashes ((), state.shared.2.ctx)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_one] at bound
  change ((fun result => (result.1, { state with shared := result.2 })) <$>
    ((fun result => (result.1, (state.shared.1, { state.shared.2 with ctx := result.2.2 }))) <$>
      (simulateQ (PqxdhDeploymentNative.primitives setup codec) work).run ((), state.shared.2.ctx))).IsTotalQueryBound 64
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- A Server record command (send or raw receive) of the native deployment handler draws at most 64 coins: at most one BLAKE2b request (`PqxdhDeploymentCompileBudget.server_hashes`). -/
theorem serverStep_uniform (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    ((PqxdhDeploymentNative.serverStep setup codec route query).run state).IsTotalQueryBound 64 := by
  have hashes := PqxdhDeploymentCompileBudget.logged_bound _ _ 1 []
    (PqxdhDeploymentCompileBudget.server_hashes (PqxdhDeploymentNative.senderId state) route codec.frameRead query
      (PqxdhDeploymentNative.serverView state))
  have kdfs : ((RawCtxServerMixed.serverImpl (PqxdhDeploymentNative.senderId state) route codec.frameRead query).run
      (PqxdhDeploymentNative.serverView state)).IsQueryBoundP (fun request => RawCtxMixedOwner.callKind request = .kdf)
      51 := by
    rcases query with ⟨plaintext, kid⟩ | raw
    · exact (RawCtxServerMixed.send_bound _ plaintext kid _ .kdf).mono (by decide)
    · exact RawCtxServerMixed.raw_bound route codec.frameRead raw _ .kdf
  have record := record_uniform setup codec _ 51 (PqxdhDeploymentCompileBudget.logged_bound _ _ 51 [] kdfs) hashes
    state.native
  unfold PqxdhDeploymentNative.serverStep
  exact (isTotalQueryBound_bind record fun _ => (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial)).mono
    (by omega)

/-- A Beacon record command (send or raw receive) of the native deployment handler draws at most 64 coins: at most one BLAKE2b request (`PqxdhDeploymentCompileBudget.beacon_hashes`). -/
theorem beaconStep_uniform (index : ℕ) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhDeploymentNative.State KemSK) :
    ((PqxdhDeploymentNative.beaconStep setup codec index query).run state).IsTotalQueryBound 64 := by
  change (PqxdhDeploymentNative.beaconStep setup codec index query state).IsTotalQueryBound 64
  unfold PqxdhDeploymentNative.beaconStep
  split
  · trivial
  · rename_i owner _
    have hashes := PqxdhDeploymentCompileBudget.logged_bound _ _ 1 []
      (PqxdhDeploymentCompileBudget.beacon_hashes codec.frameRead query ⟨owner.beacon, state.ownerRaw index⟩)
    have kdfs : ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
        ⟨owner.beacon, state.ownerRaw index⟩).IsQueryBoundP (fun request => RawCtxMixedOwner.callKind request = .kdf) 51 := by
      have bound := RawCtxBeaconLifecycle.step_bound codec.frameRead query ⟨owner.beacon, state.ownerRaw index⟩ .kdf
      rcases query with plaintext | raw
      · exact bound.mono (by simp [RawCtxMixedOwner.sendCost])
      · exact bound
    have record := record_uniform setup codec _ 51 (PqxdhDeploymentCompileBudget.logged_bound _ _ 51 [] kdfs) hashes
      state.native
    exact (isTotalQueryBound_bind record fun _ => (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial)).mono
      (by omega)

end Records

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) (caps : KemCaps)
open PqxdhDeploymentCompileBudget (commandKind)

/-- The per-class uniform cost of one command of the native deployment handler (classes of `commandKind`). -/
def nativeCost (caps : KemCaps) : Fin 12 → ℕ :=
  ![1, 64 + caps.keygenCost, 32, 96 + caps.encapsCost, 64, 69 * max 64 caps.decapsCost, 64, 64, 64, 64, 64, 64]

/-- A registration-scheduler step run on the native deployment state keeps its coin bound. -/
theorem onNative_uniform {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α) (k : ℕ)
    (state : PqxdhDeploymentNative.State KemSK) (bound : (work.run state.native).IsTotalQueryBound k) :
    ((PqxdhDeploymentNative.onNative work).run state).IsTotalQueryBound k := by
  change ((fun result => (result.1, { state with native := result.2 })) <$> work.run state.native).IsTotalQueryBound k
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- Every command of the native deployment handler draws at most `nativeCost caps` of its class: the registration commands by `PqxdhRegistrationSchedule.handler_uniform` (a create with a wrong-width pin draws nothing), the record commands by `serverStep_uniform` and `beaconStep_uniform`. Premise: `KemBound setup caps`. -/
theorem native_uniform (bounded : KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : PqxdhDeploymentInterface.Spec.Domain) (state : PqxdhDeploymentNative.State KemSK) :
    ((PqxdhDeploymentNative.handler setup codec checks route seed query).run state).IsTotalQueryBound
      (nativeCost caps (commandKind query)) := by
  have schedule := fun request => PqxdhRegistrationSchedule.handler_uniform setup codec checks caps bounded seed 0
    request state.native
  rcases query with coin | command
  · simp [PqxdhDeploymentNative.handler, nativeCost, commandKind, StateT.run_lift, IsTotalQueryBound]
  · cases command with
    | create pin keyId =>
        change (match PqxdhDeploymentInterface.parsePin pin with
          | none => pure none
          | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.handler setup codec checks seed
              (.inr (.create word keyId)))).run state |>.IsTotalQueryBound _
        cases PqxdhDeploymentInterface.parsePin pin with
        | none => trivial
        | some word =>
            rw [StateT.run_map]
            simp only [IsTotalQueryBound, isQueryBound_map_iff]
            exact onNative_uniform _ _ state ((PqxdhRegistrationSchedule.create_uniform setup caps bounded word keyId
              state.native).mono (by simp [nativeCost, commandKind]))
    | bundle owner => exact onNative_uniform _ _ state ((schedule (.inr (.bundle owner))).mono
        (by simp [nativeCost, commandKind, PqxdhRegistrationSchedule.uniformCost, PqxdhRegistrationSchedule.sourceKind]))
    | accept raw => exact onNative_uniform _ _ state ((schedule (.inr (.accept raw))).mono
        (by simp [nativeCost, commandKind, PqxdhRegistrationSchedule.uniformCost, PqxdhRegistrationSchedule.sourceKind]))
    | build session payload => exact onNative_uniform _ _ state ((schedule (.inr (.build session payload))).mono
        (by simp [nativeCost, commandKind, PqxdhRegistrationSchedule.uniformCost, PqxdhRegistrationSchedule.sourceKind]))
    | finish owner raw => exact onNative_uniform _ _ state ((schedule (.inr (.finish owner raw))).mono
        (by simp [nativeCost, commandKind, PqxdhRegistrationSchedule.uniformCost, PqxdhRegistrationSchedule.sourceKind]))
    | hmac key message => exact onNative_uniform _ _ state ((schedule (.inr (.hmac key message))).mono
        (by simp [nativeCost, commandKind, PqxdhRegistrationSchedule.uniformCost, PqxdhRegistrationSchedule.sourceKind]))
    | hash bytes => exact onNative_uniform _ _ state ((schedule (.inr (.hash bytes))).mono
        (by simp [nativeCost, commandKind, PqxdhRegistrationSchedule.uniformCost, PqxdhRegistrationSchedule.sourceKind]))
    | serverSend keyId plaintext => exact serverStep_uniform setup codec route _ state
    | serverRaw raw => exact serverStep_uniform setup codec route _ state
    | beaconSend owner plaintext => exact beaconStep_uniform setup codec owner _ state
    | beaconRaw owner raw => exact beaconStep_uniform setup codec owner _ state

/-- Every command of the LQ-F run-phase handler draws at most `nativeCost caps` of its class: the logged accept (`PqxdhDeploymentEnvironment.acceptLogged_uniform`) for an accept, the native step otherwise. -/
theorem later_uniform (bounded : KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : PqxdhDeploymentInterface.Spec.Domain) (state : PqxdhDeploymentNative.State KemSK × PqxdhDeploymentLaterServerSource.Log) :
    ((PqxdhDeploymentLaterServerGame.handler setup codec checks route seed query).run state).IsTotalQueryBound
      (nativeCost caps (commandKind query)) := by
  have native : ∀ query', (∀ raw, query' ≠ .inr (.accept raw)) →
      ((PqxdhDeploymentLaterServerGame.handler setup codec checks route seed query').run state) =
        (fun result => (result.1, (result.2, state.2))) <$>
          (PqxdhDeploymentNative.handler setup codec checks route seed query').run state.1 := by
    intro query' other
    rcases query' with coin | command
    · rfl
    · cases command
      case accept raw => exact absurd rfl (other raw)
      all_goals rfl
  by_cases accept : ∃ raw, query = .inr (.accept raw)
  · obtain ⟨raw, rfl⟩ := accept
    change ((fun result => (result.1, ({ state.1 with native := result.2.1 }, result.2.2))) <$>
      ((fun result => (result.1.1, (result.2, state.2 ++ [result.1.2]))) <$>
        (PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed
          raw)).run state.1.native)).IsTotalQueryBound _
    have logged := (PqxdhDeploymentEnvironment.acceptLogged_uniform setup codec checks caps bounded seed raw
      state.1.native).mono (show 96 + caps.encapsCost ≤ nativeCost caps (commandKind (.inr (.accept raw))) by
        simp [nativeCost, commandKind])
    simp only [IsTotalQueryBound, isQueryBound_map_iff] at logged ⊢
    exact logged
  · rw [native query fun raw same => accept ⟨raw, same⟩]
    have bound := native_uniform setup codec route checks caps bounded seed query state.1
    simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
    exact bound

end Native

section Hidden
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhRegistrationJointKemRootCosts (WBound wBound_pure wBound_bind wBound_map wBound_mono wBound_query
  wBound_query_bind wBound_run wBound_of_total wBound_of_isQueryBoundP wBound_weight_mono)

/-- A program with at most `n` BLAKE2b queries, run against the lazily sampled 64-byte BLAKE2b cache, draws at most `64 * n` coins. -/
theorem rom_uniform {α : Type} (work : OracleComp CtxRomAuth.CtxRO α) (n : ℕ) (bounded : work.IsTotalQueryBound n)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    ((simulateQ CtxRomAuth.ctxRandomOracle work).run cache).IsTotalQueryBound (64 * n) := by
  have weighted := wBound_of_isQueryBoundP (fun _ => True) 64 ((isQueryBoundP_true_iff work n).mpr bounded)
  have flat : WBound work (fun _ => 64) (64 * n) := wBound_weight_mono (fun _ => by simp) weighted
  exact PqxdhDeploymentIdealEnvCost.total_of_wBound (wBound_run _ (fun _ => 64) (fun _ => 1)
    (fun query current => wBound_of_total (CtxComputationalSecurity.ctxRandomOracle_total_query_bound query current))
    flat cache)

/-- The native Beacon primitive interpreter draws at most 64 coins per request: none for a KDF request, at most one BLAKE2b digest for an opening. -/
theorem nativePrim_uniform (query : RawCtxWholeOwner.PrimitiveSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState Unit) :
    ((PqxdhServerAuthBeaconFactor.nativePrim setup codec query).run state).IsTotalQueryBound 64 := by
  rcases query with request | input
  · rw [PqxdhServerAuthBeaconFactor.native_kdf]
    trivial
  · rw [PqxdhDeploymentHiddenKernels.nativePrim_open]
    change ((fun r => (r.1, PqxdhDeploymentHiddenKernels.ctxLens.set state r.2)) <$>
      (simulateQ CtxRomAuth.ctxRandomOracle (simulateQ (RawCtxSourceOpen.romAdapter setup.source.crypto)
        (RawCtxSourceOpen.openInput input))).run (PqxdhDeploymentHiddenKernels.ctxLens.get state)).IsTotalQueryBound 64
    have bound := rom_uniform _ 1 (PqxdhDeploymentHiddenEntry.opening_hash_bound setup.source.crypto input)
      (PqxdhDeploymentHiddenKernels.ctxLens.get state)
    simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
    exact bound

/-- The erased hidden finish tail with the native primitives draws at most 64 coins: the finish-time receive makes at most one opening request (`PqxdhDeploymentHiddenEntry.requests_bound`), each at most one BLAKE2b digest. -/
theorem finishErased_uniform (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : PqxdhServerAuthSendFactor.Factor) (state : RawCtxSharedPrimitive.SharedState Unit) :
    ((PqxdhDeploymentHiddenKernels.finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response)) codec.frameRead
      prepared value).run state).IsTotalQueryBound 64 := by
  unfold PqxdhDeploymentHiddenKernels.finishErased
  rw [StateT.run_bind, StateT.run_pure, pure_bind]
  cases codec.application prepared.response with
  | none => trivial
  | some raw =>
      dsimp only
      split
      · rw [StateT.run_map, PqxdhDeploymentHiddenEntry.factoredBody_requests, StateT.run_map]
        have requests := (PqxdhDeploymentHiddenEntry.requests_bound codec.frameRead prepared value raw).2
        have weighted := wBound_of_isQueryBoundP _ 64 requests
        have step : ∀ request current, WBound ((PqxdhServerAuthBeaconFactor.primLabels
            (PqxdhServerAuthBeaconFactor.nativePrim setup codec) setup.source value.1 request).run current) (fun _ => 1)
            (if request.isRight = true then 64 else 0) := by
          intro request current
          rcases request with slot | opening
          · simp only [PqxdhServerAuthBeaconFactor.primLabels, StateT.run_pure]
            exact wBound_pure _ _ _
          · simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, RawCtxWholeOwner.adapter,
              Sum.isRight_inr, ite_true]
            split
            · simp only [simulateQ_pure, StateT.run_pure]
              exact wBound_pure _ _ _
            · simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
              exact wBound_mono (wBound_bind (a := 64) (b := 0) (wBound_of_total (nativePrim_uniform setup codec _ _))
                fun _ _ => wBound_pure _ _ _) (by omega)
        have bound := PqxdhDeploymentIdealEnvCost.total_of_wBound (wBound_run _ _ (fun _ => 1) step weighted state)
        simp only [Nat.mul_one, IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
        exact bound
      · trivial

/-- The erased hidden finish (the Beacon continuation of `erasedHidden`) draws at most 64 coins. -/
theorem hiddenAfter_uniform (value : PqxdhServerAuthKeySchedule.Output)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (state : RawCtxSharedPrimitive.SharedState Unit) :
    (((PqxdhDeploymentIdealSteps.erasedHidden setup codec checks value).hiddenAfter pending).run state).IsTotalQueryBound
      64 := by
  change (Prod.fst <$> PqxdhDeploymentHiddenKernels.finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
    (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response)) codec.frameRead
    (PqxdhPhase2DhRootConsumer.cleared pending) _).run state |>.IsTotalQueryBound 64
  rw [StateT.run_map]
  have bound := finishErased_uniform setup codec (PqxdhPhase2DhRootConsumer.cleared pending)
    (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput
      (PqxdhDeploymentHiddenLayout.splitOutput value).1 (PqxdhDeploymentHiddenLayout.splitOutput value).2)) state
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- One callback of the logged Server response tail draws at most 64 coins, and only a seal draws any. -/
theorem tailImpl_uniform (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    ((PqxdhServerAuthExperiment.tailImpl setup codec checks query).run state).IsTotalQueryBound
      (if PqxdhServerRegistrationPublication.callKind query = .seal then 64 else 0) := by
  have forget := PqxdhServerAuthExperiment.tail_native setup codec checks
    (liftM (PqxdhServerRegistrationPublication.TailSpec.query query)) state
  simp only [simulateQ_spec_query] at forget
  have seals : (liftM (PqxdhServerRegistrationPublication.TailSpec.query query) :
      OracleComp PqxdhServerRegistrationPublication.TailSpec _).IsQueryBoundP
      (fun request => PqxdhServerRegistrationPublication.callKind request = .seal)
      (if PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) :=
    (isQueryBoundP_query_iff _ _ _).mpr fun found => by simp only [found, ite_true, Nat.one_pos]
  have hashes := PqxdhServerRegistrationPublication.native_seal_bound _ _ seals .hash
  simp only [simulateQ_spec_query] at hashes
  have bound := PqxdhServerAuthTailCosts.registration_uniform setup codec checks _ _ hashes
    (PqxdhServerAuthExperiment.forgetAux state)
  rw [IsTotalQueryBound, ← isQueryBound_map_iff (f := Prod.map id PqxdhServerAuthExperiment.forgetAux), forget,
    ← IsTotalQueryBound]
  exact bound.mono (by split <;> simp)

/-- One send of the logged factored Server build draws at most 64 coins: at most one seal (`program_seal_bound`). -/
theorem loggedSend_uniform (challenge : RatchetKdfResponse) (entry : RawCtxSelectedChain.Kernel)
    (context : RawCtxSourceSend.SealContext)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (((PqxdhServerAuthLoggedSendFactor.calls (fun entry _ _ => pure (entry, .None))
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source challenge).send entry context).run
        state).IsTotalQueryBound 64 := by
  change ((simulateQ (PqxdhServerAuthSendFactor.primLabels (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks)
      setup.source challenge) (RawCtxChainSend.execute entry context)).run state).IsTotalQueryBound 64
  have seals := wBound_of_isQueryBoundP _ 64 (RawCtxChainSend.program_seal_bound (Output := RawCtxSourceSend.Encrypted)
    (RawCtxChainSend.normalBegin entry context))
  have step : ∀ request current, WBound ((PqxdhServerAuthSendFactor.primLabels
      (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source challenge request).run current)
      (fun _ => 1) (if request.isRight = true then 64 else 0) := by
    intro request current
    rcases request with slot | pending
    · simp only [PqxdhServerAuthSendFactor.primLabels, StateT.run_pure]
      exact wBound_pure _ _ _
    · simp only [PqxdhServerAuthSendFactor.primLabels, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, Sum.isRight_inr,
        ite_true]
      have sealed := tailImpl_uniform setup codec checks (.inl (.inr (RawCtxSourceSend.arguments
        (RawCtxInterpretedSend.nativeSeal (RawCtxChainSend.nativeSeal (fun _ => RawCtxSelectedChain.unusedChain)
          (fun _ => RawCtxSelectedChain.unusedChain) pending))))) current
      simp only [PqxdhServerRegistrationPublication.callKind, ite_true] at sealed
      exact wBound_mono (wBound_bind (a := 64) (b := 0) (wBound_of_total sealed) fun _ _ => wBound_pure _ _ _)
        (by omega)
  have bound := PqxdhDeploymentIdealEnvCost.total_of_wBound (wBound_run _ _ (fun _ => 1) step seals state)
  simp only [Nat.mul_one] at bound
  exact bound

/-- The logged factored Server build of `erasedHidden` (the marked build's response tail) draws at most 64 coins. -/
theorem hiddenBuild_uniform (value : PqxdhServerAuthKeySchedule.Output)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (((PqxdhDeploymentIdealSteps.erasedHidden setup codec checks value).hiddenBuild token payload server).run
      state).IsTotalQueryBound 64 := by
  change ((PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
    (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) setup.source
    (PqxdhServerAuthLoggedSendFactor.loggedAux setup codec checks)
    (PqxdhServerAuthCtxMaterial.factor value) token.pending payload () server).run state).IsTotalQueryBound 64
  refine (isQueryBoundP_true_iff _ _).mp ?_
  simp only [PqxdhServerAuthLoggedSendFactor.factored, StateT.run_map, isQueryBoundP_map_iff]
  exact PqxdhDeploymentEnvironment.generic_build_bound (fun _ => True) _ _ 64
    (fun entry context current => (isQueryBoundP_true_iff _ _).mpr (loggedSend_uniform setup codec checks _ entry context
      current))
    (fun query current => (isQueryBoundP_true_iff _ _).mpr ((tailImpl_uniform setup codec checks (.inr query)
      current).mono (by cases query <;> simp [PqxdhServerRegistrationPublication.callKind,
        PqxdhServerRegistrationPublication.auxKind]))) _ _ _ _ _ state

end Hidden

section Slots
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) (caps : KemCaps) {count : ℕ}
open PqxdhRegistrationJointKemRootCosts (WBound wBound_pure wBound_bind wBound_map wBound_mono wBound_query
  wBound_query_bind wBound_run wBound_simulate wBound_of_total wBound_of_isQueryBoundP wBound_weight_mono)
open PqxdhDeploymentIdealEnvCost (wSlot liftS_cost total_of_wBound)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk erasedHidden onSlots)
open PqxdhDeploymentIdealKernel (slotRunX lazyDummy)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhServerAuthNative (NativeState)

/-- A step of the native deployment state run on the extended state keeps its coin bound. -/
theorem onBase_uniform {Bk : Type} {n : ℕ} {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (k : ℕ) (x : XState KemSK Bk n) (bound : (step.run x.base).IsTotalQueryBound k) :
    ((PqxdhDeploymentBackend.onBase step).run x).IsTotalQueryBound k := by
  change ((fun r => (r.1, PqxdhDeploymentBackend.baseLens.set x r.2)) <$> step.run x.base).IsTotalQueryBound k
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- A shared-state step run on the CTX cache keeps its coin bound. -/
theorem nativeCtx_uniform {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) (k : ℕ)
    (s : NativeState KemSK) (bound : (work.run ((), s.2.ctx)).IsTotalQueryBound k) :
    ((PqxdhServerAuthNative.nativeCtx work).run s).IsTotalQueryBound k := by
  change ((fun result => (result.1, (s.1, { s.2 with ctx := result.2.2 }))) <$> work.run ((), s.2.ctx)).IsTotalQueryBound k
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- A slot step whose every run is within `n` slot-weighted requests, run against the allocator in front of the lazy material service on the extended state, draws at most `n` coins. -/
theorem slotRunX_uniform {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β)
    (n : ℕ) (bounded : ∀ y, WBound (step.run y) wSlot n) (x : XState KemSK SplitBk 2) :
    ((slotRunX lazyDummy step).run x).IsTotalQueryBound n := by
  change ((fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair lazyDummy step).run
      (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))).IsTotalQueryBound n
  rw [PqxdhDeploymentIdealErase.onPair_run]
  have bound := PqxdhDeploymentIdealEnvCost.slotRun_total _ n (bounded (PqxdhDeploymentIdealKeys.detachX x))
    (x.backend.2.1, (x.backend.1, x.seeds))
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- A registration command of the real handler on any extended state: the LQ-F run-phase handler's cost. -/
theorem realRegAt_uniform (bounded : KemBound setup caps) {Bk : Type} {n : ℕ}
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhRecordLiftInterface.EnvQuery)
    (x : XState KemSK Bk n) :
    ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created query).run x).IsTotalQueryBound
      (nativeCost caps (commandKind (.inr query.val))) := by
  have bound := later_uniform setup codec route checks caps bounded created.seed (.inr query.val) (x.base, x.log)
  change (_ <$> (PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr query.val)).run
    (x.base, x.log)).IsTotalQueryBound _
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- The pool create draws at most `64 + keygenCost` coins on any extended state. -/
theorem createReg_uniform (bounded : KemBound setup caps) {Γ : Type} {n : ℕ}
    (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) (x : XState KemSK Γ n) :
    ((PqxdhDeploymentIdealSteps.createReg setup pool pin keyId).run x).IsTotalQueryBound (64 + caps.keygenCost) := by
  unfold PqxdhDeploymentIdealSteps.createReg
  refine onBase_uniform _ _ x ?_
  split
  · trivial
  · rename_i word _
    rw [StateT.run_map]
    have bound := onNative_uniform _ _ x.base (PqxdhDeploymentIdealEnvCost.createPool_uniform setup caps bounded pool word
      keyId x.base.native)
    simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
    exact bound

/-- The marked build with the erased hidden services draws at most 64 coins (`hiddenBuild_uniform`). -/
theorem buildHidden_uniform (value : PqxdhServerAuthKeySchedule.Output) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (shared : NativeState KemSK) :
    ((PqxdhDeploymentIdealSteps.buildHidden (erasedHidden setup codec checks value) session payload).run
      shared).IsTotalQueryBound 64 := by
  simp only [PqxdhDeploymentIdealSteps.buildHidden, StateT.run_bind]
  simp only [StateT.run, PqxdhServerAuthNative.nativeGet, PqxdhServerAuthNative.localState, pure_bind]
  cases found : shared.2.pending session with
  | none => trivial
  | some token =>
      change ((PqxdhServerAuthNative.nativeCoins _ >>= _).run shared).IsTotalQueryBound 64
      simp only [StateT.run_bind, StateT.run_pure]
      simp only [StateT.run, PqxdhServerAuthNative.nativeCoins, PqxdhServerAuthNative.nativeSet,
        PqxdhServerAuthNative.localState, map_pure, bind_pure_comp]
      have bound := hiddenBuild_uniform setup codec checks value token payload shared.2.server ([], shared.2.ctx)
      simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
      exact bound

/-- One 64-byte hidden seed draws 64 coins. -/
theorem seed_uniform : ($ᵗ PqxdhRecordLiftSeed.Seed : ProbComp PqxdhRecordLiftSeed.Seed).IsTotalQueryBound 64 := by
  simp only [← PqxdhFullSecretInputKdf.pairSample]
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun left =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun right =>
      show (pure (left, right) : ProbComp PqxdhRecordLiftSeed.Seed).IsTotalQueryBound 0 from by trivial))

/-- A lazy read of the hidden-seed table draws at most 64 coins. -/
theorem seedQuery_uniform {Bk : Type} (j : PqxdhRecordLiftInterface.Slot 2) (x : XState KemSK Bk 2) :
    ((PqxdhDeploymentBackend.seedLens.query j).run x).IsTotalQueryBound 64 := by
  change ((fun r => (r.1, PqxdhDeploymentBackend.seedLens.set x r.2)) <$>
    ((PqxdhRecordLiftWorld.SeedSpec 2).randomOracle j).run (PqxdhDeploymentBackend.seedLens.get x)).IsTotalQueryBound 64
  simp only [IsTotalQueryBound, isQueryBound_map_iff]
  cases cached : (PqxdhDeploymentBackend.seedLens (KemSK := KemSK) (Bk := Bk) (n := 2)).get x j with
  | none =>
      rw [LazyOracleDiscard.query_of_none cached, bind_pure_comp]
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using seed_uniform
  | some seed =>
      rw [LazyOracleDiscard.query_of_some cached]
      trivial

/-- A hidden install of the final split form draws at most one seed: 64 coins. -/
theorem xInstall_uniform {β : Type} (coords : β × XState KemSK IdealCore 2 → Option PqxdhDeploymentIdealSlots.Coord)
    (gate : β × XState KemSK IdealCore 2 → Bool)
    (apply : PqxdhRecordLiftSeed.Seed → β × XState KemSK IdealCore 2 → β × XState KemSK IdealCore 2)
    (r : β × XState KemSK SplitBk 2) :
    (PqxdhDeploymentIdealDefer.xInstall coords gate apply r).IsTotalQueryBound 64 := by
  unfold PqxdhDeploymentIdealDefer.xInstall
  split
  · trivial
  · split
    · trivial
    · split
      · rename_i j _ _
        have bound := seedQuery_uniform j r.2
        simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
        exact bound
      · trivial

/-- A probabilistic step lifted to a slot client costs its coins. -/
theorem onSlots_cost {σ α : Type} (step : StateT σ ProbComp α) (n : ℕ) (state : σ)
    (bounded : (step.run state).IsTotalQueryBound n) :
    WBound ((onSlots step).run state) wSlot n :=
  liftS_cost _ n bounded

/-- The raw accept of the ideal registration costs at most `140 + encapsCost` slot-weighted requests: the selected accept (`acceptExposed_cost`) or the real logged accept. -/
theorem acceptStep_cost (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) (x : XState KemSK IdealCore 2) :
    WBound ((PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run x) wSlot
      (140 + caps.encapsCost) := by
  change WBound (if x.backend.accepts = t.accept then _ else _) _ _
  split
  · exact wBound_map _ (PqxdhDeploymentIdealEnvCost.acceptExposed_cost setup codec checks caps bounded _ _ _ _ _)
  · exact wBound_mono (onSlots_cost _ _ _ (realRegAt_uniform setup codec route checks caps bounded created
      ⟨.accept raw, trivial⟩ _)) (by simp [nativeCost, commandKind])

/-- The build of the ideal registration with the erased hidden services costs at most `108 + 64` slot-weighted requests: the marked build's slot read and its hidden response tail, or the real build. -/
theorem buildStepC_cost (bounded : KemBound setup caps) (created : PqxdhLiveServerConstruction.Created Unit)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (x : XState KemSK IdealCore 2) :
    WBound ((PqxdhDeploymentIdealKernel.buildStepC setup codec checks route (erasedHidden setup codec checks) created
      session payload).run x) wSlot (108 + 64) := by
  have real : WBound ((fun r => ((r.1, none), r.2)) <$> (onSlots (PqxdhDeploymentIdealSteps.realRegAt setup codec route
      checks created ⟨.build session payload, trivial⟩)).run x : OracleComp PqxdhDeploymentIdealSlots.SlotSpec
        ((Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
          XState KemSK IdealCore 2)) wSlot (108 + 64) :=
    wBound_mono (wBound_map _ (onSlots_cost _ _ _ (realRegAt_uniform setup codec route checks caps bounded created
      ⟨.build session payload, trivial⟩ _))) (by simp [nativeCost, commandKind])
  unfold PqxdhDeploymentIdealKernel.buildStepC
  simp only [StateT.run]
  split
  · split
    · rename_i index coords _ _
      unfold PqxdhDeploymentIdealKernel.buildHiddenC
      have h := PqxdhDeploymentIdealErase.readAt_bind_run coords (fun value => onSlots ((fun r => (r, some coords)) <$>
        PqxdhDeploymentIdealErase.buildFocus (erasedHidden setup codec checks value) session payload coords)) x
      simp only [StateT.run] at h
      rw [h]
      refine wBound_bind ((wBound_query _ _ _).mpr le_rfl) fun value _ => ?_
      refine onSlots_cost _ 64 x ?_
      rw [StateT.run_map]
      have bound := buildHidden_uniform setup codec checks value session payload x.base.native.shared
      change (_ <$> (_ <$> (PqxdhDeploymentIdealSteps.buildHidden (erasedHidden setup codec checks value) session
        payload).run x.base.native.shared)).IsTotalQueryBound 64
      simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
      exact bound
    · exact real
  · exact real

/-- The grouped finish request of owner k with the erased hidden services costs at most `108 + 64` slot-weighted requests: a slot read and the hidden continuation, or the native root and the native continuation after it. -/
theorem groupCE_cost (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response)
    (s : NativeState KemSK × Option PqxdhDeploymentIdealSlots.Coord) :
    WBound ((PqxdhDeploymentIdealSteps.groupCE setup codec (erasedHidden setup codec checks) pending).run s) wSlot
      (108 + 64) := by
  unfold PqxdhDeploymentIdealSteps.groupCE
  dsimp only
  split
  · split
    · refine wBound_bind ((wBound_query _ _ _).mpr le_rfl) fun value _ => ?_
      rw [← Nat.add_zero 64]
      exact wBound_bind (liftS_cost _ 64 (nativeCtx_uniform _ 64 s.1 (hiddenAfter_uniform setup codec checks value _ _)))
        fun _ _ => wBound_pure _ _ _
    · exact wBound_pure _ _ _
  · refine wBound_mono (wBound_map _ (liftS_cost _ (64 + 64) ?_)) (by omega)
    simp only [StateT.run_bind]
    refine isTotalQueryBound_bind (PqxdhDeploymentIdealEnvCost.markedRoot_uniform setup.hmac _ _ s.1) fun r => ?_
    rcases r with ⟨_ | root, after⟩
    · exact (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial).mono (Nat.zero_le _)
    · dsimp only
      refine nativeCtx_uniform _ 64 after ?_
      rw [PqxdhRegistrationJointKemPostSkeleton.afterRoot_embed]
      exact PqxdhServerAuthTailCosts.beacon_after_uniform setup codec _ root _

/-- The weights of the grouped owner's requests: a preparation request its decapsulation weight, the grouped finish request `108 + 64`. -/
def wOwner (caps : KemCaps) : (PqxdhDeploymentIdealSteps.OwnerSpecCE KemSK Response).Domain → ℕ
  | .inl query => PqxdhRegistrationJointKemRootCosts.wPrep caps query
  | .inr _ => 108 + 64

/-- Owner k's grouped native finish under the CE-native interpreter costs at most `decapsCost + 108 + 64` slot-weighted requests: one decapsulation in its preparation and one grouped finish request. -/
theorem ownerCE_cost (bounded : KemBound setup caps) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (s : NativeState KemSK × Option PqxdhDeploymentIdealSlots.Coord) :
    WBound ((simulateQ (PqxdhDeploymentIdealSteps.ownerImplCE setup codec (erasedHidden setup codec checks) challenge)
      (PqxdhDeploymentIdealSteps.groupedOwnerCE raw owner)).run s) wSlot (caps.decapsCost + (108 + 64)) := by
  have source : WBound (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw owner) (wOwner caps)
      (caps.decapsCost + (108 + 64)) := by
    unfold PqxdhDeploymentIdealSteps.groupedOwnerCE
    split
    · refine wBound_bind (wBound_simulate _ (PqxdhRegistrationJointKemRootCosts.wPrep caps) (wOwner caps)
        (fun query => (wBound_query _ _ _).mpr le_rfl) (PqxdhRegistrationJointKemRootCosts.prepare_cost caps _ _ _ _ _
          raw)) fun prepared _ => ?_
      split
      · exact wBound_pure _ _ _
      · rw [← Nat.add_zero (108 + 64)]
        exact wBound_bind ((wBound_query _ _ _).mpr le_rfl) fun _ _ => wBound_pure _ _ _
    · exact wBound_pure _ _ _
  refine wBound_run _ (wOwner caps) wSlot (fun query state => ?_) source s
  rcases query with query | pending
  · exact wBound_map _ (liftS_cost _ _ (total_of_wBound (PqxdhDeploymentIdealEnvCost.preparationCE_step setup codec caps
      bounded challenge query)))
  · exact groupCE_cost setup codec checks pending state

/-- Owner k's challenge finish with the erased hidden services costs at most `decapsCost + 108 + 64` slot-weighted requests. -/
theorem finishChallenge_cost (bounded : KemBound setup caps) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (index : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK × Option PqxdhDeploymentIdealSlots.Coord) :
    WBound ((PqxdhDeploymentIdealSteps.finishChallenge setup codec (erasedHidden setup codec checks) challenge index
      raw).run state) wSlot (caps.decapsCost + (108 + 64)) := by
  unfold PqxdhDeploymentIdealSteps.finishChallenge
  simp only [StateT.run]
  split
  · exact wBound_pure _ _ _
  · rw [← Nat.add_zero (caps.decapsCost + (108 + 64))]
    exact wBound_bind (ownerCE_cost setup codec checks caps bounded challenge raw _ _) fun _ _ => wBound_pure _ _ _

/-- The challenge finish is within the real finish's bill: `decapsCost + 108 + 64 ≤ 69 · max 64 decapsCost`. -/
theorem challenge_le (caps : KemCaps) : caps.decapsCost + (108 + 64) ≤ 69 * max 64 caps.decapsCost := by
  have left := Nat.le_max_left 64 caps.decapsCost
  have right := Nat.le_max_right 64 caps.decapsCost
  omega

/-- The finish of the ideal registration with the erased hidden services costs at most `69 · max 64 decapsCost` slot-weighted requests: owner k's challenge finish or the real finish. -/
theorem finishStepC_cost (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK IdealCore 2) :
    WBound ((PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p (erasedHidden setup codec checks) created
      owner raw).run x) wSlot (69 * max 64 caps.decapsCost) := by
  unfold PqxdhDeploymentIdealKernel.finishStepC
  simp only [StateT.run]
  split
  · unfold PqxdhDeploymentIdealKernel.finishHiddenC
    exact wBound_mono (wBound_map _ (finishChallenge_cost setup codec checks caps bounded _ _ _ _)) (challenge_le caps)
  · exact wBound_map _ (onSlots_cost _ _ _ (realRegAt_uniform setup codec route checks caps bounded created
      ⟨.finish owner raw, trivial⟩ _))

end Slots

section Split
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) (caps : KemCaps) {count : ℕ}
open PqxdhDeploymentIdealSteps (IdealCore SplitBk erasedHidden onSlots idealProg)
open PqxdhDeploymentIdealKernel (slotRunX lazyDummy)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhRegistrationJointKemRootCosts (WBound)

/-- The per-command uniform weight of the anomaly guesser's split handler `handlerWith (idealSplit …)`, by native command class (`PqxdhDeploymentCompileBudget.commandKind`): coin 1; create `64 + keygenCost` (the pool create); bundle 32; accept `140 + encapsCost` (the selected accept: its ephemeral, one slot read and, inactive, the logged accept's encapsulation); build `108 + 64 + 64` (the marked build's slot read, its response tail's BLAKE2b digest and the hidden Server install's seed); finish `69 · max 64 decapsCost + 64` (the real finish, which covers owner k's challenge finish, and the hidden Beacon install's seed); HMAC, BLAKE2b and the four record commands 64. -/
def splitWeight (caps : KemCaps) : Fin 12 → ℕ :=
  ![1, 64 + caps.keygenCost, 32, 140 + caps.encapsCost, 108 + 64 + 64, 69 * max 64 caps.decapsCost + 64, 64, 64, 64,
    64, 64, 64]

/-- The hidden Server install of the final split form draws at most one seed: 64 coins. -/
theorem serverInstall_uniform
    (r : (Option PqxdhServerRegistrationPublication.Response × Option PqxdhDeploymentIdealSlots.Coord) ×
      XState KemSK SplitBk 2) :
    (PqxdhDeploymentIdealDefer.serverInstall r).IsTotalQueryBound 64 :=
  xInstall_uniform _ _ _ r

/-- The hidden Beacon install of the final split form draws at most one seed: 64 coins. -/
theorem beaconInstall_uniform (owner : ℕ)
    (r : (Option Pqxdh.Bytes × Option PqxdhDeploymentIdealSlots.Coord) × XState KemSK SplitBk 2) :
    (PqxdhDeploymentIdealDefer.beaconInstall owner r).IsTotalQueryBound 64 :=
  xInstall_uniform _ _ _ r

/-- The build of the final split form: the build with its coordinates, then the hidden Server install. -/
theorem splitBuild_uniform (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes)
    (x : XState KemSK SplitBk 2) :
    ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created ⟨.build session payload, trivial⟩).run
      x).IsTotalQueryBound (108 + 64 + 64) := by
  change ((fun r => (r.1.1, r.2)) <$> ((slotRunX lazyDummy (PqxdhDeploymentIdealKernel.buildStepC setup codec checks
    route (erasedHidden setup codec checks) created session payload)).run x >>=
      PqxdhDeploymentIdealDefer.serverInstall)).IsTotalQueryBound _
  have bound := isTotalQueryBound_bind (slotRunX_uniform _ _ (fun y => buildStepC_cost setup codec route checks caps
    bounded created session payload y) x) (fun r => serverInstall_uniform r)
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- The finish of the final split form: the finish with its coordinates, then the hidden Beacon install. -/
theorem splitFinish_uniform (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK SplitBk 2) :
    ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created ⟨.finish owner raw, trivial⟩).run
      x).IsTotalQueryBound (69 * max 64 caps.decapsCost + 64) := by
  change ((fun r => (r.1.1, r.2)) <$> ((slotRunX lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks
    route t p (erasedHidden setup codec checks) created owner raw)).run x >>=
      PqxdhDeploymentIdealDefer.beaconInstall owner)).IsTotalQueryBound _
  have bound := isTotalQueryBound_bind (slotRunX_uniform _ _ (fun y => finishStepC_cost setup codec route checks caps
    bounded t p created owner raw y) x) (fun r => beaconInstall_uniform owner r)
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
  exact bound

/-- `splitStep_uniform` (design-v2 section 9): every step of the anomaly guesser's split handler `handlerWith (idealSplit …)` draws at most the weight `splitWeight caps` of its native command class, from every extended state. Premise: `KemBound setup caps`. -/
theorem splitStep_uniform (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) :
    ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
      query).run x).IsTotalQueryBound (splitWeight caps (commandKind query)) := by
  have core : ∀ (command : PqxdhDeploymentInterface.Command) (allowed : PqxdhRecordLiftInterface.IsEnvironment command)
      (k : ℕ), (∀ y, WBound ((idealProg setup codec route checks t p (erasedHidden setup codec checks) created
        ⟨command, allowed⟩).run y) PqxdhDeploymentIdealEnvCost.wSlot k) →
      ((PqxdhDeploymentIdealKeys.slotCoreX (idealProg setup codec route checks t p (erasedHidden setup codec checks))
        lazyDummy created ⟨command, allowed⟩).run x).IsTotalQueryBound k := by
    intro command allowed k bounded'
    rw [PqxdhDeploymentIdealKernel.slotCoreX_run]
    exact slotRunX_uniform _ k bounded' x
  rcases query with coin | command
  · simp [handlerWith, splitWeight, commandKind, StateT.run_lift, IsTotalQueryBound]
  · cases command with
    | create pin keyId =>
        exact core (.create pin keyId) trivial _ fun y => onSlots_cost _ _ y (createReg_uniform setup caps bounded _ pin keyId y)
    | bundle owner =>
        exact core (.bundle owner) trivial _ fun y => onSlots_cost _ _ y (realRegAt_uniform setup codec route checks caps
          bounded created ⟨.bundle owner, trivial⟩ y)
    | accept raw =>
        exact core (.accept raw) trivial _ fun y => acceptStep_cost setup codec route checks caps bounded t p created raw y
    | build session payload => exact splitBuild_uniform setup codec route checks caps bounded t p created session payload x
    | finish owner raw => exact splitFinish_uniform setup codec route checks caps bounded t p created owner raw x
    | hmac key message =>
        exact core (.hmac key message) trivial _ fun y => onSlots_cost _ _ y (realRegAt_uniform setup codec route checks
          caps bounded created ⟨.hmac key message, trivial⟩ y)
    | hash bytes => exact onBase_uniform _ _ x (native_uniform setup codec route checks caps bounded created.seed
        (.inr (.hash bytes)) x.base)
    | serverSend keyId plaintext => exact onBase_uniform _ _ x (serverStep_uniform setup codec route _ x.base)
    | serverRaw raw => exact onBase_uniform _ _ x (serverStep_uniform setup codec route _ x.base)
    | beaconSend owner plaintext => exact onBase_uniform _ _ x (beaconStep_uniform setup codec owner _ x.base)
    | beaconRaw owner raw => exact onBase_uniform _ _ x (beaconStep_uniform setup codec owner _ x.base)

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.record_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.record_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.serverStep_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.serverStep_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.beaconStep_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.beaconStep_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.onNative_uniform' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.onNative_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.native_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.later_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.later_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.rom_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.rom_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.nativePrim_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.nativePrim_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.finishErased_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.finishErased_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.hiddenAfter_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.hiddenAfter_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.tailImpl_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.tailImpl_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.loggedSend_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.loggedSend_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.hiddenBuild_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.hiddenBuild_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.onBase_uniform' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.onBase_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.nativeCtx_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.nativeCtx_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.slotRunX_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.slotRunX_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.realRegAt_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.realRegAt_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.createReg_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.createReg_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.buildHidden_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.buildHidden_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.seed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.seed_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.seedQuery_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.seedQuery_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.xInstall_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.xInstall_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.onSlots_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.onSlots_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.acceptStep_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.acceptStep_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.buildStepC_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.buildStepC_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.groupCE_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.groupCE_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.ownerCE_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.ownerCE_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.finishChallenge_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.finishChallenge_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.challenge_le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.challenge_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.finishStepC_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.finishStepC_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.serverInstall_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.serverInstall_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.beaconInstall_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.beaconInstall_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.splitBuild_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.splitBuild_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.splitFinish_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.splitFinish_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.splitStep_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost.splitStep_uniform
