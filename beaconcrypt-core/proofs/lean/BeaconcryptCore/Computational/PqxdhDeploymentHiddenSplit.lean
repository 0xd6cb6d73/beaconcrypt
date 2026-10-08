-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenEntry
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld

/-!
# Split forms of the hidden-entry wrappers and their kernel identities

The factor-form hidden build and finish (`PqxdhDeploymentHiddenEntry.buildFactor` and the erased finish `finishErasedSvc`) consume the 108 bytes `joinOutput m seed` of a hidden slot. This module shows that they read the world seed (next32, right32) only through the kernel they publish or stage, and that this kernel is exactly the record world's kernel of the seed (critique M3 and m4). The split forms `buildSplit m` and `finishSplit m` run the same programs on the environment material `m` alone, with a fixed seed, and publish or stage a fixed `placeholderKernel`; `build_factor_split` and `finish_factor_split` state that the factor forms equal the split forms with the World's Server or Beacon kernel of the seed put in place of the placeholder.

The proofs read every chain label as the unused chain. The first send of the hidden Server and the sequence-one receive of the hidden Beacon each make exactly one key derivation on the hidden slot, answered by the selected step of the 76-byte response, whose material (key32, nonce12) does not depend on the next chain (`decode_full`, `material_assemble`). With the chain labels read as the unused chain, the native admission and continuation (`RawCtxChainSend.normalBegin_native`, `RawCtxChainReceive.normalBegin_native`, `normalResume_native`) show that the seal of the first send and the opening of the receive depend only on that material and on fields that do not hold a chain (`seal_unused`, `opening_unused`), so the sealed record and the opened reply are the same programs for every seed (`send_seal`, `reply_unused`). The kernels come from the labelled-kernel identities `resolve_after_send` and `resolve_after_receive` with `PqxdhRecordLiftWorld.kernel_exact`. On the Server side the generic build differs between two such sends only in the kernel it publishes (`genericBuild_kernel`).

These are equalities of programs in every lawful monad (and at the service level for the native primitives). They make no authentication, secrecy or independence claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit
open PqxdhServerAuthSendFactor (Kernel Factor resolve)
open RawCtxSelectedChain (Slot)
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
open PqxdhDeploymentHiddenLayout (Material joinOutput)

/-- The constant unused-chain interpretation of chain labels. -/
abbrev unused {α : Type} : α → RatchetChain := fun _ => RawCtxSelectedChain.unusedChain

/-- The material (key32, nonce12) of an assembled 76-byte response is its key and nonce. -/
theorem material_assemble (key next : RootOutput) (nonce : NonceOutput) :
    PqxdhOrderedChainHybrids.material (RawCtxKdfRequestTable.assemble (key, next, nonce)) = (key, nonce) :=
  congrArg (fun parts => (parts.1, parts.2.2))
    (PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.apply_symm_apply (key, next, nonce))

/-- Decoding a full 76-byte response yields its next chain and its material. -/
theorem decode_full (output : FullOutput) :
    RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output) =
      (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output),
        RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material output)) := by
  have chosen := (BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok
    (RawCtxKdfRequestTable.fullResponse output)).choose_spec
  have same := RustM.ok.inj ((PqxdhRecordLiftSeed.response_step output).symm.trans chosen)
  unfold RawCtxInterpretedReceive.decodeResponse
  simp only [← same]

/-- The material of the selected step on the hidden slot depends on the response only through its material. -/
theorem step_material (source : FixedHkdfSha512NoSaltSource) (output output' : FullOutput)
    (hmat : PqxdhOrderedChainHybrids.material output = PqxdhOrderedChainHybrids.material output') :
    (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden).2 =
      (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output') .hidden).2 := by
  simp only [RawCtxSelectedChain.step, decode_full, hmat]

/-- The sequence-one receive from the hidden Beacon's initial kernel requests one key derivation on the hidden slot and then an opening, for every response. -/
theorem sequence_one_shape (source : FixedHkdfSha512NoSaltSource) (right : RootOutput) (output : FullOutput)
    (context : RawCtxWholeOwner.OpenContext) :
    ∃ pending opening, RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context =
        .kdfRequested pending ∧ pending.request = .hidden ∧
      RawCtxChainReceive.normalResume pending
        (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden) = .openRequested opening := by
  obtain ⟨kernel, built⟩ := PqxdhRecordLiftSeed.beaconKernel_total (PqxdhOrderedChainHybrids.nextChain output, right)
  have counted := PqxdhRecordLiftSeed.receiveOne_from_counters RawCtxSelectedChain.unusedChain
    (RawCtxFreshChainCut.concreteChain right) (RawCtxKdfRequestTable.fullResponse output) _
    (PqxdhRecordLiftSeed.response_step output) context (⟨[], 0#u64, 0#u64⟩ : RawCtxWholeOwner.Decrypted)
  rw [PqxdhDeploymentHiddenKernels.beaconInitial_native, bind_tc_ok,
    PqxdhDeploymentHiddenKernels.receive_native source] at counted
  rw [show ConcreteRatchetKernel.from_counters 0#u64 1#u64 (RawCtxFreshChainCut.concreteChain right)
      (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output)) = ok kernel from built,
    RawCtxMaterialInterpretation.rust_map_ok] at counted
  cases begun : RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context with
  | rejected entry actual => simp only [begun, RustM.ok.injEq, reduceCtorEq] at counted
  | openRequested opening => simp only [begun, RustM.ok.injEq, reduceCtorEq] at counted
  | kdfRequested pending =>
      have request : pending.request = .hidden :=
        PqxdhDeploymentHiddenKernels.receive_begin_request _ 1#u64 context pending begun
      cases resumed : RawCtxChainReceive.normalResume pending
          (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden) with
      | rejected entry actual => simp only [begun, resumed, RustM.ok.injEq, reduceCtorEq] at counted
      | kdfRequested next => simp only [begun, resumed, RustM.ok.injEq, reduceCtorEq] at counted
      | openRequested opening => exact ⟨pending, opening, rfl, request, resumed⟩


/-- With every chain label read as the unused chain, the opening reached by the sequence-one receive from the hidden Beacon's initial kernel depends on the 76-byte response only through its material and not on the opposite chain. -/
theorem opening_unused (source : FixedHkdfSha512NoSaltSource) (right right' : RootOutput) (output output' : FullOutput)
    (hmat : PqxdhOrderedChainHybrids.material output = PqxdhOrderedChainHybrids.material output')
    (context : RawCtxWholeOwner.OpenContext)
    (pending pending' : RawCtxChainReceive.Kdf Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (opening opening' : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (begun : RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context = .kdfRequested pending)
    (begun' : RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right') 1#u64 context = .kdfRequested pending')
    (resumed : RawCtxChainReceive.normalResume pending
      (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden) = .openRequested opening)
    (resumed' : RawCtxChainReceive.normalResume pending'
      (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output') .hidden) = .openRequested opening') :
    RawCtxChainInterpretation.mapOpeningChains unused unused opening =
      RawCtxChainInterpretation.mapOpeningChains unused unused opening' := by
  have admitted : RawCtxChainReceive.nativeEffect unused unused
      (RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context) =
      RawCtxChainReceive.nativeEffect unused unused
        (RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right') 1#u64 context) := by
    rw [← RawCtxChainReceive.normalBegin_native, ← RawCtxChainReceive.normalBegin_native]
    rfl
  rw [begun, begun'] at admitted
  simp only [RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.Effect.kdfRequested.injEq] at admitted
  have stepped : RawCtxChainReceive.nativeEffect unused unused (RawCtxChainReceive.normalResume pending
      (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden)) =
      RawCtxChainReceive.nativeEffect unused unused (RawCtxChainReceive.normalResume pending'
        (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output') .hidden)) := by
    rw [← RawCtxChainReceive.normalResume_native, ← RawCtxChainReceive.normalResume_native, admitted,
      step_material source output output' hmat]
  rw [resumed, resumed'] at stepped
  simpa only [RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.Effect.openRequested.injEq] using stepped

section Reply
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The reply of the labelled sequence-one receive of a hidden Beacon is the same program for every response with the same material and every opposite chain. -/
theorem reply_unused (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (source : FixedHkdfSha512NoSaltSource)
    (right right' : RootOutput) (output output' : FullOutput)
    (hmat : PqxdhOrderedChainHybrids.material output = PqxdhOrderedChainHybrids.material output')
    (context : RawCtxWholeOwner.OpenContext) :
    Prod.snd <$> simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source (RawCtxKdfRequestTable.fullResponse output))
        (RawCtxChainReceive.execute (Plaintext := RawCtxWholeOwner.Decrypted)
          (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context) =
      Prod.snd <$> simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source (RawCtxKdfRequestTable.fullResponse output'))
        (RawCtxChainReceive.execute (Plaintext := RawCtxWholeOwner.Decrypted)
          (PqxdhServerAuthBeaconFactor.initial right') 1#u64 context) := by
  obtain ⟨pending, opening, begun, request, resumed⟩ := sequence_one_shape source right output context
  obtain ⟨pending', opening', begun', request', resumed'⟩ := sequence_one_shape source right' output' context
  have same := opening_unused source right right' output output' hmat context pending pending' opening opening'
    begun begun' resumed resumed'
  simp only [RawCtxChainReceive.execute, begun, begun', RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query,
    PqxdhServerAuthBeaconFactor.primLabels, pure_bind, request, request', resumed, resumed', simulateQ_pure, map_bind,
    map_pure, PqxdhDeploymentHiddenKernels.normalFinish_reply]
  exact congrArg (fun opened => (prim ∘ₛ RawCtxWholeOwner.adapter)
    (Sum.inr (RawCtxInterpretedOpening.toNative opened)) >>= fun a => pure a) same

end Reply

/-- A staged registration with its kernel replaced. -/
def withKernel (kernel : ConcreteRatchetKernel) (staged : PqxdhBeaconPhase2Publication.Staged) :
    PqxdhBeaconPhase2Publication.Staged :=
  { staged with kernel := kernel }

/-- The sequence-one gate and the authentication after the opening do not read the kernel; the kernel is only staged. -/
theorem afterOpening_kernel (candidate : pqxdh.BeaconRegistrationCandidate) (kernel other : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    PqxdhBeaconPhase2Publication.afterOpening candidate kernel reply =
      Option.map (withKernel kernel) (PqxdhBeaconPhase2Publication.afterOpening candidate other reply) := by
  unfold PqxdhBeaconPhase2Publication.afterOpening
  cases reply with
  | none => rfl
  | some opened =>
      dsimp only
      split
      · rfl
      · split
        · split <;> rfl
        · rfl

section Finish
variable {m : Type → Type} [Monad m] [LawfulMonad m] {Response : Type}

/-- The Beacon kernel of the World for a seed is the record-lift Beacon kernel of the next and opposite chains. -/
theorem beaconKernel_seed (key : RootOutput) (nonce : NonceOutput) (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhRecordLiftSeed.beaconKernel (PqxdhOrderedChainHybrids.nextChain
      (RawCtxKdfRequestTable.assemble (key, seed.1, nonce)), seed.2) =
      ok (PqxdhRecordLiftWorld.kernel .beacon seed) := by
  rw [PqxdhRecordLiftSeed.assembled_next]
  exact PqxdhRecordLiftWorld.kernel_exact .beacon seed

/-- On a raw input whose decoded sequence is one, the hidden finish body depends on the world seed only through the staged kernel, which is the World's Beacon kernel of the seed. -/
theorem body_split (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (material : Material)
    (seed seed' : PqxdhRecordLiftSeed.Seed) (raw : Pqxdh.Bytes)
    (one : PqxdhDeploymentHiddenKernels.SeqOne decode raw = true) :
    PqxdhDeploymentHiddenKernels.factoredBody prim sendCall source decode prepared
        (PqxdhServerAuthCtxMaterial.factor (joinOutput material seed)) raw =
      Option.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)) <$>
        PqxdhDeploymentHiddenKernels.factoredBody prim sendCall source decode prepared
          (PqxdhServerAuthCtxMaterial.factor (joinOutput material seed')) raw := by
  simp only [PqxdhDeploymentHiddenKernels.factoredBody, RawCtxChainOwner.rawReceive, StateT.run,
    PqxdhServerAuthBeaconFactor.localState]
  by_cases blank : raw.isEmpty = true
  · simp only [blank, ite_true, pure_bind, map_pure, RawCtxChainOwner.publish,
      PqxdhBeaconPhase2Publication.afterOpening, Option.map_none]
  · simp only [blank, Bool.false_eq_true, ite_false]
    cases decoded : decode raw with
    | none =>
        simp only [pure_bind, map_pure, RawCtxChainOwner.publish, PqxdhBeaconPhase2Publication.afterOpening,
          Option.map_none]
    | some frame =>
        have sequence : frame.sequence = 1#u64 := by
          simpa only [PqxdhDeploymentHiddenKernels.SeqOne, decoded, decide_eq_true_eq] using one
        dsimp only
        by_cases valid : RawCtxReceive.ValidFrame
            (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate).server_binding.identity_key_id
            (absBytes (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate).associated_data) frame
        · simp only [valid, ite_true, PqxdhServerAuthBeaconFactor.primCalls,
            RawCtxChainOwner.publish, sequence, bind_pure_comp, PqxdhDeploymentHiddenLayout.factor_join]
          simp only [Functor.map_map]
          have kernel := PqxdhDeploymentHiddenKernels.resolve_after_receive prim source seed.2
            (RawCtxKdfRequestTable.assemble (material.1, seed.1, material.2))
            ⟨raw, frame, absBytes (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate).associated_data⟩
            (PqxdhRecordLiftWorld.kernel .beacon seed)
            (fun kernel reply => PqxdhBeaconPhase2Publication.afterOpening
              (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate) kernel reply)
            (beaconKernel_seed material.1 material.2 seed) (fun _ _ => rfl)
          rw [kernel]
          have restaged : (fun result : Kernel × core.option.Option RawCtxWholeOwner.Decrypted =>
              Option.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed))
                (PqxdhBeaconPhase2Publication.afterOpening (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
                  (resolve result.1) result.2)) =
              (fun result => PqxdhBeaconPhase2Publication.afterOpening
                (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
                (PqxdhRecordLiftWorld.kernel .beacon seed) result.2) :=
            funext fun result => (afterOpening_kernel _ _ _ result.2).symm
          rw [restaged]
          have replied := reply_unused prim source seed.2 seed'.2
            (RawCtxKdfRequestTable.assemble (material.1, seed.1, material.2))
            (RawCtxKdfRequestTable.assemble (material.1, seed'.1, material.2))
            (by rw [material_assemble, material_assemble])
            ⟨raw, frame, absBytes (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate).associated_data⟩
          have composed := congrArg (fun program => (fun reply => PqxdhBeaconPhase2Publication.afterOpening
            (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
            (PqxdhRecordLiftWorld.kernel .beacon seed) reply) <$> program) replied
          simpa only [Functor.map_map, Function.comp_def] using composed
        · simp only [valid, ite_false, pure_bind, map_pure, RawCtxChainOwner.publish,
            PqxdhBeaconPhase2Publication.afterOpening, Option.map_none]

/-- The erased hidden finish depends on the world seed only through the staged kernel, which is the World's Beacon kernel of the seed (C7-erased factor form against any other seed). -/
theorem erased_split (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (material : Material) (seed seed' : PqxdhRecordLiftSeed.Seed) :
    Prod.fst <$> PqxdhDeploymentHiddenKernels.finishErased prim sendCall source application decode prepared
        (PqxdhServerAuthCtxMaterial.factor (joinOutput material seed)) =
      Option.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)) <$>
        (Prod.fst <$> PqxdhDeploymentHiddenKernels.finishErased prim sendCall source application decode prepared
          (PqxdhServerAuthCtxMaterial.factor (joinOutput material seed'))) := by
  simp only [PqxdhDeploymentHiddenKernels.finishErased, map_bind, Functor.map_map]
  refine bind_congr fun raw => ?_
  cases raw with
  | none => simp only [map_pure, Option.map_none]
  | some raw =>
      dsimp only
      by_cases one : PqxdhDeploymentHiddenKernels.SeqOne decode raw = true
      · simp only [one, ite_true, Functor.map_map]
        rw [body_split prim sendCall source decode prepared material seed seed' raw one, Functor.map_map]
      · simp only [one, Bool.false_eq_true, ite_false, map_pure, Option.map_none]

end Finish

/-- A fixed seed standing for the World's seed in the split forms. -/
def dummySeed : PqxdhRecordLiftSeed.Seed := (List.Vector.replicate 32 0, List.Vector.replicate 32 0)

/-- A fixed kernel standing for "installed by the World": the split forms stage it in place of the seed kernel; it carries no slot data. -/
noncomputable def placeholderKernel : ConcreteRatchetKernel := PqxdhRecordLiftWorld.kernel .beacon dummySeed

/-- Replacing the staged kernel twice keeps the second replacement. -/
theorem withKernel_withKernel (first second : ConcreteRatchetKernel) (staged : PqxdhBeaconPhase2Publication.Staged) :
    withKernel second (withKernel first staged) = withKernel second staged := rfl

section Service
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)

/-- The split hidden finish with the service type: the erased finish on the material alone, staging the placeholder kernel. -/
noncomputable def finishSplit (material : Material) : PqxdhDeploymentHiddenEntry.HiddenAfter Response := fun pending =>
  Option.map (withKernel placeholderKernel) <$>
    PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec material dummySeed pending

/-- Kernel identity of the Beacon (m4): the erased hidden finish at material and seed is the split finish with the World's Beacon kernel of the seed staged in place of the placeholder. -/
theorem finish_factor_split (material : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec material seed pending =
      Option.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)) <$> finishSplit setup codec material pending := by
  simp only [finishSplit, Functor.map_map]
  have fold : (fun staged => Option.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed))
      (Option.map (withKernel placeholderKernel) staged)) =
      Option.map (withKernel (PqxdhRecordLiftWorld.kernel .beacon seed)) := by
    funext staged
    cases staged <;> rfl
  rw [fold]
  exact erased_split _ _ setup.source _ codec.frameRead _ material seed dummySeed

/-- The split hidden finish commutes with completions of the CTX cache. -/
theorem finishSplit_commutes_ctx (material : Material) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    LazyOracleDiscard.Commutes PqxdhDeploymentHiddenKernels.ctxLens (finishSplit setup codec material pending) :=
  LazyOracleDiscard.commutes_map _ _
    (PqxdhDeploymentHiddenEntry.finishErased_commutes_ctx setup codec material dummySeed pending)

end Service

/-- With every chain label read as the unused chain, the first seal of the hidden Server depends on the 76-byte response only through its material and not on the opposite chain. -/
theorem seal_unused (source : FixedHkdfSha512NoSaltSource) (right right' : RootOutput) (output output' : FullOutput)
    (hmat : PqxdhOrderedChainHybrids.material output = PqxdhOrderedChainHybrids.material output')
    (context : RawCtxSourceSend.SealContext)
    (pending pending' : RawCtxChainSend.Kdf Slot Slot RatchetMaterial RawCtxSourceSend.SealContext)
    (begun : RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial right) context = .requested pending)
    (begun' : RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial right') context =
      .requested pending') :
    RawCtxChainSend.nativeSeal unused unused
        (RawCtxChainSend.ready pending (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output)
          pending.request)) =
      RawCtxChainSend.nativeSeal unused unused
        (RawCtxChainSend.ready pending' (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output')
          pending'.request)) := by
  obtain ⟨other, otherBegun, request⟩ := PqxdhDeploymentHiddenKernels.initial_send_requested right context
  obtain ⟨other', otherBegun', request'⟩ := PqxdhDeploymentHiddenKernels.initial_send_requested right' context
  rw [begun] at otherBegun
  rw [begun'] at otherBegun'
  cases otherBegun
  cases otherBegun'
  have admitted : RawCtxChainSend.nativeStart unused unused
      (RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial right) context) =
      RawCtxChainSend.nativeStart unused unused
        (RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial right') context) := by
    rw [← RawCtxChainSend.normalBegin_native, ← RawCtxChainSend.normalBegin_native]
    rfl
  rw [begun, begun'] at admitted
  simp only [RawCtxChainSend.nativeStart, RawCtxInterpretedSend.Start.requested.injEq, RawCtxChainSend.nativeKdf,
    RawCtxInterpretedSend.Kdf.mk.injEq] at admitted
  obtain ⟨entries, contexts, committed, logicals, sequences, _⟩ := admitted
  have slots := congrArg (fun kernel => kernel.receive_slots) entries
  simp only [RawCtxChainInterpretation.mapChains] at slots
  rw [request, request']
  simp only [RawCtxChainSend.nativeSeal, RawCtxChainSend.ready, RawCtxChainInterpretation.mapChains,
    step_material source output output' hmat, contexts, committed, logicals, sequences, slots]


/-- The first send of the hidden Server's initial kernel is one seal, and it returns the kernel advanced on the selected step. -/
theorem send_seal {m : Type → Type} [Monad m] [LawfulMonad m]
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (source : FixedHkdfSha512NoSaltSource)
    (challenge : RatchetKdfResponse) (right : RootOutput) (context : RawCtxSourceSend.SealContext)
    (pending : RawCtxChainSend.Kdf Slot Slot RatchetMaterial RawCtxSourceSend.SealContext)
    (begun : RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial right) context = .requested pending) :
    (PqxdhServerAuthLoggedSendFactor.calls receiveCall prim source challenge).send
        (PqxdhDeploymentHiddenKernels.serverInitial right) context =
      (fun sealed => ((RawCtxChainSend.ready pending (RawCtxSelectedChain.step source challenge pending.request)).advanced,
        sealed)) <$>
        (prim ∘ₛ RawCtxSourceSend.adapter) (.inr (RawCtxInterpretedSend.nativeSeal (RawCtxChainSend.nativeSeal unused unused
          (RawCtxChainSend.ready pending (RawCtxSelectedChain.step source challenge pending.request))))) := by
  simp only [PqxdhServerAuthLoggedSendFactor.calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  simp only [PqxdhServerAuthSendFactor.primLabels, pure_bind, bind_pure_comp]
  rfl

section Publish
variable {K Metadata PeerMetadata Consumed : Type}

/-- Set the kernel of the Server peer at a key ID, if one is present. -/
def setPeerKernel (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) (key : Std.U64)
    (kernel : ConcreteRatchetKernel) : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed :=
  { state with server := { state.server with peers := Function.update state.server.peers key ((state.server.peers key).map fun peer => { peer with kernel := kernel }) } }

/-- Replace the kernel that a successful build published; every other result is kept. -/
def replaceRaw (kernel : ConcreteRatchetKernel) :
    Option PqxdhServerRegistrationPublication.Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed →
      Option PqxdhServerRegistrationPublication.Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed
  | (some response, state) => (some response, setPeerKernel state response.keyId kernel)
  | result => result

/-- Publishing one kernel and then setting another at the published key ID publishes the second. -/
theorem publish_setPeerKernel (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (first second : ConcreteRatchetKernel) (metadata : PeerMetadata) :
    setPeerKernel (PqxdhServerRegistrationPublication.publish state candidate first metadata) candidate.key_id second =
      PqxdhServerRegistrationPublication.publish state candidate second metadata := by
  simp only [setPeerKernel, PqxdhServerRegistrationPublication.publish, Function.update_self, Option.map_some,
    Function.update_idem]

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- When the first sends of two builds are the same seal and return kernels with fixed interpretations, the interpreted first send and Phase 2 writing differ only in the published kernel. -/
theorem afterInitialization_kernel (interpret : K → ConcreteRatchetKernel) (calls₁ calls₂ : RawCtxChainOwner.Calls K m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (k₁ k₂ : K) (a₁ a₂ : RawCtxSourceSend.SealContext → K)
    (kernel₁ kernel₂ : ConcreteRatchetKernel)
    (sealing : RawCtxSourceSend.SealContext → m (Option RawCtxSourceSend.Encrypted))
    (send₁ : ∀ context, calls₁.send k₁ context = (fun sealed => (a₁ context, sealed)) <$> sealing context)
    (send₂ : ∀ context, calls₂.send k₂ context = (fun sealed => (a₂ context, sealed)) <$> sealing context)
    (resolved₁ : ∀ context, interpret (a₁ context) = kernel₁) (resolved₂ : ∀ context, interpret (a₂ context) = kernel₂)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    Prod.map id (PqxdhInitialGenericPublication.native interpret) <$>
        PqxdhInitialGenericPublication.afterInitialization calls₁ aux candidate authenticated k₁ metadata state =
      replaceRaw kernel₁ <$> (Prod.map id (PqxdhInitialGenericPublication.native interpret) <$>
        PqxdhInitialGenericPublication.afterInitialization calls₂ aux candidate authenticated k₂ metadata state) := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  rw [send₁, send₂, bind_map_left, bind_map_left, map_bind, map_bind, map_bind]
  refine bind_congr fun sealed => ?_
  rw [map_bind, map_bind, map_bind]
  refine bind_congr fun _ => ?_
  cases sealed with
  | none => simp only [map_pure]; rfl
  | some encrypted =>
      dsimp only
      rw [map_bind, map_bind, map_bind]
      refine bind_congr fun serialized => ?_
      cases serialized with
      | none => simp only [map_pure]; rfl
      | some serialized =>
          simp only [map_pure, Prod.map_apply, id_eq, replaceRaw, PqxdhInitialGenericPublication.publish_native,
            resolved₁, resolved₂, publish_setPeerKernel]

/-- The interpreted candidate admission and first send of two such builds differ only in the published kernel. -/
theorem candidate_kernel (interpret : K → ConcreteRatchetKernel) (calls₁ calls₂ : RawCtxChainOwner.Calls K m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (k₁ k₂ : K) (a₁ a₂ : RawCtxSourceSend.SealContext → K)
    (kernel₁ kernel₂ : ConcreteRatchetKernel)
    (sealing : RawCtxSourceSend.SealContext → m (Option RawCtxSourceSend.Encrypted))
    (send₁ : ∀ context, calls₁.send k₁ context = (fun sealed => (a₁ context, sealed)) <$> sealing context)
    (send₂ : ∀ context, calls₂.send k₂ context = (fun sealed => (a₂ context, sealed)) <$> sealing context)
    (resolved₁ : ∀ context, interpret (a₁ context) = kernel₁) (resolved₂ : ∀ context, interpret (a₂ context) = kernel₂)
    (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native interpret)) <$>
        PqxdhInitialGenericBuilder.candidate calls₁ aux (ok k₁) candidate data metadata state =
      Functor.map (replaceRaw kernel₁) <$> (Functor.map (Prod.map id (PqxdhInitialGenericPublication.native interpret)) <$>
        PqxdhInitialGenericBuilder.candidate calls₂ aux (ok k₂) candidate data metadata state) := by
  unfold PqxdhInitialGenericBuilder.candidate PqxdhInitialGenericBuilder.continueRust
  simp only [map_bind]
  refine bind_congr fun valid => ?_
  by_cases hvalid : (!valid) = true
  · simp only [hvalid, ite_true, map_pure]
    rfl
  · simp only [hvalid, Bool.false_eq_true, ite_false, map_bind]
    refine bind_congr fun reserved => ?_
    by_cases hreserved : (!reserved) = true
    · simp only [hreserved, ite_true, map_pure]
      rfl
    · simp only [hreserved, Bool.false_eq_true, ite_false]
      split
      · simp only [map_pure]; rfl
      · split
        · simp only [map_bind]
          refine bind_congr fun allocated => ?_
          by_cases hallocated : (!allocated) = true
          · simp only [hallocated, ite_true, map_pure]
            rfl
          · simp only [hallocated, Bool.false_eq_true, ite_false]
            split
            next _ binding _ =>
              have key := afterInitialization_kernel interpret calls₁ calls₂ aux k₁ k₂ a₁ a₂ kernel₁ kernel₂ sealing
                send₁ send₂ resolved₁ resolved₂ candidate
                (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness) metadata state
              have lifted := congrArg (fun program => (ok <$> program : m (RustM _))) key
              simp only [Functor.map_map] at lifted
              simp only [Functor.map_map]
              exact lifted
            next => simp only [map_pure]; rfl
            next => simp only [map_pure]; rfl
        · simp only [map_pure]; rfl

/-- The interpreted generic builds of two such builds differ only in the published kernel. -/
theorem genericBuild_kernel (interpret : K → ConcreteRatchetKernel) (calls₁ calls₂ : RawCtxChainOwner.Calls K m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (k₁ k₂ : K) (a₁ a₂ : RawCtxSourceSend.SealContext → K)
    (kernel₁ kernel₂ : ConcreteRatchetKernel)
    (sealing : RawCtxSourceSend.SealContext → m (Option RawCtxSourceSend.Encrypted))
    (send₁ : ∀ context, calls₁.send k₁ context = (fun sealed => (a₁ context, sealed)) <$> sealing context)
    (send₂ : ∀ context, calls₂.send k₂ context = (fun sealed => (a₂ context, sealed)) <$> sealing context)
    (resolved₁ : ∀ context, interpret (a₁ context) = kernel₁) (resolved₂ : ∀ context, interpret (a₂ context) = kernel₂)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native interpret)) <$>
        PqxdhServerAuthSendFactor.genericBuild calls₁ aux (ok k₁) pending data metadata state =
      Functor.map (replaceRaw kernel₁) <$> (Functor.map (Prod.map id (PqxdhInitialGenericPublication.native interpret)) <$>
        PqxdhServerAuthSendFactor.genericBuild calls₂ aux (ok k₂) pending data metadata state) := by
  unfold PqxdhServerAuthSendFactor.genericBuild PqxdhInitialGenericBuilder.continueRust
  rcases pqxdh.server_next_key_id state.control with (next | error) | error | _
  · dsimp only
    split
    next _ prepared _ =>
      cases prepared with
      | Err error => simp only [map_pure]; rfl
      | Ok candidate =>
          exact candidate_kernel interpret calls₁ calls₂ aux k₁ k₂ a₁ a₂ kernel₁ kernel₂ sealing send₁ send₂
            resolved₁ resolved₂ _ data metadata state
    next => simp only [map_pure]; rfl
    next => simp only [map_pure]; rfl
  · simp only [map_pure]; rfl
  · simp only [map_pure]; rfl
  · simp only [map_pure]; rfl

end Publish

/-- The Server kernel of the World for a seed is the record-lift Server kernel of the next and opposite chains. -/
theorem serverKernel_seed (key : RootOutput) (nonce : NonceOutput) (seed : PqxdhRecordLiftSeed.Seed) :
    PqxdhRecordLiftSeed.serverKernel (PqxdhOrderedChainHybrids.nextChain
      (RawCtxKdfRequestTable.assemble (key, seed.1, nonce)), seed.2) =
      ok (PqxdhRecordLiftWorld.kernel .server seed) := by
  rw [PqxdhRecordLiftSeed.assembled_next]
  exact PqxdhRecordLiftWorld.kernel_exact .server seed

/-- Kernel identity of the Server at the build level: the factored build at material and seed is the factored build at any other seed with the World's Server kernel of the seed published in place of the other seed's kernel. -/
theorem build_split_raw {m : Type → Type} [Monad m] [LawfulMonad m] {Metadata PeerMetadata Consumed : Type}
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (source : FixedHkdfSha512NoSaltSource)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m) (material : Material)
    (seed seed' : PqxdhRecordLiftSeed.Seed) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerAuthLoggedSendFactor.factored receiveCall prim source aux
        (PqxdhServerAuthCtxMaterial.factor (joinOutput material seed)) pending data metadata state =
      Functor.map (replaceRaw (PqxdhRecordLiftWorld.kernel .server seed)) <$>
        PqxdhServerAuthLoggedSendFactor.factored receiveCall prim source aux
          (PqxdhServerAuthCtxMaterial.factor (joinOutput material seed')) pending data metadata state := by
  let output := RawCtxKdfRequestTable.assemble (material.1, seed.1, material.2)
  let output' := RawCtxKdfRequestTable.assemble (material.1, seed'.1, material.2)
  have hmat : PqxdhOrderedChainHybrids.material output = PqxdhOrderedChainHybrids.material output' := by
    simp only [output, output', material_assemble]
  let first (context : RawCtxSourceSend.SealContext) :=
    (PqxdhDeploymentHiddenKernels.initial_send_requested seed.2 context).choose
  let second (context : RawCtxSourceSend.SealContext) :=
    (PqxdhDeploymentHiddenKernels.initial_send_requested seed'.2 context).choose
  have firstBegun : ∀ context, RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial seed.2) context =
      .requested (first context) := fun context =>
    (PqxdhDeploymentHiddenKernels.initial_send_requested seed.2 context).choose_spec.1
  have secondBegun : ∀ context, RawCtxChainSend.normalBegin (PqxdhDeploymentHiddenKernels.serverInitial seed'.2) context =
      .requested (second context) := fun context =>
    (PqxdhDeploymentHiddenKernels.initial_send_requested seed'.2 context).choose_spec.1
  unfold PqxdhServerAuthLoggedSendFactor.factored
  simp only [PqxdhDeploymentHiddenLayout.factor_join]
  rw [show RawCtxSelectedInitialConstructor.initial false seed.2 = ok (PqxdhDeploymentHiddenKernels.serverInitial seed.2)
      from rfl, show RawCtxSelectedInitialConstructor.initial false seed'.2 =
        ok (PqxdhDeploymentHiddenKernels.serverInitial seed'.2) from rfl]
  refine genericBuild_kernel resolve _ _ aux _ _
    (fun context => (RawCtxChainSend.ready (first context) (RawCtxSelectedChain.step source
      (RawCtxKdfRequestTable.fullResponse output) (first context).request)).advanced)
    (fun context => (RawCtxChainSend.ready (second context) (RawCtxSelectedChain.step source
      (RawCtxKdfRequestTable.fullResponse output') (second context).request)).advanced)
    (PqxdhRecordLiftWorld.kernel .server seed) (PqxdhRecordLiftWorld.kernel .server seed')
    (fun context => (prim ∘ₛ RawCtxSourceSend.adapter) (.inr (RawCtxInterpretedSend.nativeSeal
      (RawCtxChainSend.nativeSeal unused unused (RawCtxChainSend.ready (second context) (RawCtxSelectedChain.step source
        (RawCtxKdfRequestTable.fullResponse output') (second context).request))))))
    (fun context => ?_) (fun context => ?_) (fun context => ?_) (fun context => ?_) pending data metadata
    (PqxdhServerAuthSendFactor.embed state)
  · rw [send_seal receiveCall prim source _ seed.2 context (first context) (firstBegun context),
      seal_unused source seed.2 seed'.2 output output' hmat context (first context) (second context)
        (firstBegun context) (secondBegun context)]
    rfl
  · exact send_seal receiveCall prim source _ seed'.2 context (second context) (secondBegun context)
  · exact RustM.ok.inj ((PqxdhDeploymentHiddenKernels.resolve_after_send source seed.2 output context (first context)
      (firstBegun context)).symm.trans (serverKernel_seed material.1 material.2 seed))
  · exact RustM.ok.inj ((PqxdhDeploymentHiddenKernels.resolve_after_send source seed'.2 output' context (second context)
      (secondBegun context)).symm.trans (serverKernel_seed material.1 material.2 seed'))

/-- Replacing the published kernel twice keeps the second replacement. -/
theorem replaceRaw_replaceRaw {Metadata PeerMetadata Consumed : Type} (first second : ConcreteRatchetKernel)
    (result : Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    replaceRaw second (replaceRaw first result) = replaceRaw second result := by
  rcases result with ⟨_ | response, state⟩
  · rfl
  · simp only [replaceRaw, setPeerKernel, Function.update_self, Function.update_idem, Option.map_map,
      Function.comp_def]

section BuildService
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (checks : PqxdhServerAuthExperiment.Checks)

/-- The split hidden build with the service type: the factored build on the material alone, publishing the placeholder kernel. -/
noncomputable def buildSplit (material : Material) : PqxdhDeploymentHiddenEntry.HiddenBuild := fun token payload server =>
  Functor.map (replaceRaw placeholderKernel) <$>
    PqxdhDeploymentHiddenEntry.buildFactor setup codec checks material dummySeed token payload server

/-- Kernel identity of the Server (m4): the factor-form hidden build at material and seed is the split build with the World's Server kernel of the seed published in place of the placeholder. -/
theorem build_factor_split (material : Material) (seed : PqxdhRecordLiftSeed.Seed)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    PqxdhDeploymentHiddenEntry.buildFactor setup codec checks material seed token payload server =
      Functor.map (replaceRaw (PqxdhRecordLiftWorld.kernel .server seed)) <$>
        buildSplit setup codec checks material token payload server := by
  simp only [buildSplit]
  rw [Functor.map_map]
  have fold : (fun result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerAuthEntryFactor.ServerState) => Functor.map (replaceRaw (PqxdhRecordLiftWorld.kernel .server seed))
      (Functor.map (replaceRaw placeholderKernel) result)) =
      Functor.map (replaceRaw (PqxdhRecordLiftWorld.kernel .server seed)) := by
    funext result
    cases result with
    | ok value => exact congrArg RustM.ok (replaceRaw_replaceRaw _ _ value)
    | fail error => rfl
    | div => rfl
  rw [fold]
  exact build_split_raw _ _ setup.source _ material seed dummySeed _ _ () server

/-- The split hidden build commutes with completions of the CTX cache of its seal state. -/
theorem buildSplit_commutes_ctx (material : Material) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState) :
    LazyOracleDiscard.Commutes (PqxdhDeploymentHiddenEntry.sharedLens (List RawCtxSourceSend.SealContext))
      (buildSplit setup codec checks material token payload server) :=
  LazyOracleDiscard.commutes_map _ _
    (PqxdhDeploymentHiddenEntry.buildFactor_commutes_ctx setup codec checks material dummySeed token payload server)

end BuildService

end BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.material_assemble' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.material_assemble

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.decode_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.decode_full

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.step_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.step_material

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.sequence_one_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.sequence_one_shape

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.opening_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.opening_unused

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.reply_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.reply_unused

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.afterOpening_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.afterOpening_kernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.beaconKernel_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.beaconKernel_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.body_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.body_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.erased_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.erased_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.withKernel_withKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.withKernel_withKernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.finish_factor_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.finish_factor_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.finishSplit_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.finishSplit_commutes_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.seal_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.seal_unused

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.send_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.send_seal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.publish_setPeerKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.publish_setPeerKernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.afterInitialization_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.afterInitialization_kernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.candidate_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.candidate_kernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.genericBuild_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.genericBuild_kernel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.serverKernel_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.serverKernel_seed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.build_split_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.build_split_raw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.replaceRaw_replaceRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.replaceRaw_replaceRaw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.build_factor_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.build_factor_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.buildSplit_commutes_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit.buildSplit_commutes_ctx
