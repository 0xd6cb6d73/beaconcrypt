-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSourceDraw

/-! The exact digest-bearing selected seal state and its retained projection. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode materialAt)
open PqxdhRecordFactsOriginMuteComplete (project)
open PqxdhRecordFactsPrivateCacheFresh (sealResult)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec compileSeal compileKeyedSeal compileHiddenSeal)
variable {n : Nat}

/-- Literal successful local seal result reinstalled at its chosen coordinate with every other field retained. -/
def keyedResult (label : Label n) (input : CtxSealInput) (body tag : Pqxdh.Bytes)
    (width : tag.length = 16) (digest : CtxDigest) (state : CtxPrivate n) :
    Option CtxRomRecord × CtxPrivate n :=
  let result := sealResult input body tag width digest (state.keys label, state.base.primitive.2)
  (result.1, { state with
    base := { state.base with primitive := (state.base.primitive.1, result.2.2) }
    keys := Function.update state.keys label result.2.1 })

/-- The complete retained selected-key poststate is independent of the fresh digest, before any writer outcome is conditioned on. -/
theorem keyed_project (label : Label n) (input : CtxSealInput) (body tag : Pqxdh.Bytes)
    (width : tag.length = 16) (first second : CtxDigest) (state : CtxPrivate n) :
    project label (keyedResult label input body tag width first state).2 =
      project label (keyedResult label input body tag width second state).2 := by
  simp only [project, PqxdhRecordFactsOriginMuteFamily.project,
    PqxdhRecordFactsPrivateCacheFamily.localLens, PqxdhRecordFactsOriginMute.project,
    PqxdhRecordFactsOriginLogs.clearCtx, PqxdhRecordFactsOriginLogs.clearPrivate,
    keyedResult, sealResult, Function.update_self, Function.update_idem]

/-- Complete literal hidden-seal result, retaining its actual writer option and pre-writer frame append. -/
def hiddenResult (writer : RawCtxMixedShared.Writer) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (input : CtxSealInput) (body tag : Pqxdh.Bytes) (width : tag.length = 16)
    (digest : CtxDigest) (state : CtxPrivate n) : Option RawCtxSourceSend.Encrypted × CtxPrivate n :=
  let record : CtxRomRecord := ⟨body, tag, width, digest⟩
  let frame : RawCtxReceive.DecodedFrame := ⟨pending.sequence, pending.context.senderId, record.encode⟩
  let result := keyedResult pending.material input body tag width digest state
  ((writer frame).map fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩,
    { result.2 with base := { result.2.base with pending := state.base.pending ++ [frame] } })

/-- Clearing precisely the private copies makes the complete hidden-seal poststate digest-independent while leaving its literal writer reply outside the projection. -/
theorem hidden_project (writer : RawCtxMixedShared.Writer) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (input : CtxSealInput) (body tag : Pqxdh.Bytes) (width : tag.length = 16)
    (first second : CtxDigest) (state : CtxPrivate n) :
    project pending.material (hiddenResult writer pending input body tag width first state).2 =
      project pending.material (hiddenResult writer pending input body tag width second state).2 := by
  exact keyed_project pending.material input body tag width first second state

/-- Exact body/tag generation precedes the complete uniform digest; no primitive sampler order is interchanged. -/
noncomputable def keyedSampler (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (label : Label n) (input : CtxSealInput) (state : CtxPrivate n) :
    ProbComp (Option CtxRomRecord × CtxPrivate n) := do
  if modes label = .random then
    let body ← $ᵗ (FixedBytes input.plaintext.length)
    let tag ← $ᵗ (FixedBytes 16)
    let digest ← $ᵗ CtxDigest
    pure (keyedResult label input body.toList tag.toList tag.toList_length digest state)
  else
    let ciphertext := crypto.aeadSeal (materialAt state.base.chain label).1.toList
      input.nonce.toList input.context.ad.bytes input.plaintext
    let digest ← $ᵗ CtxDigest
    pure (keyedResult label input ciphertext.1 ciphertext.2
      (crypto.aeadSeal_tag_length _ _ _ _) digest state)

/-- The exposed selected digest compiler evaluates to the exact ordered full-state sampler. -/
theorem keyed_sampler (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (label : Label n) (input : CtxSealInput) (state : CtxPrivate n) :
    simulateQ (PqxdhRecordFactsPrivateCacheSourceDraw.evaluate ordinary)
      (compileKeyedSeal modes crypto label input state) = keyedSampler modes crypto label input state := by
  simp only [compileKeyedSeal, compileSeal, keyedSampler]
  split
  · simp only [simulateQ_bind, PqxdhRecordFactsPrivateCacheSourceDraw.evaluate_coins,
      simulateQ_spec_query, PqxdhRecordFactsPrivateCacheSourceDraw.evaluate, simulateQ_pure,
      map_bind, map_pure, keyedResult]
    rfl
  · simp only [simulateQ_bind, simulateQ_spec_query,
      PqxdhRecordFactsPrivateCacheSourceDraw.evaluate, simulateQ_pure, map_bind, map_pure, keyedResult]
    rfl

/-- The actual hidden-seal sampler exposes a uniform commitment after all source input, body and tag choices, retaining literal writer and buffer behavior. -/
noncomputable def hiddenSampler (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    ProbComp (Option RawCtxSourceSend.Encrypted × CtxPrivate n) :=
  if width : (PqxdhRecordLiftIdeal.replaceContext replace pending.context).associatedData.length = 153 then do
    let input := RawCtxSelectedMessageSealing.selectedInput (materialAt state.base.chain pending.material).2
      pending.sequence (PqxdhRecordLiftIdeal.replaceContext replace pending.context) width
    if modes pending.material = .random then
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let digest ← $ᵗ CtxDigest
      pure (hiddenResult writer pending input body.toList tag.toList tag.toList_length digest state)
    else
      let ciphertext := crypto.aeadSeal (materialAt state.base.chain pending.material).1.toList
        input.nonce.toList input.context.ad.bytes input.plaintext
      let digest ← $ᵗ CtxDigest
      pure (hiddenResult writer pending input ciphertext.1 ciphertext.2
        (crypto.aeadSeal_tag_length _ _ _ _) digest state)
  else pure (none, state)

/-- The exact compiler includes every rejection, ordered draw, literal writer option and complete poststate in this sampler. -/
theorem hidden_sampler (ordinary : Pqxdh.Bytes → ProbComp CtxDigest)
    (modes : Label n → KeyMode) (crypto : Pqxdh.Crypto)
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    simulateQ (PqxdhRecordFactsPrivateCacheSourceDraw.evaluate ordinary)
      (compileHiddenSeal modes crypto writer replace pending state) =
      hiddenSampler modes crypto writer replace pending state := by
  unfold compileHiddenSeal hiddenSampler
  split
  · simp only [simulateQ_bind, keyed_sampler]
    unfold keyedSampler
    split
    · simp only [bind_assoc, pure_bind, keyedResult, sealResult, simulateQ_pure, hiddenResult]
    · simp only [bind_assoc, pure_bind, keyedResult, sealResult, simulateQ_pure, hiddenResult]
  · rfl

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A reached fresh replay/random hidden sealing service is exactly the ordered sampler, with its original complete private state and literal writer return. -/
theorem source_sampler (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (ideal : modes pending.material ≠ .real)
    (fresh : PqxdhRecordFactsPrivateCacheSource.FreshPoint state (.sealing pending)) :
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing pending)).run state =
      hiddenSampler modes setup.source.crypto codec.frameWrite replace pending state :=
  (PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_exact (fun _ => pure default)
    modes replace setup codec pending state ideal fresh).symm.trans
      (hidden_sampler (fun _ => pure default) modes setup.source.crypto codec.frameWrite replace pending state)

/-- A fixed actual service continuation is independent of the selected digest after the checked private-copy projection; writer-result selection is deliberately not assumed independent. -/
theorem continuation_independent {X : Type} (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (first second : CtxDigest)
    (state : CtxPrivate n) (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0) :
    Prod.map id (project pending.material) <$>
      (simulateQ (PqxdhRecordFactsOriginMuteServices.interpreter pending.material modes
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace) client).run
          (hiddenResult codec.frameWrite pending input body tag width first state).2 =
    Prod.map id (project pending.material) <$>
      (simulateQ (PqxdhRecordFactsOriginMuteServices.interpreter pending.material modes
        (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace) client).run
          (hiddenResult codec.frameWrite pending input body tag width second state).2 :=
  PqxdhRecordFactsOriginMuteComplete.program_congr pending.material modes setup codec replace client noSeal _ _
    (hidden_project codec.frameWrite pending input body tag width first second state)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.keyed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.keyed_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.hidden_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.hidden_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.keyed_sampler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.keyed_sampler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.hidden_sampler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.hidden_sampler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.source_sampler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.source_sampler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.continuation_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal.continuation_independent
