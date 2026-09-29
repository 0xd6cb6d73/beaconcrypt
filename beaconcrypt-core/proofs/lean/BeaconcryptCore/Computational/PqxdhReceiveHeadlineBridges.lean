import BeaconcryptCore.Computational.PqxdhOpenContextBridge

/-!
# Receive bridges in the HB-111 and HB-112 headline statements

Audit finding F5 asks that the bridging equalities be conjuncts of the headline statements. `PqxdhOpenBridges` restates HB-111 and HB-112 with the record-opening bridge B12 as a conjunct (`authenticated_native_root_bound_bridged_open`, `authenticated_extracted_root_bound_open`, `evolving_bound_bridged_open` and `evolving_extracted_bound_open`), while the context completion of B12 and the receive-loop equalities of `PqxdhOpenContextBridge` are separate theorems. This module adds those equalities to the four restatements as one further conjunct. It adds new statements and changes no existing theorem.

`ReceiveBridge` is the conjunction of three propositions. The first is `PqxdhOpenContextBridge.ContextBridge`, which bundles `opened_record_bridge`, `receive_loop_bridge` and `decoded_receive_bridge`: for the same KDF replies, the extracted `begin_receive` and `ReceiveKdf.resume` give opening capabilities with the same ratchet entry and prepared receive for the experiments' context and for the frame context admitted by the extracted `record.OpenFrameContext.from_frame`, and on that capability `PqxdhOpenBridges.executeOpen` equals the experiments' opening step; the loop transcription `executeReceiveFrom` equals the experiments' receive driver `RawCtxOwnerOracle.receive`; and the decoded-frame transcription `executeDecoded` equals the branch of `RawCtxWholeOwner.rawReceive` after decoding and before publication. These three equalities hold at the interface of `RawCtxMixedOwner.receiveAdapter`. The second conjunct is the universally quantified statement of `PqxdhOpenContextBridge.decoded_receive_native`, the decoded-frame equality at the native opening interface `RawCtxSourceOpen.nativeAdapter`, before the embedding into the receive adapter. The third is the universally quantified statement of `PqxdhOpenContextBridge.decoded_after_root`, the same equality at the interface of the HB-111 target raw-opening site `PqxdhBeaconPhase2Shared.afterRoot` (through `PqxdhBeaconPhase2Shared.rawLift`), for every `Response` and `Shared` type. The second and third conjuncts are copied verbatim from the statements of those theorems, and `receive_bridge` proves `ReceiveBridge` from `context_bridge`, `decoded_receive_native` and `decoded_after_root`. The per-effect lemma `receive_loop_native` used in the proof of `decoded_receive_native` is not bundled. The only premises inside `ReceiveBridge` are B12's representation conditions (a payload slice and a 153-byte associated-data array representing the frame), the admission of the frame context by `from_frame` for the first two parts of `ContextBridge` and, for its first part, the hypothesis that the KDF replies drive the receive with the experiments' context to an opening capability.

`authenticated_native_root_bound_bridged_receive`, `authenticated_extracted_root_bound_receive`, `evolving_bound_bridged_receive` and `evolving_extracted_bound_receive` state the statement of the corresponding `PqxdhOpenBridges` theorem, copied verbatim, conjoined with `ReceiveBridge`, at the same parameters and under the same hypotheses. Each is proved by pairing that theorem with `receive_bridge`. `ReceiveBridge` is proved without hypotheses and mentions none of the headline parameters, so the restatements add no security premise and keep the bounds of the `PqxdhOpenBridges` theorems.

The added conjunct relates hand-written Lean transcriptions of unextracted Rust adapter functions to the experiments. `executeDecoded`, `executeReceiveFrom` and `executeReceive` transcribe the post-decoding part of `decrypt_message_with_ratchet` in `beaconcrypt/src/ratchet.rs`, `executeOpen` transcribes `execute_open`, and the reply fold `receiveReplies` models the iteration of that loop over KDF replies. The transcriptions call the extracted `begin_receive`, `ReceiveKdf.impl.request`, `ReceiveKdf.resume`, `record.OpenFrameContext.from_frame` and the extracted opening phases. Their agreement with the Rust functions is reviewed adapter trust, recorded in OR-10 of the trusted-boundary inventory; no Lean statement proves it. The conjunct does not change the experiments: HB-111 and HB-112 still run their hand-written receive and opening programs, and `ReceiveBridge` states equalities between those programs and the transcriptions next to the unchanged bounds.

Not covered, as in `PqxdhOpenContextBridge`: frame decoding, including the check that decoding consumed the whole input and the sequence read from the frame, stays outside the proof, because messages are arbitrary byte strings that each side knows how to decode. The empty-input rejection is not transcribed. The realization of the KDF query by `ratchet_hkdf` (OR-07), the kernel `take` and `put` (OR-12) and the serialization of operations on one owner remain adapter trust. HB-112's experiments also receive through the symbolic chain owner `RawCtxChainOwner.rawReceive`, and this module does not compose `ReceiveBridge` with that driver.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge

/-! ## The receive bridge -/

section Receive
open PqxdhOpenContextBridge

/-- The receive bridge: `PqxdhOpenContextBridge.ContextBridge` together with the universally quantified statements of `PqxdhOpenContextBridge.decoded_receive_native` (the decoded-frame transcription `executeDecoded` equals, wrapped in `ok`, the branch of `RawCtxWholeOwner.rawReceive` after decoding and before publication, at the native opening interface `RawCtxSourceOpen.nativeAdapter`) and `PqxdhOpenContextBridge.decoded_after_root` (the same equality at the interface of the HB-111 target raw-opening site `PqxdhBeaconPhase2Shared.afterRoot`, for every `Response` and `Shared` type), each under B12's representation conditions. -/
def ReceiveBridge : Prop :=
  ContextBridge ∧
  (∀ (erased : Std.Array Std.U8 229#usize) (kernel : ConcreteRatchetKernel) (expected : Std.U64)
      (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) (associatedData : Pqxdh.Bytes)
      (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize),
    RawCtxNativeFramePrelude.sliceBytes payload = frame.payload →
    absBytes ad = associatedData →
    executeDecoded erased kernel expected frame payload ad =
      (fun result => ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
        (if RawCtxReceive.ValidFrame expected associatedData frame then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
              ⟨raw, frame, associatedData⟩)
        else pure (kernel, .None))) ∧
  (∀ {Response Shared : Type} (erased : Std.Array Std.U8 229#usize) (kernel : ConcreteRatchetKernel)
      (expected : Std.U64) (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame)
      (associatedData : Pqxdh.Bytes) (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize),
    RawCtxNativeFramePrelude.sliceBytes payload = frame.payload →
    absBytes ad = associatedData →
    simulateQ (PqxdhBeaconPhase2Shared.rawLift (Response := Response) (Shared := Shared))
        (executeDecoded erased kernel expected frame payload ad) =
      (fun result => ok result) <$> simulateQ PqxdhBeaconPhase2Shared.rawLift
        (simulateQ RawCtxSourceOpen.nativeAdapter
          (if RawCtxReceive.ValidFrame expected associatedData frame then
            simulateQ RawCtxWholeOwner.adapter
              (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
                ⟨raw, frame, associatedData⟩)
          else pure (kernel, .None))))

/-- The receive bridge holds, by `context_bridge`, `decoded_receive_native` and `decoded_after_root`. -/
theorem receive_bridge : ReceiveBridge :=
  ⟨context_bridge, decoded_receive_native, @decoded_after_root⟩

end Receive

/-! ## Headline statements with the receive bridge -/

section Headlines
open PqxdhHeadlineBridges
open PqxdhOpenBridges (OpenBridge)
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhChallengeSecretQueryBounds PqxdhAuthenticatedRootPrepareBounds
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf
open ENNReal
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)

/-- HB-111 with bridges B1-B10, B12 and the receive bridge in the statement: the statement of `PqxdhOpenBridges.authenticated_native_root_bound_bridged_open` (HB-111's bound and reached Server representation, bridges B1-B10 and B12, same hypotheses) together with `ReceiveBridge`, which relates hand-written Lean transcriptions of the unextracted adapter functions `decrypt_message_with_ratchet` and `execute_open`, calling the extracted receive and opening phases, to the experiments' receive driver and post-decoding raw receive. The experiments are unchanged and still run the hand-written receive and opening programs. -/
theorem authenticated_native_root_bound_bridged_receive
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    (let p := protocol env kem attachedVerify primitives program post
    ((actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧
    AcceptBridge env baseImpl kem attachedVerify primitives program post secretIdentity ∧
    ValidateInitBridge ∧
    OpenBridge) ∧
    ReceiveBridge :=
  ⟨PqxdhOpenBridges.authenticated_native_root_bound_bridged_open env baseImpl kem attachedVerify primitives
      program post c compatible adapter functional hmac sourceCorrect fallback ordinaryFallback secretIdentity
      initialMatch,
    receive_bridge⟩

/-- HB-111 for the experiment that executes the extracted acceptance on its accepted branch: the statement of `PqxdhOpenBridges.authenticated_extracted_root_bound_open` (same hypotheses) together with `ReceiveBridge`, which relates hand-written Lean transcriptions of the unextracted adapter functions `decrypt_message_with_ratchet` and `execute_open`, calling the extracted receive and opening phases, to the experiments' receive driver and post-decoding raw receive. The experiments are unchanged and still run the hand-written receive and opening programs. -/
theorem authenticated_extracted_root_bound_receive
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    (let p := protocol env kem attachedVerify primitives program post
    ((extractedActual env baseImpl kem attachedVerify primitives program post secretIdentity).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    (∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2) ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    OpenBridge) ∧
    ReceiveBridge :=
  ⟨PqxdhOpenBridges.authenticated_extracted_root_bound_open env baseImpl kem attachedVerify primitives
      program post c compatible adapter functional hmac sourceCorrect fallback ordinaryFallback secretIdentity
      initialMatch,
    receive_bridge⟩

variable (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)

/-- HB-112 with bridges B1-B8, B10, B11, B12 and the receive bridge in the statement: the statement of `PqxdhOpenBridges.evolving_bound_bridged_open` (HB-112's bound, bridges B1-B8, B10, B11 and B12, same hypotheses) together with `ReceiveBridge`, which relates hand-written Lean transcriptions of the unextracted adapter functions `decrypt_message_with_ratchet` and `execute_open`, calling the extracted receive and opening phases, to the experiments' receive driver and post-decoding raw receive. The experiments are unchanged and still run the hand-written receive and opening programs. HB-112's symbolic chain receive driver is not composed with `ReceiveBridge`. -/
theorem evolving_bound_bridged_receive (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    ((PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    EvolvingAcceptBridge env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
      secretIdentity ∧
    OpenBridge) ∧
    ReceiveBridge :=
  ⟨PqxdhOpenBridges.evolving_bound_bridged_open env baseImpl kem attachedVerify primitives program
      post c selected number ancestors disclosed positive compatible adapter functional hmac correct fallback
      ordinaryFallback secretIdentity initialMatch,
    receive_bridge⟩

/-- HB-112 for the experiment that executes the extracted acceptance on its accepted branch: the statement of `PqxdhOpenBridges.evolving_extracted_bound_open` (same hypotheses) together with `ReceiveBridge`, which relates hand-written Lean transcriptions of the unextracted adapter functions `decrypt_message_with_ratchet` and `execute_open`, calling the extracted receive and opening phases, to the experiments' receive driver and post-decoding raw receive. The experiments are unchanged and still run the hand-written receive and opening programs. HB-112's symbolic chain receive driver is not composed with `ReceiveBridge`. -/
theorem evolving_extracted_bound_receive (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    ((extractedEvolvingActual env baseImpl kem attachedVerify primitives program post selected number ancestors
        disclosed secretIdentity).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed) ≤
      PqxdhAuthenticatedEvolvingSecrecy.loss env baseImpl kem attachedVerify primitives program post selected
        number ancestors disclosed c hmac fallback ordinaryFallback ∧
    PrepareBridge ∧ CommitBridge ∧ BeaconStartBridge ∧ BeaconCommitBridge ∧ RegistrationIdBridge ∧
    CommitmentTranscriptBridge ∧ SendFinishBridge ∧ FramePayloadBridge ∧ ValidateInitBridge ∧
    OpenBridge) ∧
    ReceiveBridge :=
  ⟨PqxdhOpenBridges.evolving_extracted_bound_open env baseImpl kem attachedVerify primitives program
      post c selected number ancestors disclosed positive compatible adapter functional hmac correct fallback
      ordinaryFallback secretIdentity initialMatch,
    receive_bridge⟩

end Headlines

end BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges

/-- info: 'BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.receive_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.receive_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.authenticated_native_root_bound_bridged_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.authenticated_native_root_bound_bridged_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.authenticated_extracted_root_bound_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.authenticated_extracted_root_bound_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.evolving_bound_bridged_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.evolving_bound_bridged_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.evolving_extracted_bound_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhReceiveHeadlineBridges.evolving_extracted_bound_receive
