import BeaconcryptCore.Computational.PqxdhInitialBuilderReceipt
import BeaconcryptCore.Computational.PqxdhInitialFinishReceipt
import BeaconcryptCore.Computational.PqxdhInitialInstallOccurrence
import BeaconcryptCore.Computational.RawCtxPendingNativeCalls
import BeaconcryptCore.Computational.PqxdhInitialReceiptConstruction
import BeaconcryptCore.Computational.PqxdhInitialOriginFinishPath
import BeaconcryptCore.Computational.RawCtxRetainedNativeCycles

/-!
The complete Server Builder and Beacon finish publish kernels on the two literal chains in their own source initializer receipts. The actual first Server send precedes erasure, writing and publication; failed-writer sends remain attributable to the attempted initializer without inventing an installed owner. Full source state and optional branches remain in the support witnesses. Fixed retained-table reachability is a functional source property, not a distributional replacement or secrecy theorem.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialReceiptPublication
open PqxdhInitialGenericPublication
open PqxdhServerRegistrationPublication (AuxSpec Response firstContext responseFields)
variable {Kernel M P Auxiliary ξ : Type} {base : OracleSpec.{0, 0} ξ}

/-- Every executed first-send tail begins with that exact supplied kernel and authenticated context; its full optional result and later effects are retained even when no peer is published. -/
theorem sent (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : P) (entry : State Kernel M P (List Pqxdh.Bytes)) (before : Auxiliary)
    (result : (Option Response × State Kernel M P (List Pqxdh.Bytes)) × Auxiliary)
    (supported : result ∈ support ((afterInitialization calls aux candidate authenticated kernel metadata entry).run before)) :
    ∃ (sent : Kernel × Option RawCtxSourceSend.Encrypted) (atSend : Auxiliary),
      (sent, atSend) ∈ support ((calls.send kernel (firstContext candidate authenticated)).run before) ∧
      result ∈ support ((PqxdhInitialBuilderContext.afterSend aux candidate authenticated metadata entry sent).run atSend) := by
  rw [PqxdhInitialBuilderContext.after_factor] at supported
  simpa only [StateT.run_bind, mem_support_bind_iff, Prod.exists] using supported

/-- A successful local response publishes precisely the advanced kernel from its actual first send, after the literal erase and writer callbacks succeed. -/
theorem published (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : P) (entry : State Kernel M P (List Pqxdh.Bytes)) (before : Auxiliary)
    (response : Response) (updated : State Kernel M P (List Pqxdh.Bytes)) (after : Auxiliary)
    (supported : ((some response, updated), after) ∈ support
      ((afterInitialization calls aux candidate authenticated kernel metadata entry).run before)) :
    ∃ (advanced : Kernel) (encrypted : RawCtxSourceSend.Encrypted) (serialized : Pqxdh.Bytes)
      (atSend atErased : Auxiliary),
      ((advanced, some encrypted), atSend) ∈ support ((calls.send kernel (firstContext candidate authenticated)).run before) ∧
      ((), atErased) ∈ support ((aux (.erase authenticated)).run atSend) ∧
      (some serialized, after) ∈ support ((aux (.write (responseFields candidate encrypted))).run atErased) ∧
      response = ⟨serialized, candidate.key_id⟩ ∧ updated = publish entry candidate advanced metadata := by
  simp only [afterInitialization, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨sent, first, erased, erasedSupport, rest⟩ := supported
  cases encrypted : sent.1.2 <;>
    simp only [encrypted, StateT.run_pure, mem_support_pure_iff, StateT.run_bind, mem_support_bind_iff] at rest
  · cases rest
  · rename_i encryptedValue
    obtain ⟨written, writtenSupport, rest⟩ := rest
    cases serialized : written.1 <;>
      simp only [serialized, StateT.run_pure, mem_support_pure_iff] at rest
    · cases rest
    · rename_i serializedValue
      simp only [Prod.mk.injEq, Option.some.injEq] at rest
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := rest
      refine ⟨sent.1.1, encryptedValue, serializedValue, sent.2, erased.2, ?_, ?_, ?_, rfl, rfl⟩
      · simpa only [← encrypted] using first
      · simpa only [show erased.1 = () from Subsingleton.elim _ _] using erasedSupport
      · simpa only [← serialized] using writtenSupport

/-- The actually published Server peer lies on the two literal source initializer paths under the same retained private table, with the first send and complete publication effects preserved. -/
theorem server_path {A AD PT CT : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (response64 : pqxdh.concrete.InitialRatchetKdfResponse) (kernel : ConcreteRatchetKernel)
    (initialized : PqxdhInitialReplyErasure.kernelOf false response64 = .ok kernel)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (metadata : P) (entry : State (RawCtxPendingOwnerQueries.Kernel RatchetChain) M P (List Pqxdh.Bytes))
    (before : RawCtxSharedPrimitive.SharedState A)
    (response : Response) (updated : State (RawCtxPendingOwnerQueries.Kernel RatchetChain) M P (List Pqxdh.Bytes))
    (after : RawCtxSharedPrimitive.SharedState A)
    (supported : ((some response, updated), after) ∈ support
      ((afterInitialization (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native source writer prior))
        aux candidate authenticated kernel.refined metadata entry).run before)) :
    response.keyId = candidate.key_id ∧
      ∃ peer, updated.server.peers response.keyId = some peer ∧
        RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
          kernel.refined.send_chain kernel.refined.receive_chain ⟨peer.kernel⟩ := by
  obtain ⟨advanced, encrypted, serialized, atSend, _, first, _, _, responseEq, updatedEq⟩ :=
    published (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native source writer prior))
      aux candidate authenticated kernel.refined metadata entry before response updated after supported
  have valid := PqxdhInitialKernelConstruction.supplied_reachable
    (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) false response64 kernel initialized
  have reached := RawCtxRetainedNativeCycles.send_valid source writer prior cr
    kernel.refined.send_chain kernel.refined.receive_chain kernel.refined valid
    (firstContext candidate authenticated) before ((advanced, some encrypted), atSend) first
  subst response
  subst updated
  exact ⟨rfl, ⟨candidate.beacon_identity_public_key, advanced, metadata⟩,
    Function.update_self _ _ _, reached⟩

private theorem after_accepted
    (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (kernel : Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (entry : State Kernel M P (List Pqxdh.Bytes)) (before : Auxiliary)
    (response : Response) (updated : State Kernel M P (List Pqxdh.Bytes)) (after : Auxiliary)
    (supported : (.ok (some response, updated), after) ∈ support
      ((PqxdhInitialBuilderReceipt.afterInitial calls aux kernel candidate data metadata entry).run before)) :
    ∃ atSend, ((some response, updated), after) ∈ support
      ((afterInitialization calls aux candidate
        (Pqxdh.LE64 candidate.key_id.val ++ data.getD PqxdhServerRegistrationPublication.registrationWitness)
        kernel metadata entry).run atSend) := by
  unfold PqxdhInitialBuilderReceipt.afterInitial at supported
  dsimp only at supported
  split at supported
  · simp only [StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
  · split at supported
    · simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨allocated, _, rest⟩ := supported
      cases found : allocated.1
      case false =>
        simp only [found, Bool.not_false, ite_true, StateT.run_pure, mem_support_pure_iff] at rest
        cases rest
      case true =>
        obtain ⟨binding, created, bytes⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
        simp only [found, Bool.not_true, Bool.false_eq_true, ite_false, created,
          PqxdhInitialGenericBuilder.continueRust, StateT.run_map, support_map, bytes] at rest
        obtain ⟨completed, reached, same⟩ := rest
        simp only [Prod.mk.injEq, RustM.ok.injEq] at same
        rcases completed with ⟨value, finalState⟩
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨allocated.2, reached⟩
    · simp only [StateT.run_pure, mem_support_pure_iff] at supported
      cases supported

/-- Every successful candidate response has its own initializer receipt and actually reaches the first-send tail with the source eight-byte binding and application suffix. -/
theorem candidate_published
    (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (entry : State Kernel M P (List Pqxdh.Bytes)) (before : Auxiliary)
    (response : Response) (updated : State Kernel M P (List Pqxdh.Bytes)) (after : Auxiliary)
    (receipt : Option (PqxdhInitialBuilderReceipt.Receipt Kernel))
    (supported : ((.ok (some response, updated), receipt), after) ∈ support
      ((PqxdhInitialBuilderReceipt.candidate calls aux initial candidate data metadata entry).run before)) :
    ∃ (kernel : Kernel) (atSend : Auxiliary), receipt = some ⟨candidate, kernel⟩ ∧ initial = .ok kernel ∧
      ((some response, updated), after) ∈ support
        ((afterInitialization calls aux candidate
          (Pqxdh.LE64 candidate.key_id.val ++ data.getD PqxdhServerRegistrationPublication.registrationWitness)
          kernel metadata entry).run atSend) := by
  unfold PqxdhInitialBuilderReceipt.candidate at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨valid, _, rest⟩ := supported
  cases validFound : valid.1
  case false =>
    simp only [validFound, Bool.not_false, ite_true, StateT.run_pure, mem_support_pure_iff] at rest
    cases rest
  case true =>
    simp only [validFound, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨reserved, _, rest⟩ := rest
    cases reservedFound : reserved.1
    case false =>
      simp only [reservedFound, Bool.not_false, ite_true, StateT.run_pure, mem_support_pure_iff] at rest
      cases rest
    case true =>
      simp only [reservedFound, Bool.not_true, Bool.false_eq_true, ite_false] at rest
      cases initial with
      | fail error =>
        simp only [StateT.run_pure, mem_support_pure_iff] at rest
        cases rest
      | div =>
        simp only [StateT.run_pure, mem_support_pure_iff] at rest
        cases rest
      | ok kernel =>
        simp only [StateT.run_map, support_map] at rest
        obtain ⟨completed, reached, same⟩ := rest
        rcases completed with ⟨value, finalState⟩
        simp only [Prod.mk.injEq] at same
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := same
        obtain ⟨atSend, tail⟩ := after_accepted calls aux kernel candidate data metadata entry
          reserved.2 response updated _ reached
        exact ⟨kernel, atSend, rfl, rfl, tail⟩

/-- Every successfully admitted consumed-input builder reaches its own candidate's literal first-send tail and records the exact initializer, after the original allocation and preparation branches. -/
theorem used_published
    (calls : RawCtxChainOwner.Calls Kernel (StateT Auxiliary (OracleComp base)))
    (aux : QueryImpl AuxSpec (StateT Auxiliary (OracleComp base)))
    (initial : RustM Kernel) (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes)
    (metadata : P) (entry : State Kernel M P (List Pqxdh.Bytes)) (before : Auxiliary)
    (response : Response) (updated : State Kernel M P (List Pqxdh.Bytes)) (after : Auxiliary)
    (recorded : Option (PqxdhInitialBuilderReceipt.Receipt Kernel))
    (supported : ((.ok (some response, updated), recorded), after) ∈ support
      ((PqxdhInitialBuilderReceipt.used calls aux initial pending data metadata entry).run before)) :
    ∃ (receipt : PqxdhInitialBuilderReceipt.Receipt Kernel) (atSend : Auxiliary),
      recorded = some receipt ∧ initial = .ok receipt.initial ∧
      ((some response, updated), after) ∈ support
        ((afterInitialization calls aux receipt.candidate
          (Pqxdh.LE64 receipt.candidate.key_id.val ++ data.getD PqxdhServerRegistrationPublication.registrationWitness)
          receipt.initial metadata entry).run atSend) := by
  unfold PqxdhInitialBuilderReceipt.used at supported
  split at supported
  all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported }
  rename_i next allocated
  dsimp only at supported
  cases prepared : PqxdhRegistrationInputs.prepare entry.control pending
    ⟨entry.server.identity, entry.identityKeyId⟩
    (if (entry.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
  | fail error => simp only [prepared, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | div => simp only [prepared, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
  | ok outcome =>
    cases outcome with
    | Err error => simp only [prepared, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
    | Ok candidate =>
      simp only [prepared] at supported
      obtain ⟨kernel, atSend, recorded, initialized, tail⟩ := candidate_published calls aux initial candidate data
        metadata entry before response updated after recorded supported
      exact ⟨⟨candidate, kernel⟩, atSend, recorded, initialized, tail⟩

section Builder
open PqxdhInitialPendingPost
variable {ι Chain I D K X SourceResponse Shared : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Complete indexed Builder success always records its actual initializer and publishes the matching assigned peer. The installed kernel is exactly the supported first-send return from that initializer, with the literal binding-prefixed plaintext. -/
theorem build_published
    (impl : QueryImpl (Spec extra Chain I D K X SourceResponse Shared S B) (StateT Auxiliary (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) (state : Auxiliary)
    (result : ((RustM (Option Response) × Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf Chain))) ×
      Front Chain M P I D K S B) × Auxiliary)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialBuilderReceipt.build source initial sender index metadata input).run before)).run state))
    (response : Response) (accepted : result.1.1.1 = .ok (some response)) :
    ∃ receipt, result.1.1.2 = some receipt ∧ initial = .ok receipt.initial ∧ response.keyId = receipt.candidate.key_id ∧
      ∃ (advanced : KernelOf Chain) (encrypted : RawCtxSourceSend.Encrypted) (atSend atSent : Auxiliary),
        ((result.1.2.roles.1.1 index).server.peers response.keyId) =
          some ⟨receipt.candidate.beacon_identity_public_key, advanced, metadata⟩ ∧
        ((advanced, some encrypted), atSent) ∈ support
          (((RawCtxGenericOwnerInterpretation.interpretedCalls impl calls).send receipt.initial
            (firstContext receipt.candidate
              (Pqxdh.LE64 receipt.candidate.key_id.val ++ input.application.getD PqxdhServerRegistrationPublication.registrationWitness))).run atSend) := by
  simp only [PqxdhInitialBuilderReceipt.build, StateT.run, simulateQ_map] at supported
  rw [PqxdhInitialBuilderReceipt.ready_interpretation] at supported
  change result ∈ support (StateT.run _ state) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨original, reached, rfl⟩ := supported
  rcases original with ⟨⟨outcome, recorded⟩, after⟩
  cases outcome with
  | fail error => cases accepted
  | div => cases accepted
  | ok output =>
    rcases output with ⟨optional, updated⟩
    simp only [PqxdhInitialPendingBuilder.reinstall, RustM.ok.injEq] at accepted
    subst optional
    obtain ⟨receipt, atSend, recordedEq, initialized, tail⟩ := used_published
      (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ auxForward)
      initial _ input.application metadata _ state response updated after recorded reached
    obtain ⟨advanced, encrypted, serialized, atSent, _, first, _, _, responseEq, updatedEq⟩ :=
      published (RawCtxGenericOwnerInterpretation.interpretedCalls impl calls) (impl ∘ₛ auxForward)
        receipt.candidate _ receipt.initial metadata _ atSend response updated after tail
    have keyEq : response.keyId = receipt.candidate.key_id := congrArg Response.keyId responseEq
    refine ⟨receipt, recordedEq, initialized, keyEq, advanced, encrypted, atSend, atSent, ?_, first⟩
    simp only [PqxdhInitialPendingBuilder.reinstall, PqxdhInitialPendingBuilder.install,
      Function.update_self, updatedEq, publish, keyEq]

/-- The successful Server builder necessarily passes the actual occurrence map's assigned-key and present-peer filters. Its token labels this source attempt, independently of all secret and transcript byte equalities. -/
theorem build_occurrence
    (impl : QueryImpl (Spec extra Chain I D K X SourceResponse Shared S B) (StateT Auxiliary (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front Chain M P I D K S B) (state : Auxiliary)
    (result : ((RustM (Option Response) × Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf Chain))) ×
      Front Chain M P I D K S B) × Auxiliary)
    (supported : result ∈ support ((simulateQ impl
      ((PqxdhInitialBuilderReceipt.build source initial sender index metadata input).run before)).run state))
    (response : Response) (accepted : result.1.1.1 = .ok (some response))
    (started : PqxdhInitialInstallOccurrence.Trace Chain SourceResponse Shared S B) (attempt : Nat) :
    ∃ receipt, result.1.1.2 = some receipt ∧
      (PqxdhInitialInstallOccurrence.built started attempt input index result.1.2 result.1.1.1 result.1.1.2).installed
        (.server index response.keyId) =
          some ⟨⟨.server index response.keyId, attempt⟩, .server input receipt⟩ := by
  obtain ⟨receipt, recorded, _, keyEq, advanced, _, _, _, peer, _⟩ :=
    build_published impl source initial sender index metadata input before state result supported response accepted
  refine ⟨receipt, recorded, ?_⟩
  rw [keyEq] at peer ⊢
  simp only [PqxdhInitialInstallOccurrence.built, recorded, accepted, keyEq, decide_true,
    peer, Option.isSome_some, Bool.and_true, PqxdhInitialInstallOccurrence.note,
    ite_true, Function.update_self]

section Retained
variable {A AD PT CT : Type}

/-- The original pending interface uses its actual native and public services under one retained private table. All read and external callback replies and state effects remain supplied through their original interfaces. -/
noncomputable def retained (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf RatchetChain) S B)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (external : QueryImpl (External extra RatchetChain I D K X SourceResponse Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    QueryImpl (Spec extra RatchetChain I D K X SourceResponse Shared S B)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl query => RawCtxPendingFamilyLiveQueries.handler
      (RawCtxPendingNativeCalls.pending (RawCtxFunctionalFamily.native source writer prior)
        (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift)) reader query
  | .inr query => external query

private theorem retained_calls (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf RatchetChain) S B)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (external : QueryImpl (External extra RatchetChain I D K X SourceResponse Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :
    RawCtxGenericOwnerInterpretation.interpretedCalls (retained source writer prior reader external) calls =
      RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native source writer prior) := by
  have forwarding : retained source writer prior reader external ∘ₛ primitiveForward =
      RawCtxPendingNativeCalls.pending (RawCtxFunctionalFamily.native source writer prior)
        (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift) := by
    funext query
    simp [QueryImpl.compose, primitiveForward, retained, OracleSpec.query, RawCtxPendingFamilyLiveQueries.handler]
  simp only [calls, RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, forwarding]
  exact RawCtxPendingNativeCalls.calls_interpretation _ _

/-- In the complete actual retained-source Builder, every accepted response installs the kernel on the two exact chains in its own source initializer receipt. The source supplied-response constructor and native first send discharge both links. -/
theorem build_native_path (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf RatchetChain) S B)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (external : QueryImpl (External extra RatchetChain I D K X SourceResponse Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (response64 : pqxdh.concrete.InitialRatchetKdfResponse)
    (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (input : PqxdhPrivateAcceptedRoot.Ready) (before : Front RatchetChain M P I D K S B)
    (state : RawCtxSharedPrimitive.SharedState A)
    (result : ((RustM (Option Response) × Option (PqxdhInitialBuilderReceipt.Receipt (KernelOf RatchetChain))) ×
      Front RatchetChain M P I D K S B) × RawCtxSharedPrimitive.SharedState A)
    (supported : result ∈ support ((simulateQ (retained source writer prior reader external)
      ((PqxdhInitialBuilderReceipt.build source
        (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)
        sender index metadata input).run before)).run state))
    (response : Response) (accepted : result.1.1.1 = .ok (some response)) :
    ∃ receipt, result.1.1.2 = some receipt ∧ response.keyId = receipt.candidate.key_id ∧
      ∃ peer, ((result.1.2.roles.1.1 index).server.peers response.keyId) = some peer ∧
        RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
          receipt.initial.send_chain receipt.initial.receive_chain ⟨peer.kernel⟩ := by
  obtain ⟨receipt, recorded, _, keyEq, advanced, encrypted, atSend, atSent, peer, sent⟩ :=
    build_published (retained source writer prior reader external) source _ sender index metadata input
      before state result supported response accepted
  have initialPath := (PqxdhInitialReceiptConstruction.server (retained source writer prior reader external)
    source response64 sender index metadata input before state result supported receipt recorded
    (withInterpreter cr (RawCtxFunctionalFamily.execute prior))).2
  rw [retained_calls] at sent
  have advancedPath := RawCtxRetainedNativeCycles.send_valid source writer prior cr
    receipt.initial.send_chain receipt.initial.receive_chain receipt.initial initialPath
    _ atSend ((advanced, some encrypted), atSent) sent
  exact ⟨receipt, recorded, keyEq, ⟨receipt.candidate.beacon_identity_public_key, advanced, metadata⟩, peer, advancedPath⟩

end Retained
end Builder

section Beacon
open PqxdhInitialReceiptConstruction PqxdhInitialGenericBeacon
variable {A N AD PT CT Response Shared I D K X Origin : Type}

/-- The actual retained native calls inside the same shared, identity and root-cache state as the concrete Beacon initializer. Only tuple association changes. -/
noncomputable def nativeCalls (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior) :
    RawCtxChainOwner.Calls (RawCtxPendingOwnerQueries.Kernel RatchetChain) (StateT (InitialState A N) ProbComp) where
  receive kernel target context := fun state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((PqxdhInitialBeaconAmbient.liftCalls (RawCtxGenericNativeCalls.calls
        (RawCtxFunctionalFamily.native source writer prior))).receive kernel target context state.1).run state.2)
  send kernel context := fun state =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((PqxdhInitialBeaconAmbient.liftCalls (RawCtxGenericNativeCalls.calls
        (RawCtxFunctionalFamily.native source writer prior))).send kernel context state.1).run state.2)

private theorem native_rules (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (sendOrigin receiveOrigin : RatchetChain) :
    RawCtxFamilyStateInvariant.Rules (nativeCalls (A := A) (N := N) source writer prior)
      (fun _ _ => True) (fun kernel _ => RoleReachable
        (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) sendOrigin receiveOrigin ⟨kernel⟩) where
  refl := fun _ => trivial
  trans := fun _ _ _ _ _ => trivial
  mono := fun _ _ _ _ valid => valid
  receive := by
    intro entry target context state result supported
    simp only [nativeCalls, PqxdhInitialBeaconAmbient.liftCalls, PqxdhInitialBeaconAmbient.lift,
      StateT.run, Functor.map_map, support_map] at supported
    obtain ⟨actual, reached, rfl⟩ := supported
    exact ⟨trivial, fun valid => RawCtxRetainedNativeCycles.receive_valid source writer prior cr
      sendOrigin receiveOrigin entry valid target context state.1.1 actual reached⟩
  send := by
    intro entry context state result supported
    simp only [nativeCalls, PqxdhInitialBeaconAmbient.liftCalls, PqxdhInitialBeaconAmbient.lift,
      StateT.run, Functor.map_map, support_map] at supported
    obtain ⟨actual, reached, rfl⟩ := supported
    exact ⟨trivial, fun valid => RawCtxRetainedNativeCycles.send_valid source writer prior cr
      sendOrigin receiveOrigin entry valid context state.1.1 actual reached⟩

private theorem opened_kernel (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : Staged (RawCtxPendingOwnerQueries.Kernel RatchetChain))
    (found : afterOpening candidate kernel reply = some staged) : staged.kernel = kernel := by
  cases reply with
  | none => cases found
  | some opened =>
    simp only [afterOpening] at found
    split at found
    · cases found
    · split at found
      · split at found
        · cases found
        · cases found; rfl
      · cases found

/-- The actual complete application getter and first raw receive preserve both initializer chains under the same retained interpreter. Rejections and arbitrary getter state effects stay in the source run. -/
theorem beacon_tail_path (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Shared.Prepared Response Shared)
    (kernel : RawCtxPendingOwnerQueries.Kernel RatchetChain)
    (constructed : ConcreteRatchetKernel.new kernel.send_chain kernel.receive_chain = .ok ⟨kernel⟩)
    (before : InitialState A N) (result : Option (Staged (RawCtxPendingOwnerQueries.Kernel RatchetChain)) × InitialState A N)
    (supported : result ∈ support ((afterInitial (nativeCalls source writer prior) application decode prepared kernel).run before)) :
    ∀ staged, result.1 = some staged → RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
      kernel.send_chain kernel.receive_chain ⟨staged.kernel⟩ := by
  simp only [afterInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨applicationResult, _, rest⟩ := supported
  cases found : applicationResult.1 with
  | none =>
    simp only [found, StateT.run_pure, mem_support_pure_iff] at rest
    subst result
    intro staged impossible
    cases impossible
  | some raw =>
    simp only [found, StateT.run_bind, mem_support_bind_iff] at rest
    obtain ⟨received, reached, final⟩ := rest
    simp only [StateT.run_pure, mem_support_pure_iff] at final
    subst result
    have preserved := (RawCtxFamilyStateInvariant.raw (nativeCalls source writer prior) _ _
      (native_rules source writer prior cr kernel.send_chain kernel.receive_chain) decode raw
      (localOwner (PqxdhBeaconPhase2Shared.clearedMetadata prepared.metadata) kernel)
      applicationResult.2 received reached).2
    obtain ⟨created, creation, _, valid⟩ := new_reachable
      (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) kernel.send_chain kernel.receive_chain
    have same : created = ⟨kernel⟩ := RustM.ok.inj (creation.symm.trans constructed)
    intro staged produced
    rw [opened_kernel _ _ _ staged produced]
    exact preserved (by simpa only [same, localOwner] using valid)

/-- An actual successful Beacon installation is reachable from the exact two chains recorded before its first receive. The concrete retained initializer discharges source construction; no arbitrary initializer or path-preservation callback premise is used. -/
theorem beacon_path (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (prior : RawCtxSelectedParentTable.Prior)
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (selected : PqxdhCorrelatedExtractFamily.Message) (previousRoot : PqxdhSecretInputKdf.RootOutput)
    (response : PqxdhInitialRootLabelService.Response)
    (mark : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (InitialState A N) ProbComp))
    (application : Response → StateT (InitialState A N) ProbComp (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (entry : RawCtxGenericRoleStorage.BeaconState (PqxdhInitialPendingPost.KernelOf RatchetChain) I D K)
    (before : InitialState A N)
    (result : PqxdhInitialFinishReceipt.Result (PqxdhInitialPendingPost.KernelOf RatchetChain) Origin I D K Response
      PqxdhPhase2DecapsulationRouting.Shared × InitialState A N)
    (supported : result ∈ support ((PqxdhInitialFinishReceipt.owner mark pre (nativeCalls source writer prior)
      application (initial source selected previousRoot response) decode raw entry).run before))
    (receipt : PqxdhInitialFinishReceipt.Receipt (PqxdhInitialPendingPost.KernelOf RatchetChain) Response PqxdhPhase2DecapsulationRouting.Shared)
    (recorded : result.1.2 = some receipt)
    (installed : PqxdhInitialPendingPost.KernelOf RatchetChain)
    (found : PqxdhInitialOriginFinishPath.beaconKernel result.1.1.1.2 = some installed) :
    RoleReachable (withInterpreter cr (RawCtxFunctionalFamily.execute prior))
      receipt.initial.send_chain receipt.initial.receive_chain ⟨installed⟩ := by
  obtain ⟨control, _, _, _, atPrepared, atInitial, staged, _, _, initialized, completed, finished⟩ :=
    PqxdhInitialFinishReceipt.owner_origin mark pre (nativeCalls source writer prior) application
      (initial source selected previousRoot response) decode raw entry before result supported receipt recorded
  have constructed := (initial_constructed source selected previousRoot response receipt.prepared.root
    (withInterpreter cr (RawCtxFunctionalFamily.execute prior)) atPrepared atInitial receipt.initial initialized).1
  have paths := beacon_tail_path source writer prior cr application decode receipt.prepared receipt.initial
    constructed atInitial (staged, result.2) completed
  rw [finished] at found
  obtain ⟨actual, produced, same, _⟩ := PqxdhInitialOriginFinishPath.finish_kernel control entry staged installed found
  simpa only [same] using paths actual produced

end Beacon
end BeaconcryptCore.Computational.PqxdhInitialReceiptPublication

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.sent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.sent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.published

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.server_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.server_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.candidate_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.candidate_published

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.used_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.used_published

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.build_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.build_published

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.build_occurrence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.build_occurrence

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.build_native_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.build_native_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.beacon_tail_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.beacon_tail_path

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.beacon_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialReceiptPublication.beacon_path
