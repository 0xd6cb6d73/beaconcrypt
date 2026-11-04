-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPublication
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual source first-record and response serialization form one completion program before the literal mutable-map installer. Successful SDK responses yield a same-run publication/insertion receipt with complete external states; no unrelated supported execution is selected. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildBody (Server Reply)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {State : Type} [localOps : LocalOperations (RustT (StateT State ProbComp))]
variable [containers : ContainerOperations (RustT (StateT State ProbComp))]
variable [children : ChildOperations (RustT (StateT State ProbComp))]

noncomputable def completion (operations : AdapterPublicServerPublication.Primitives (StateT State ProbComp))
    (kdf : AdapterPublicServerRecord.Kdf (StateT State ProbComp)) (initial : registration.ServerInitialKdf) :=
  RegistrationServerSourceCompletionReceipt.program
    (AdapterPublicServerRecord.recordOperations kdf) AdapterPublicServerRecord.sealLeaf
    (fun transcript => (children.commitmentHash transcript).run) AdapterPublicServerRecord.writeLeaf
    (AdapterPublicServerPublication.outgoing operations) AdapterPublicServerPublication.encode initial

theorem source (operations : AdapterPublicServerPublication.Primitives (StateT State ProbComp))
    (self : Server) (contract : AdapterPublicServerPublication.Contract operations self)
    (kdf : AdapterPublicServerRecord.Kdf (StateT State ProbComp))
    (kdfContract : AdapterPublicServerRecord.KdfContract kdf) (initial : registration.ServerInitialKdf) :
    (AdapterPublicServerBuildBody.record (m := StateT State ProbComp) self initial).run = (do
      let published ← completion operations kdf initial
      AdapterPublicServerPublication.afterPublication self published) := by
  rw [AdapterPublicServerPublication.record operations self contract kdf kdfContract]
  unfold completion RegistrationServerSourceCompletionReceipt.program
  rw [bind_assoc]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => simp only [RegistrationNativePlatformServerPublication.continueResult, pure_bind,
      AdapterPublicServerPublication.afterRecord, AdapterPublicServerPublication.afterPublication]
  | ok result => cases result <;> simp only [RegistrationNativePlatformServerPublication.continueResult,
      pure_bind, AdapterPublicServerPublication.afterRecord, AdapterPublicServerPublication.afterPublication]

theorem success (operations : AdapterPublicServerPublication.Primitives (StateT State ProbComp))
    (self : Server) (contract : AdapterPublicServerPublication.Contract operations self)
    (kdf : AdapterPublicServerRecord.Kdf (StateT State ProbComp))
    (kdfContract : AdapterPublicServerRecord.KdfContract kdf) (initial : registration.ServerInitialKdf)
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.record (m := StateT State ProbComp) self initial).run).run before)) :
    ∃ published middle pending,
      (.ok (.Ok published), middle) ∈ support ((completion operations kdf initial).run before) ∧
      peer.begin_peer_insert self.control published = .ok (.Ok pending) ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.install (m := StateT State ProbComp) self pending).run).run middle) := by
  rw [source operations self contract kdf kdfContract initial] at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨published, middle⟩, reached, continued⟩ := supported
  cases published with
  | fail error | div => simp only [AdapterPublicServerPublication.afterPublication, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok result => cases result with
    | Err previous => simp only [AdapterPublicServerPublication.afterPublication, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | Ok published =>
      change (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.checked (m := StateT State ProbComp) self (peer.begin_peer_insert self.control published)
          (AdapterPublicServerBuildBody.install self)).run).run middle) at continued
      rw [AdapterPublicServerRecord.checked] at continued
      cases began : peer.begin_peer_insert self.control published with
      | fail error | div => simp only [began, AdapterPublicServerRecord.resumeResult, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
      | ok result => cases result with
        | Err previous => simp only [began, AdapterPublicServerRecord.resumeResult, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
        | Ok pending => exact ⟨published, middle, pending, reached, began, by simpa only [began, AdapterPublicServerRecord.resumeResult] using continued⟩

theorem parsed (operations : AdapterPublicServerPublication.Primitives (StateT State ProbComp))
    (self : Server) (contract : AdapterPublicServerPublication.Contract operations self)
    (kdf : AdapterPublicServerRecord.Kdf (StateT State ProbComp))
    (kdfContract : AdapterPublicServerRecord.KdfContract kdf) (initial : registration.ServerInitialKdf)
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.record (m := StateT State ProbComp) self initial).run).run before))
    (initialParsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key) :
    ∃ published middle pending,
      (.ok (.Ok published), middle) ∈ support ((completion operations kdf initial).run before) ∧
      peer.begin_peer_insert self.control published = .ok (.Ok pending) ∧
      AdapterPublicServerToken.ParsedKey pending.peer.binding.beacon_identity_public_key ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.install (m := StateT State ProbComp) self pending).run).run middle) := by
  obtain ⟨published, middle, pending, reached, began, installed⟩ := success operations self contract kdf kdfContract initial response current before after supported
  refine ⟨published, middle, pending, reached, began, ?_, installed⟩
  exact AdapterPublicServerCompletionInstall.insertion_parsed self.control initial published pending
    (RegistrationServerSourceCompletionReceipt.stateful _ _ _ _ _ _ initial (.ok (.Ok published)) before middle reached) began initialParsed
end BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt.success

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt.parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt.parsed
