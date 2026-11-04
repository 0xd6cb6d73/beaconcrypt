-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication
import BeaconcryptCore.Refinement.AdapterPublicInitPublication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual source Server hash/sign/serialize suffix runs the maintained native response-publication controller with the literal stateful source writer. Narrow hash and ML signing functional interpretations are separate leaves, while source installation remains its actual container body. Every absent signature, failed allocation, failed publication and reached shared poststate remains visible. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPublication
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
open AdapterPublicServerBuildBody (Server Reply)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)]
variable [containers : ContainerOperations (RustT m)] [children : ChildOperations (RustT m)]

structure Primitives (m : Type → Type) where
  hash : registration.HashRequest → m CtxRomAuth.CtxDigest
  sign : registration.MldsaSigningRequest → m (core.option.Option (alloc.vec.Vec U8))

structure Contract (operations : Primitives m) (self : Server) : Prop where
  hash : ∀ request, (children.executeHash request).run =
    (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> operations.hash request
  sign : ∀ request, (localOps.auth_MldsaIdentity_sign_requested (platform.arcView self.identity).mldsa_identity request).run =
    RustM.ok <$> operations.sign request

omit localOps containers children in
def outgoing (operations : Primitives m) : QueryImpl RegistrationSigningShared.Spec m
  | .hash request => operations.hash request
  | .sign request _ _ => AdapterPublicInitPublication.borrowed <$> operations.sign request

noncomputable def encode (view : registration.SignedResponseView) : m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  (children.encodeResponse (RegistrationNativeSourceEncoders.responseSyntax view)).run

noncomputable def afterPublication (self : Server) :
    RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) → m (RustM Reply)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok (.None, self))
  | .ok (.Ok published) =>
      (AdapterPublicServerBuildBody.checked self (peer.begin_peer_insert self.control published)
        (AdapterPublicServerBuildBody.install self)).run

omit localOps children in
private theorem fused {A : Type} (self : Server) (action : RustM (core.result.Result A pqxdh.ServerState))
    (next : A → m (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))) :
    (do let result ← RegistrationNativePlatformServerPublication.continueResult action next
        afterPublication self result) = AdapterPublicServerRecord.resumeResult self action
          (fun value => do let result ← next value; afterPublication self result) := by
  cases action with
  | fail error | div => simp only [RegistrationNativePlatformServerPublication.continueResult,
      pure_bind, afterPublication, AdapterPublicServerRecord.resumeResult]
  | ok result => cases result <;> simp only [RegistrationNativePlatformServerPublication.continueResult,
      pure_bind, afterPublication, AdapterPublicServerRecord.resumeResult]

omit localOps in
theorem publish (self : Server) (pending : registration.ServerResponseReady) :
    (AdapterPublicServerBuildBody.publish (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformServerPublication.ready encode pending
      afterPublication self result) := by
  unfold AdapterPublicServerBuildBody.publish RegistrationNativePlatformServerPublication.ready
  cases requested : pending.message with
  | fail error | div => simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerPublication.continueWith, afterPublication]
  | ok view =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerPublication.continueWith, encode, bind_assoc]
    apply bind_congr
    intro encoded
    cases encoded with
    | fail error | div => simp only [bind_tc_fail, bind_tc_div, afterPublication]
    | ok encoded =>
      simp only [AdapterPublicServerRecord.checked, bind_tc_ok]
      cases published : pending.publish encoded with
      | fail error | div => rfl
      | ok answer => cases answer <;> simp only [AdapterPublicServerRecord.resumeResult, afterPublication, AdapterPublicServerRecord.checked]

noncomputable def signing (self : Server) (pending : registration.ServerResponseSigning) : RustT m Reply := do
  let identity ← liftRust (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref self.identity)
  let request ← liftRust pending.request
  let signature ← localOps.auth_MldsaIdentity_sign_requested identity.mldsa_identity request
  let signatureView ← liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) signature)
  AdapterPublicServerBuildBody.checked self (pending.resume signatureView) (AdapterPublicServerBuildBody.publish self)

theorem signing_source (operations : Primitives m) (self : Server) (contract : Contract operations self)
     (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    (signing (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformServerPublication.signing (outgoing operations) encode payload digest pending
      afterPublication self result) := by
  unfold signing RegistrationNativePlatformServerPublication.signing
  simp only [RustT.run_bind, RustT.run_liftRust, CoreModels.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, pure_bind]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationNativePlatformServerPublication.continueWith, afterPublication]
  | ok request =>
    simp only [Contract.sign (self := self) contract, RegistrationNativePlatformServerPublication.continueWith,
      outgoing, bind_map_left, bind_assoc]
    apply bind_congr
    intro signature
    simp only [AdapterPublicInitPublication.borrowed_source,
      AdapterPublicServerRecord.checked, fused, publish]

theorem sign (operations : Primitives m) (self : Server) (contract : Contract operations self)
    (pending : registration.ServerResponseHash) :
    (AdapterPublicServerBuildBody.sign (m := m) self pending).run = (do
      let result ← RegistrationNativePlatformServerPublication.program (outgoing operations) encode pending
      afterPublication self result) := by
  change (do let request ← liftRust pending.request
             let hash ← children.executeHash request
             AdapterPublicServerBuildBody.checked self (pending.resume hash) (signing self)).run = _
  unfold RegistrationNativePlatformServerPublication.program
  cases requested : pending.request with
  | fail error | div => simp only [RustT.run_bind, RustT.run_liftRust, pure_bind,
      RegistrationNativePlatformServerPublication.continueWith, afterPublication]
  | ok request =>
    simp only [RustT.run_bind, RustT.run_liftRust, pure_bind, Contract.hash (self := self) contract,
      RegistrationNativePlatformServerPublication.continueWith, outgoing, bind_map_left, bind_assoc]
    apply bind_congr
    intro digest
    simp only [AdapterPublicServerRecord.checked, fused, signing_source operations self contract ⟨.server, RegistrationInputs.hashBytes request⟩ digest]

noncomputable def afterRecord (operations : Primitives m) (self : Server) :
    RustM RegistrationServerRecordExecutor.Result → m (RustM Reply)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok (.None, self))
  | .ok (.Ok pending) => do
      let published ← RegistrationNativePlatformServerPublication.program (outgoing operations) encode pending
      afterPublication self published

/-- The actual SDK response suffix includes the complete first record, ML publication and actual container-install continuation. -/
theorem record (operations : Primitives m) (self : Server) (contract : Contract operations self)
    (kdf : AdapterPublicServerRecord.Kdf m) (kdfContract : AdapterPublicServerRecord.KdfContract kdf)
    (pending : registration.ServerInitialKdf) :
    (AdapterPublicServerBuildBody.record (m := m) self pending).run = (do
      let recorded ← RegistrationNativePlatformSourceRecord.fromInitialWithHash
        (AdapterPublicServerRecord.recordOperations kdf) AdapterPublicServerRecord.sealLeaf
        (fun transcript => (children.commitmentHash transcript).run) AdapterPublicServerRecord.writeLeaf pending
      afterRecord operations self recorded) := by
  rw [AdapterPublicServerRecord.record kdf kdfContract]
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error | div => rfl
  | ok answer => cases answer with
    | Err previous => rfl
    | Ok pending => exact sign operations self contract pending
end BeaconcryptCore.Refinement.AdapterPublicServerPublication

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublication.publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublication.publish

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublication.signing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublication.signing_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublication.sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublication.sign

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublication.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublication.record
