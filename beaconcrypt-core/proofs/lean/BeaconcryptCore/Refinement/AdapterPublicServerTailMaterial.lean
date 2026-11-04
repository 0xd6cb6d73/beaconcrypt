-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerTailCanonical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The original source installer retains its returned private Server material at the canonical native administrative result. Both current states are explicit values from the same source run; no native result is chosen from an unrelated supported execution. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerTailMaterial
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
variable {n : Nat} {S Platform A : Type}

private theorem pure_equal (before : S) (external : Platform) (left right : A)
    (equal : (pure left : StateT S (StateT Platform ProbComp) A) = pure right) : left = right := by
  have represented := congrArg (fun work => (work.run before).run external) equal
  change (pure ((left, before), external) : ProbComp _) = pure ((right, before), external) at represented
  have selected : ((left, before), external) ∈ support (pure ((left, before), external) : ProbComp _) := by
    simp only [support_pure, Set.mem_singleton_iff]
  rw [represented] at selected
  simp only [support_pure, Set.mem_singleton_iff] at selected
  exact congrArg (fun result => result.1.1) selected

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT S (StateT Platform ProbComp)))]
variable {mlSource : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem source (coins : QueryImpl unifSpec (StateT S (StateT Platform ProbComp)))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self before)
    (initial : registration.ServerInitialKdf)
    (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (published : RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)))
    (retained : RegistrationServerSourceCompletionReceipt.Post initial published)
    (standard : ∀ publication pending publicKey,
      published = .ok (.Ok publication) → peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := StateT S (StateT Platform ProbComp)) views self pending publicKey)
    (current : S) (external : Platform) :
    ∃ word,
      AdapterPublicServerPublication.afterPublication (m := StateT S (StateT Platform ProbComp)) self published = pure word ∧
      AdapterPublicServerPublicationInstall.project word = (AdapterPublicServerTailCanonical.result self.control published before).1 ∧
      AdapterPublicServerPublicationInstall.Returned view views created credential word
        (AdapterPublicServerTailCanonical.result self.control published before).2 := by
  obtain ⟨word, after, actual, nativeComputed, materialRetained⟩ := AdapterPublicServerPublicationInstall.publication coins
    view views created credential self before related initial previous parsed published retained standard
  have compared := pure_equal current external _ _ (nativeComputed.symm.trans
    (AdapterPublicServerTailCanonical.native_run coins self.control published before))
  refine ⟨word, actual, congrArg Prod.fst compared, ?_⟩
  have afterEq := congrArg Prod.snd compared
  rw [← afterEq]
  exact materialRetained
end BeaconcryptCore.Refinement.AdapterPublicServerTailMaterial
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerTailMaterial.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerTailMaterial.source
