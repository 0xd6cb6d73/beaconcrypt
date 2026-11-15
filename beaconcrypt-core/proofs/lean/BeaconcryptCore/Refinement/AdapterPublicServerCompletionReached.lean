-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildPrefix
import BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall
import BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial
import BeaconcryptCore.Refinement.Transport
import BeaconcryptCore.PanicFreedom.Transport
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
/-! Every reached source first-record/publication receipt retains its actual returned Server material at the same canonical native administrative poststate, including publication, allocation, signing and installation rejection. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionReached
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open AdapterPublicServerBuildBody (Server Reply)
variable {n : Nat} {KemSK Platform E I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => StateT Native Base
local notation "SourceM" => StateT Cut Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

open AdapterPublicServerBuildPrefix (completion)

theorem source
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before after : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (initial : registration.ServerInitialKdf) (previous : initial.candidate.previous_state = self.control)
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (standard : ∀ publication pending publicKey,
      peer.begin_peer_insert self.control publication = .ok (.Ok pending) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views self pending publicKey)
    (published : AdapterPublicServerBuildTrace.Publication) (word : RustM Reply)
    (external next : Platform)
    (supported : (((published, word), after), next) ∈ support
      (((completion coins setup codec keyView failure allocation helper erased sign writer fallback self initial).run before).run external)) :
    AdapterPublicServerPublicationInstall.Returned view views created credential word
      (AdapterPublicServerCompletionLifetime.project self.control ((published, word), after)).2.server := by
  unfold completion AdapterPublicServerBuildTrace.complete AdapterPublicServerCompletionSource.receipt at supported
  simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pub, current⟩, between⟩, called, continued⟩ := supported
  obtain ⟨⟨⟨output, final⟩, finished⟩, installed, returned⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff] at returned
  have pubEq := congrArg (fun result => result.1.1.1) returned
  have wordEq := congrArg (fun result => result.1.1.2) returned
  have stateEq := congrArg (fun result => result.1.2) returned
  have externalEq := congrArg Prod.snd returned
  cases pubEq
  cases wordEq
  cases stateEq
  cases externalEq
  obtain ⟨retained, currentMaterial⟩ := AdapterPublicServerCompletionTrace.source_receipt coins setup codec keyView failure allocation helper erased sign writer fallback initial
    view views created credential self before current related external between published called
  obtain ⟨actualWord, actual, _observed, materialRetained⟩ := AdapterPublicServerTailMaterial.source
    (AdapterPublicServerCompletionLifetime.liftedCoins coins) view views created credential self current.1.server currentMaterial
    initial previous parsed published retained
    (fun publication pending publicKey _ began reparsed => standard publication pending publicKey began reparsed) current between
  rw [actual] at installed
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at installed
  have wordEq := congrArg (fun result => result.1.1) installed
  have stateEq := congrArg (fun result => result.1.2) installed
  cases wordEq
  cases stateEq
  exact materialRetained

end BeaconcryptCore.Refinement.AdapterPublicServerCompletionReached

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionReached.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionReached.source
