-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerReservationPost
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual source lookup returns a live Server and matching native session token on every normal outcome. Consumed rejection preserves the original object and all native private role coordinates; admitted calls retain actual reservation and agreement poststates. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerLookupPost
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt)
open AdapterPublicServerReservationNative (AllocationReply project)
open AdapterPublicServerAgreementPost (Returned)
open AdapterPublicServerLookupReceipt (identifier program)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK PlatformState : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

theorem source {R E : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.RegistrationLookup) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before after : Native) (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (membershipOperation : AdapterPublicServerReplayPrefix.contains
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations (identifier pending).bytes =
        pure (views.replay self.consumed_registrations (identifier pending).bytes))
    (allocated : StateT PlatformState ProbComp AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT PlatformState ProbComp) views {self with consumed_registrations := history})
    (receipt : Receipt R) (word : Word R) (previous next : PlatformState)
    (supported : (((receipt, .ok word), after), next) ∈ support
      (((program coins generator self pending rng).run before).run previous)) :
    ∃ handle nativeAfter, project view before ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
      Returned view views created credential word (.ok handle, nativeAfter) := by
  rw [AdapterPublicServerLookupReceipt.member coins generator self pending rng _ membershipOperation] at supported
  cases present : views.replay self.consumed_registrations (identifier pending).bytes with
  | true =>
    rw [present] at supported
    simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨none, before, rfl, related, trivial⟩
  | false =>
    rw [present] at supported
    exact AdapterPublicServerReservationPost.source coins generator self pending.control pending.authenticated rng
      view views created credential before after related allocated operation footprint insertion receipt word previous next supported

end BeaconcryptCore.Refinement.AdapterPublicServerLookupPost

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLookupPost.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLookupPost.source
