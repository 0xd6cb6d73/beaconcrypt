-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual source reservation retains the live mutable Server and its exact one-use token/session relation on every normal return. Failed allocation keeps its actual returned set and external state; successful allocation passes those objects into the same captured SDK agreement. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerReservationPost
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt program)
open AdapterPublicServerReservationNative (AllocationReply project)
open AdapterPublicServerAgreementPost (Returned)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK PlatformState : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

omit original in
private theorem allocation_joint (self : beaconcrypt_public_wrapper.server.Server)
    (allocated : StateT PlatformState ProbComp AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated) (before : Native) (previous : PlatformState) :
    (((AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations).run).run before).run previous =
      (fun result => ((RustM.ok result.1, before), result.2)) <$> allocated.run previous := by
  rw [operation]
  simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]

theorem source {R E : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E) (self : beaconcrypt_public_wrapper.server.Server)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before after : Native) (related : AdapterPublicWrapperState.Server view views created credential self before.server)
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
      (((program coins generator self control authenticated rng).run before).run previous)) :
    ∃ handle nativeAfter, project view before ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
      Returned view views created credential word (.ok handle, nativeAfter) := by
  simp only [program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨allocatedReply, middle⟩, between⟩, called, continued⟩ := supported
  rw [allocation_joint self allocated operation before previous, support_map] at called
  obtain ⟨⟨reply, allocatedExternal⟩, allocatedSupport, returned⟩ := called
  have stateEq := congrArg (fun value => value.1.2) returned
  have replyEq := congrArg (fun value => value.1.1) returned
  have externalEq := congrArg Prod.snd returned
  change before = middle at stateEq
  change .ok reply = allocatedReply at replyEq
  cases replyEq
  cases externalEq
  subst middle
  have currentMaterial := AdapterPublicWrapperState.replay_reserved view views created credential self before.server
    related reply (footprint previous reply between allocatedSupport)
  rcases reply with ⟨allocation, history⟩
  cases allocation with
  | Err error =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    cases continued
    exact ⟨none, before, rfl, currentMaterial, trivial⟩
  | Ok allocatedUnit =>
    simp only [StateT.run_map, support_map] at continued
    obtain ⟨⟨⟨⟨captured, result⟩, currentNative⟩, currentExternal⟩, called, returned⟩ := continued
    have stateEq := congrArg (fun value => value.1.2) returned
    have receiptEq := congrArg (fun value => value.1.1.1) returned
    have wordEq := congrArg (fun value => value.1.1.2) returned
    have externalEq := congrArg Prod.snd returned
    change currentNative = after at stateEq
    change some captured = receipt at receiptEq
    change result = .ok word at wordEq
    cases receiptEq
    cases externalEq
    subst after
    subst result
    obtain ⟨handle, nativeAfter, projected, post⟩ := AdapterPublicServerAgreementPost.program coins generator
      (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
      {self with consumed_registrations := history} (RegistrationAgreementExecutor.server control .Fresh authenticated) rng
      view views created credential before currentNative currentMaterial (insertion history) captured word between next called
    exact ⟨handle, nativeAfter, projected, post⟩

end BeaconcryptCore.Refinement.AdapterPublicServerReservationPost

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReservationPost.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReservationPost.source
