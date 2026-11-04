-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerSourceLens
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual source lookup, stateful reservation, agreement and returned one-use token refine the literal corrected native after-authentication SDK branch. Its Fresh condition is derived from the exact authenticated ID and standard set observation. Consumed rejection keeps the original full Native auxiliary state and performs no allocation or cryptographic call. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerLookupNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerLookupReceipt (identifier requested program)
open AdapterPublicServerReservationNative (project AllocationReply)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]

theorem coupled {PlatformState R E I : Type} {base : OracleSpec I}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (generator : rand_core.TryCryptoRng R E)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R)
    (packet : registration.InitPacket) (before : RegistrationNativeExperiment.State n KemSK mlSource)
    [ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (control : pending.control = before.server.control)
    (membershipOperation : AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      self.consumed_registrations (identifier pending).bytes =
        pure (views.replay self.consumed_registrations (identifier pending).bytes))
    (allocated : StateT PlatformState ProbComp AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT PlatformState ProbComp) views {self with consumed_registrations := history}) :
    project view before <$> ((program coins generator self pending rng).run before) =
      RustM.ok <$> (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks
          (StateT.lift (AdapterPublicServerSourceLens.admitted <$> allocated)) model.representation created packet pending.authenticated)).run before := by
  have membership := AdapterPublicServerReplayMembership.lookup view views created credential self before.server
    related pending (identifier pending) (requested pending)
  rw [AdapterPublicServerLookupReceipt.member coins generator self pending rng _ membershipOperation, membership]
  cases present : before.server.consumed.contains (RegistrationReplaySchedule.identifier pending.authenticated) with
  | true =>
    rw [ite_eq_left rfl, AdapterPublicServerSourceLens.server_run,
      RegistrationNativePlatformServerSdk.afterAuthentication_run, present]
    simp only [StateT.run_pure, map_pure, project, ↓reduceIte]
  | false =>
    rw [ite_eq_right Bool.false_ne_true, control,
      AdapterPublicServerSourceLens.after_authentication coins setup checks model.representation created packet pending.authenticated allocated before present]
    exact AdapterPublicServerReservationNative.coupled coins generator setup checks view views model entropy
      created credential self rng packet pending.authenticated before related allocated allocationOperation footprint insertion present

end BeaconcryptCore.Refinement.AdapterPublicServerLookupNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerLookupNative.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerLookupNative.coupled
