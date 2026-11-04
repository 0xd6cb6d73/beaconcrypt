-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody
import BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The actual source replay lookup rejects consumed registrations before allocation and all agreement callbacks. Fresh lookup reaches the actual initial GenerateEphemeral phase before its literal reservation. The logical status follows from the private set view and authenticated identifier. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [containers : ContainerOperations (RustT m)] [crypto : CryptoOperations (RustT m)]

noncomputable def contains (stored : AdapterPublicWrapperStorage.ReplaySet) (identifier : Std.Array U8 64#usize) : RustT m Bool :=
  containers.setContains (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    (hashbrown.Equivalent.Blanket (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
      (core.borrow.Borrow.Blanket (Std.Array U8 64#usize))) stored identifier

omit containers crypto material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [Monad m] [LawfulMonad m] in
theorem begin_fresh (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) :
    ∃ pending, agreement.begin_server_agreement control .Fresh authenticated = .ok (.GenerateEphemeral pending) := by
  simp only [agreement.begin_server_agreement, pqxdh.validate_registration_status, bind_tc_ok,
    core.result.Result.is_err, registration.AuthenticatedInit.into_parts, agreement.AgreementState.new]
  exact ⟨_, rfl⟩

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] [LawfulMonad m] containers crypto in
private theorem lift_ok {A : Type} (value : A) : (liftRust (.ok value) : RustT m A) = pure value := rfl

theorem source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup) (rng : R)
    (identifier : pqxdh.RegistrationId) (requested : pending.request = .ok identifier)
    (present : Bool) (operation : contains (m := m) self.consumed_registrations identifier.bytes = pure present) :
    AdapterPublicServerAcceptBody.acceptLookup (m := m) generator self pending rng =
      (if present then pure (core.option.Option.None, self, rng) else do
        let phase ← liftRust (agreement.begin_server_agreement pending.control .Fresh pending.authenticated)
        AdapterPublicServerAcceptBody.reserved generator self rng phase) := by
  unfold AdapterPublicServerAcceptBody.acceptLookup
  rw [requested]
  simp only [lift_ok, pure_bind, pqxdh.RegistrationId.as_bytes]
  change (do let present ← contains (m := m) self.consumed_registrations identifier.bytes
             let phase ← liftRust (pending.resume present)
             match phase with
             | .Rejected _ => pure (core.option.Option.None, self, rng)
             | _ => AdapterPublicServerAcceptBody.reserved generator self rng phase) = _
  rw [operation, pure_bind]
  cases present with
  | true => simp only [ite_true, PeerOwnership.registration_lookup_consumed, lift_ok, pure_bind]
  | false =>
    obtain ⟨phase, began⟩ := begin_fresh pending.control pending.authenticated
    rw [PeerOwnership.registration_lookup_fresh, began]
    simp only [Bool.false_eq_true, ↓reduceIte, lift_ok, pure_bind]

theorem fresh {R E : Type} {ml : RegistrationNativeMldsa.Source} {KemSK : Type} {n : Nat}
    (generator : rand_core.TryCryptoRng R E) (view : AdapterPublicWrapperState.MaterialView ml KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential ml) (self : beaconcrypt_public_wrapper.server.Server)
    (native : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view views created credential self native)
    (pending : peer.RegistrationLookup) (rng : R) (identifier : pqxdh.RegistrationId)
    (requested : pending.request = .ok identifier)
    (absent : views.replay self.consumed_registrations identifier.bytes = false)
    (operation : contains (m := m) self.consumed_registrations identifier.bytes = pure (views.replay self.consumed_registrations identifier.bytes)) :
    native.consumed.contains (RegistrationReplaySchedule.identifier pending.authenticated) = false ∧
    AdapterPublicServerAcceptBody.acceptLookup (m := m) generator self pending rng = (do
      let phase ← liftRust (agreement.begin_server_agreement pending.control .Fresh pending.authenticated)
      AdapterPublicServerAcceptBody.reserved generator self rng phase) := by
  refine ⟨AdapterPublicServerReplayMembership.fresh view views created credential self native related pending identifier requested absent, ?_⟩
  rw [source generator self pending rng identifier requested _ operation, absent]
  rfl
end BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix.begin_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix.begin_fresh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReplayPrefix.fresh
