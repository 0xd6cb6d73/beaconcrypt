-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual extracted Server lookup and replay-consumption bodies factor through literal source callbacks. Source set reservation, insertion, returned RNG and complete object updates remain explicit. The agreement child is the literal checked source executor, pending its separate whole effectful material bridge. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [containers : ContainerOperations (RustT m)] [codec : Codecs (RustT m)]
variable [children : ChildOperations (RustT m)]

noncomputable def authenticate (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) :
    RustT m (core.option.Option peer.RegistrationLookup) := do
  let parsed ← codec.decodeInit input
  match parsed with
  | .None => pure .None
  | .Some value =>
    let packet ← liftRust (registration.InitPacket.from_slices value.identity_key value.pre_key value.one_time_key
      value.pq_key value.mldsa_public_key value.signature)
    match packet with
    | .None => pure .None
    | .Some packet =>
      let pin ← beaconcrypt_public_request.server.Server.authentication_pin self
      match pin with
      | .None => pure .None
      | .Some pin =>
        let authenticated ← children.authenticateInit pin packet
        match authenticated with
        | .none => pure .None
        | .some authenticated =>
          let lookup ← liftRust (peer.begin_registration_lookup self.control authenticated)
          pure (.Some lookup)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers in
theorem authenticate_source (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) :
    beaconcrypt_public_request.server.Server.authenticate_registration_lookup (m := RustT m) self input =
      authenticate self input := by
  simp only [beaconcrypt_public_request.server.Server.authenticate_registration_lookup,
    authenticate, call_apply, call_result]
  apply bind_congr
  intro parsed
  cases parsed with
  | none => simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | some value =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind]
    apply bind_congr
    intro packet
    cases packet with
    | none => simp only [  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
    | some packet =>
      simp only [
         lift_ok, pure_bind]
      apply bind_congr
      intro pin
      cases pin with
      | none => simp only [  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
      | some pin =>
        simp only [
           lift_ok, pure_bind]
        apply bind_congr
        intro authenticated
        cases authenticated with
        | none => simp only [  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
        | some authenticated =>
          simp only [
             lift_ok, pure_bind]

noncomputable def setReserve (stored : AdapterPublicWrapperStorage.ReplaySet) :
    RustT m (core.result.Result Unit platform.ReserveError × AdapterPublicWrapperStorage.ReplaySet) :=
  containers.setReserve (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator stored 1#usize

noncomputable def setInsert (stored : AdapterPublicWrapperStorage.ReplaySet) (identifier : Array U8 64#usize) :
    RustT m (Bool × AdapterPublicWrapperStorage.ReplaySet) :=
  containers.setInsert (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator stored identifier

noncomputable def record {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (effect : agreement.AgreementEffect) :
    RustT m (core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R) := do
  match effect with
  | .ServerComplete completed =>
    let pending ← liftRust (peer.begin_registration_insert completed)
    let identifier ← liftRust pending.request
    let bytes ← liftRust identifier.as_bytes
    let again ← liftRust identifier.as_bytes
    let (inserted, history) ← setInsert self.consumed_registrations again
    let registered ← liftRust (pending.resume inserted)
    pure ((fun registration => (⟨registration, bytes⟩ : beaconcrypt_public_wrapper.server.RegistrationOutput)) <$> registered,
      { self with consumed_registrations := history }, rng)
  | _ => pure (.None, self, rng)

noncomputable def reserved {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.server.Server) (rng : R) (effect : agreement.AgreementEffect) :
    RustT m (core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R) := do
  let (allocation, history) ← setReserve self.consumed_registrations
  let current := { self with consumed_registrations := history }
  match allocation with
  | .Err _ => pure (.None, current, rng)
  | .Ok _ =>
    let secret ← beaconcrypt_public_request.server.Server.identity_sk current
    let (finished, rng) ← beaconcrypt_public_request.pqxdh.execute_agreement rngType effect
      ⟨secret, .None, .None, .None⟩ rng
    record current rng finished

noncomputable def acceptLookup {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.server.Server) (lookup : peer.RegistrationLookup) (rng : R) :
    RustT m (core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R) := do
  let identifier ← liftRust lookup.request
  let bytes ← liftRust identifier.as_bytes
  let consumed ← containers.setContains (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    (hashbrown.Equivalent.Blanket (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
      (core.borrow.Borrow.Blanket (Array U8 64#usize))) self.consumed_registrations bytes
  let effect ← liftRust (lookup.resume consumed)
  match effect with
  | .Rejected _ => pure (.None, self, rng)
  | _ => reserved rngType self rng effect

omit localOps codec children in
theorem accept_lookup_source {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.server.Server) (lookup : peer.RegistrationLookup) (rng : R) :
    beaconcrypt_public_request.server.Server.get_shared_secret_from_lookup_with_rng (m := RustT m) rngType self lookup rng =
      acceptLookup rngType self lookup rng := by
  simp only [beaconcrypt_public_request.server.Server.get_shared_secret_from_lookup_with_rng,
    acceptLookup, call_apply, call_result]
  apply bind_congr
  intro identifier
  apply bind_congr
  intro bytes
  apply bind_congr
  intro consumed
  apply bind_congr
  intro effect
  cases effect <;> simp only [reserved, setReserve]
  all_goals try rfl
  all_goals apply bind_congr
  all_goals rintro ⟨allocation, history⟩
  all_goals cases allocation with
  | Err prior => simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | Ok unitValue =>
    cases unitValue
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind]
    apply bind_congr
    intro secret
    apply bind_congr
    rintro ⟨finished, currentRng⟩
    cases finished <;> simp only [record]
    all_goals apply bind_congr
    all_goals intro pending
    all_goals apply bind_congr
    all_goals intro identifier
    all_goals apply bind_congr
    all_goals intro bytes
    all_goals apply bind_congr
    all_goals intro again
    all_goals simp only [setInsert]
    all_goals apply bind_congr
    all_goals rintro ⟨inserted, history⟩
    all_goals apply bind_congr
    all_goals intro accepted
    all_goals cases accepted <;> simp only [  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind] <;> rfl
end BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody.authenticate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody.authenticate_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody.accept_lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody.accept_lookup_source
