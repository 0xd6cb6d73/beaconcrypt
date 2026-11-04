-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicServer
import BeaconcryptCore.PanicFreedom.AdapterPublicAgreementSafety
import BeaconcryptCore.AdapterPublicServerEntryExtraction.Funs

/-! Registration acceptance retains the complete peer map on every branch, including replay, reservation refusal and failed cryptographic replies. The public delegator composes authentication and acceptance without replacing either native child. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
namespace BeaconcryptCore.PanicFreedom.AdapterPublicServerAccept
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [localOps : PublicWrapperPlatform.LocalOperations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [containers : PublicWrapperPlatform.ContainerOperations]
variable [authentication : beaconcrypt.auth.Operations]

abbrev ReplaySet := hashbrown.set.HashSet (Array U8 64#usize) collections.KeyedHasher hashbrown.alloc.inner.Global
abbrev replayContains (set : ReplaySet) (identifier : Array U8 64#usize) :=
  hashbrown.set.HashSet.contains (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    (hashbrown.Equivalent.Blanket (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
      (core.borrow.Borrow.Blanket (Array U8 64#usize))) set identifier
abbrev replayReserve (set : ReplaySet) (capacity : Usize) :=
  hashbrown.set.HashSet.try_reserve (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator set capacity
abbrev replayInsert (set : ReplaySet) (identifier : Array U8 64#usize) :=
  hashbrown.set.HashSet.insert (core.Array.Insts.CoreCmpEq 64#usize core.U8.Insts.CoreCmpEq)
    (core.Array.Insts.CoreHashHash 64#usize core.U8.Insts.CoreHashHash)
    collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
    hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator set identifier

structure ReplayContracts : Prop where
  contains : ∀ set identifier, Normal (replayContains set identifier)
  reserve : ∀ set capacity, Normal (replayReserve set capacity)
  insert : ∀ set identifier, Normal (replayInsert set identifier)

omit authentication in
theorem get_shared_secret_from_lookup_with_rng_retains
    (contracts : AdapterPublicRegistrationLoops.AgreementContracts) (replay : ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator) (self : server.Server)
    (lookup : peer.RegistrationLookup) (rng : R) :
    Ensures (server.Server.get_shared_secret_from_lookup_with_rng generator self lookup rng)
      (fun result => result.2.1.known_ids = self.known_ids) := by
  unfold server.Server.get_shared_secret_from_lookup_with_rng
  simp only [core.result.Result.ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  repeat'
    try dsimp! only
    first
      | with_reducible apply ensures_bind_at
      | (solve | simp_all)
      | with_reducible exact replay.contains _ _
      | with_reducible exact replay.reserve _ _
      | with_reducible exact replay.insert _ _
      | with_reducible exact PeerOwnership.RegistrationLookup_request_total _
      | with_reducible exact PeerOwnership.RegistrationLookup_resume_total _ _
      | with_reducible exact PeerOwnership.begin_registration_insert_total _
      | with_reducible exact PeerOwnership.RegistrationInsert_request_total _
      | with_reducible exact PeerOwnership.RegistrationInsert_resume_total _ _
      | with_reducible exact AdapterPublicTrivial.server_identity_sk_total _
      | with_reducible exact AdapterPublicAgreementSafety.execute_agreement_total contracts _ random _ _ _
      | exact normal_ok _
      | (rintro (⟨left, right⟩ : _ × _))
      | (intro value)
      | (split)
      | (split at *)

omit authentication in
theorem get_shared_secret_from_lookup_with_rng_total
    (contracts : AdapterPublicRegistrationLoops.AgreementContracts) (replay : ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator) (self : server.Server)
    (lookup : peer.RegistrationLookup) (rng : R) :
    ∃ result, server.Server.get_shared_secret_from_lookup_with_rng generator self lookup rng = ok result :=
  ensures_normal (get_shared_secret_from_lookup_with_rng_retains contracts replay generator random self lookup rng)

variable [lookupOperations : AdapterPublicOrdinaryPlatform.LookupOperations]

omit authentication in
theorem get_shared_secret_from_lookup_with_rng_preserves
    (contracts : AdapterPublicRegistrationLoops.AgreementContracts) (replay : ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator) (self : server.Server)
    (lookup : peer.RegistrationLookup) (rng : R) (valid : AdapterPublicOrdinary.ValidServer self) :
    Ensures (server.Server.get_shared_secret_from_lookup_with_rng generator self lookup rng)
      (fun result => AdapterPublicOrdinary.ValidServer result.2.1) := by
  obtain ⟨result, returned, retained⟩ := get_shared_secret_from_lookup_with_rng_retains contracts replay generator random self lookup rng
  refine ⟨result, returned, ?_⟩
  change AdapterPublicOrdinary.ValidMap result.2.1.known_ids
  rw [retained]
  exact valid

variable [PublicWrapperPlatform.Codecs]

omit lookupOperations in
theorem get_shared_secret_with_rng_total
    (authenticationContracts : AdapterPublicServer.AuthenticationContracts)
    (contracts : AdapterPublicRegistrationLoops.AgreementContracts) (replay : ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator) (self : server.Server)
    (bytes : Slice U8) (rng : R) :
    ∃ result, beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng generator self bytes rng = ok result := by
  obtain ⟨selected, authenticated⟩ := AdapterPublicServer.authenticate_registration_lookup_total authenticationContracts self bytes
  unfold beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng
  simp only [beaconcrypt_public_server_entry.server.Server.authenticate_registration_lookup,
    beaconcrypt_public_server_entry.server.Server.get_shared_secret_from_lookup_with_rng, authenticated, bind_tc_ok]
  cases selected with
  | none => exact ⟨(none, self, rng), rfl⟩
  | some lookup =>
    simpa only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok] using
      get_shared_secret_from_lookup_with_rng_total contracts replay generator random self lookup rng

theorem get_shared_secret_with_rng_preserves
    (authenticationContracts : AdapterPublicServer.AuthenticationContracts)
    (contracts : AdapterPublicRegistrationLoops.AgreementContracts) (replay : ReplayContracts)
    {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (random : AdapterPublicRegistrationLoops.AgreementRngContracts generator) (self : server.Server)
    (bytes : Slice U8) (rng : R) (valid : AdapterPublicOrdinary.ValidServer self) :
    Ensures (beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng generator self bytes rng)
      (fun result => AdapterPublicOrdinary.ValidServer result.2.1) := by
  obtain ⟨selected, authenticated⟩ := AdapterPublicServer.authenticate_registration_lookup_total authenticationContracts self bytes
  unfold beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng
  simp only [beaconcrypt_public_server_entry.server.Server.authenticate_registration_lookup,
    beaconcrypt_public_server_entry.server.Server.get_shared_secret_from_lookup_with_rng, authenticated, bind_tc_ok]
  cases selected with
  | none => exact ⟨(none, self, rng), rfl, valid⟩
  | some lookup =>
    simpa only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok] using
      get_shared_secret_from_lookup_with_rng_preserves contracts replay generator random self lookup rng valid

end BeaconcryptCore.PanicFreedom.AdapterPublicServerAccept
