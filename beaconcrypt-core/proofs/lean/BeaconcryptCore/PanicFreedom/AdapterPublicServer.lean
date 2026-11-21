-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary
import BeaconcryptCore.PanicFreedom.AdapterInitAuthentication
import BeaconcryptCore.PanicFreedom.AdapterPublicTrivial
import BeaconcryptCore.PanicFreedom.Registration
import BeaconcryptCore.PanicFreedom.PeerOwnership

/-! Native public Server admission and registration preserve ordinary rejections. External contracts concern individual leaves and the state returned by standard container operations. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
namespace BeaconcryptCore.PanicFreedom.AdapterPublicServer
open Refinement AdapterNormal beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [localOps : PublicWrapperPlatform.LocalOperations] [crypto : PublicWrapperPlatform.CryptoOperations]
variable [containers : PublicWrapperPlatform.ContainerOperations] [codec : PublicWrapperPlatform.Codecs]
variable [authentication : beaconcrypt.auth.Operations]

structure AuthenticationContracts : Prop where
  publicLeaves : AdapterPublicTrivial.Contracts
  init : AdapterInitAuthentication.Contracts
  decode : ∀ input, Normal (codec.decodeInit input)

omit [PublicWrapperPlatform.Allocator] containers in
theorem authenticate_registration_lookup_total (contracts : AuthenticationContracts)
    (self : server.Server) (bytes : Slice U8) :
    ∃ result, server.Server.authenticate_registration_lookup self bytes = ok result := by
  unfold server.Server.authenticate_registration_lookup
  simp only [beaconcrypt_parse.decode_init, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  repeat'
    first
      | with_reducible apply normal_bind_at
      | (solve | simp_all)
      | with_reducible exact contracts.decode _
      | with_reducible exact Registration.InitPacket_from_slices_total _ _ _ _
      | with_reducible exact AdapterPublicTrivial.server_authentication_pin_total contracts.publicLeaves _
      | with_reducible exact AdapterInitAuthentication.authenticate_init_total contracts.init _ _
      | exact normal_ok _
      | (intro value)
      | (split)
      | (split at *)

end BeaconcryptCore.PanicFreedom.AdapterPublicServer
