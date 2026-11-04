-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicServerEntryExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace beaconcrypt_public_server_entry
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.ContainerOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Codecs]
variable [beaconcrypt.ratchet.Operations]
variable [beaconcrypt.auth.Operations]
variable [BeaconcryptCore.Refinement.RegistrationWriterPrimitive.Operations]
variable [BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]
def server.Server.get_shared_secret_from_lookup_with_rng
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (self : server.Server)
    (lookup : beaconcrypt_core.peer.RegistrationLookup) (rng : R) :
    RustM (core.option.Option server.RegistrationOutput × server.Server × R) :=
  beaconcrypt_public_wrapper.server.Server.get_shared_secret_from_lookup_with_rng generator self lookup rng

def server.Server.authenticate_registration_lookup (self : server.Server) (input : Slice U8) :
    RustM (core.option.Option beaconcrypt_core.peer.RegistrationLookup) :=
  beaconcrypt_public_wrapper.server.Server.authenticate_registration_lookup self input
end beaconcrypt_public_server_entry
