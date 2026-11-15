-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicOrdinaryExtraction.Types
import BeaconcryptCore.AdapterRecordSendExtraction.Funs
import BeaconcryptCore.AdapterRecordExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform
open PublicWrapperPlatform
def assertBool (value : Bool) : RustM Unit := massert value
def associatedData (binding : beaconcrypt_core.session.SessionBinding) : RustM (Array U8 151#usize) :=
  .ok binding.associated_data
variable [platform : Platform] [Allocator]
/-- Individual standard-map lookup and mutable entry lens, including their Rust outcomes. -/
class LookupOperations where
  get {K V S A Q H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → core.hash.Hash Q → hashbrown.Equivalent Q K → hashbrown.map.HashMap K V S A → Q → RustM (core.option.Option V)
  getMut {K V S A Q H : Type} : core.cmp.Eq K → core.hash.Hash K → core.hash.BuildHasher S H → hashbrown.alloc.inner.Allocator A → core.hash.Hash Q → hashbrown.Equivalent Q K → hashbrown.map.HashMap K V S A → Q → RustM (core.option.Option V × (core.option.Option V → hashbrown.map.HashMap K V S A))
end BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform
namespace hashbrown.map.HashMap
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]
variable [ops : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]
abbrev get := @BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations.get _ _ ops
abbrev get_mut := @BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations.getMut _ _ ops
end hashbrown.map.HashMap
namespace beaconcrypt_parse
abbrev decode_frame := frame.decode
end beaconcrypt_parse
namespace beaconcrypt_public_ordinary.ratchet
variable [beaconcrypt_record_send.ratchet.Operations]
variable [beaconcrypt.ratchet.Operations]
abbrev execute_record_send := beaconcrypt_record_send.ratchet.execute_record_send
abbrev execute_record_receive := beaconcrypt.ratchet.execute_record_receive
end beaconcrypt_public_ordinary.ratchet
