-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPrimitiveExtraction.Types
import BeaconcryptCore.AdapterWireExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.RegistrationWriterPrimitive
/-! Only the two schema serializers are parameters here. The actual source encode_record helper and std mutable serializer ABI are reused. Concrete schema byte semantics are discharged separately. -/
class Operations where
  encodeInit : beaconcrypt_parse.transport.initkex → Slice U8 → RustM (Usize × Slice U8)
  encodeResponse : beaconcrypt_parse.transport.kexresponse → Slice U8 → RustM (Usize × Slice U8)
end BeaconcryptCore.Refinement.RegistrationWriterPrimitive
