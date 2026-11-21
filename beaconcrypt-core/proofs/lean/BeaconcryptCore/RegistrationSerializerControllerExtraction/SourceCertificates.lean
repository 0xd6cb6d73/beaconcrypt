-- SPDX-License-Identifier: 0BSD
-- Generated exact helper-boundary instances; source correspondence manifest is checked separately.
import BeaconcryptCore.RegistrationSerializerControllerExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates
variable [BeaconcryptCore.Refinement.RegistrationSerializerPrimitive.Operations]

theorem extraction_serialize_initkex_size_0 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_initkex_size_0 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_initkex_size_0 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_initkex_size_1 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_initkex_size_1 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_initkex_size_1 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_initkex_size_2 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_initkex_size_2 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_initkex_size_2 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_initkex_size_3 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_initkex_size_3 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_initkex_size_3 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_kexresponse_size_0 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_0 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_0 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_kexresponse_size_1 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_1 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_1 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_kexresponse_size_2 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_2 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_2 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

theorem extraction_serialize_kexresponse_size_3 (payload output : Slice U8) (low high : Bool) :
    ((fun captured state lo hi => beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_3 captured state lo hi) payload output low high) =
      beaconcrypt_parse.transport.extraction_serialize_kexresponse_size_3 payload output low high :=
  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _

end BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_0

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_1

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_2

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_initkex_size_3

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_0

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_1

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_2

/-- info: 'BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates.extraction_serialize_kexresponse_size_3
