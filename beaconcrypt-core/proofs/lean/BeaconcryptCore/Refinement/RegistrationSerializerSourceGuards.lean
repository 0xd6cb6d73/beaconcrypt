-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationSerializerControllerExtraction.Funs
/-! Source controller and thin-wrapper dependency guards. Five explicit codec
operations remain parameters; these guards certify no additional logical
assumption, and do not assert a complete source/native codec law. -/
set_option warningAsError true
/-- info: 'beaconcrypt_parse.extraction_encode_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_parse.extraction_encode_init
/-- info: 'beaconcrypt_parse.extraction_encode_response' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_parse.extraction_encode_response
/-- info: 'beaconcrypt_parse.cbordetver.cbor_det_serialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_parse.cbordetver.cbor_det_serialize
/-- info: 'beaconcrypt_parse.cbordetveraux.cbor_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_parse.cbordetveraux.cbor_size
/-- info: 'beaconcrypt_parse.cbordetveraux.cbor_serialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beaconcrypt_parse.cbordetveraux.cbor_serialize
