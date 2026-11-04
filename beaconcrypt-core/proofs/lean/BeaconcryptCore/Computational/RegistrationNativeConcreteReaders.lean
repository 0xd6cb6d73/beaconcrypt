-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeConcreteCodec
/-! The concrete source-backed registration decoders already perform the complete message-size preflight. The raw native read adapters therefore equal those literal decoders on every byte string, including oversized and malformed input, without an additional codec law premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeConcreteReaders

theorem init (bytes : Pqxdh.Bytes) :
    RegistrationNativeWire.readInit RegistrationNativeConcreteCodec.wire bytes = RegistrationNativeConcreteCodec.wire.decodeInit bytes := by
  unfold RegistrationNativeWire.readInit
  by_cases admitted : bytes.length ≤ CborSizing.maxMessageSize
  · simp only [admitted, ite_true]
  · simp only [admitted, ite_false]
    change none = @RegistrationNativeSourceWire.decodeInit RegistrationNativeConcreteCodec.decoderOperations bytes
    unfold RegistrationNativeSourceWire.decodeInit
    rw [dite_eq_right admitted]

theorem response (bytes : Pqxdh.Bytes) :
    RegistrationNativeWire.readResponse RegistrationNativeConcreteCodec.wire bytes = RegistrationNativeConcreteCodec.wire.decodeResponse bytes := by
  unfold RegistrationNativeWire.readResponse
  by_cases admitted : bytes.length ≤ CborSizing.maxMessageSize
  · simp only [admitted, ite_true]
  · simp only [admitted, ite_false]
    change none = @RegistrationNativeSourceWire.decodeResponse RegistrationNativeConcreteCodec.decoderOperations bytes
    unfold RegistrationNativeSourceWire.decodeResponse
    rw [dite_eq_right admitted]

end BeaconcryptCore.Computational.RegistrationNativeConcreteReaders

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteReaders.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteReaders.init

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteReaders.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteReaders.response
