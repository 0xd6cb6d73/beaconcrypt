-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTransport
import BeaconcryptCore.Computational.RawCtxNativeFramePrelude

/-! The validated native transport-frame representation and bounded decoder are shared by the production boundary and the actual native byte adapter. This module contains no experiment or security assumption. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborProductionBoundary

/-- The native decoder has already validated the complete deterministic-CBOR array and borrowed its byte string. -/
structure NativeFrame where
  sequence : Std.U64
  sender : Std.U64
  payload : Slice Std.U8

def nativeReader (parse : Pqxdh.Bytes → Option NativeFrame) :
    RawCtxNativeFramePrelude.Reader NativeFrame NativeFrame where
  readMessage raw := if raw.length ≤ CborSizing.maxMessageSize then
    (fun frame => (frame, Slice.new Std.U8)) <$> parse raw else none
  root := some
  keyId := NativeFrame.sender
  sequence := NativeFrame.sequence
  payload frame := some frame.payload

def decoded (frame : NativeFrame) : RawCtxReceive.DecodedFrame :=
  ⟨frame.sequence, frame.sender, RawCtxNativeFramePrelude.sliceBytes frame.payload⟩

def frameDecoder (parse : Pqxdh.Bytes → Option NativeFrame) : RawCtxReceive.FrameDecoder :=
  CborTransport.boundedDecoder (fun raw => decoded <$> parse raw)

end BeaconcryptCore.Computational.CborProductionBoundary
