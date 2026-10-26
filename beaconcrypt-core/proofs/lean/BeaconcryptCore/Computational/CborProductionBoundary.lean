-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRegistrationCodec
import BeaconcryptCore.Computational.CborCommandFilter
import BeaconcryptCore.Computational.PqxdhBoundaryDeploymentStep

/-!
Current CBOR boundary: complete validated native frames supply both routing and opening; registration receive uses a virtual sequence-one frame, while registration build returns raw protected bytes without an inner frame-writer failure. Exact complete-message send/build limits run before primitive callbacks. A rejected build consumes its pending token, while a rejected send preserves the entry state. Native parsing and outer response allocation remain explicit boundaries. The normalized-prefixed definitions retain the fixed-frame experiment used by the separate representation bridge; they are not the current raw-registration builder.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborProductionBoundary
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

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

/-- Bound native registration parsing and use the complete transport frame decoder. -/
def wireCodec (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option NativeFrame) :
    Codec Reader Response :=
  { wire with
    read1 := fun raw => if raw.length ≤ CborSizing.maxMessageSize then wire.read1 raw else none
    read2 := fun raw => if raw.length ≤ CborSizing.maxMessageSize then wire.read2 raw else none
    frameRead := frameDecoder parse }

def codec (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option NativeFrame)
    (sender : Std.U64) : Codec Reader Response :=
  CborRegistrationCodec.normalize (wireCodec wire parse) sender

/-- Only registration build bypasses frame serialization; native response serialization remains optional. Receive uses its implicit first-frame normalization, and established record sends keep the native frame writer. -/
def commandCodec (wire : Codec Reader Response) (parse : Pqxdh.Bytes → Option NativeFrame)
    (sender : Std.U64) (query : Spec.Domain) : Codec Reader Response :=
  match query with
  | .inr (.build _ _) => CborRegistrationCodec.raw (wireCodec wire parse)
  | _ => codec wire parse sender

theorem registration_writer (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (sender : Std.U64) (session : Nat)
    (payload : Option Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) :
    (commandCodec wire parse sender (.inr (.build session payload))).frameWrite frame = some frame.payload ∧
      (commandCodec wire parse sender (.inr (.build session payload))).write2 = wire.write2 := by
  exact ⟨rfl, rfl⟩

def nextFits (plaintext sequence sender : Nat) : Bool :=
  decide (CborSizing.frameLen (sequence + 1) sender (plaintext + 80) ≤ CborSizing.maxMessageSize)

/-- Lookup/gating failures stay in the original handler; only current transport-size admission is added here. -/
def allowed (query : Spec.Domain) (state : PqxdhDeploymentNative.State KemSK) : Bool :=
  match query with
  | .inr (.build _ payload) => decide (CborSizing.responseLen
      ((payload.getD [0xff]).length + 88) (state.native.shared.2.server.control.last_key_id.val + 1) ≤
        CborSizing.maxMessageSize)
  | .inr (.serverSend keyId plaintext) =>
      match state.native.shared.2.server.server.peers keyId with
      | none => true
      | some peer => nextFits plaintext.length peer.kernel.refined.control.send_sequence.val
          state.native.shared.2.server.identityKeyId.val
  | .inr (.beaconSend index plaintext) =>
      match state.native.owners[index]? with
      | none => true
      | some owner => match owner.beacon.phase with
        | .established _ _ kernel => nextFits plaintext.length kernel.refined.control.send_sequence.val
            owner.beacon.identityKeyId.val
        | _ => true
  | _ => true

def consumePending (session : Nat) (state : PqxdhDeploymentNative.State KemSK) :
    PqxdhDeploymentNative.State KemSK :=
  { state with native := { state.native with shared := (state.native.shared.1,
    { state.native.shared.2 with pending := Function.update state.native.shared.2.pending session none }) } }

/-- The unused oracle cases merely make this total; `allowed` always admits them. -/
def reject : (query : Spec.Domain) → PqxdhDeploymentNative.State KemSK →
    Spec.Range query × PqxdhDeploymentNative.State KemSK
  | .inl coin, state => ((⟨0, Nat.zero_lt_succ coin⟩ : Fin (coin + 1)), state)
  | .inr (.create _ _), state => (none, state)
  | .inr (.bundle _), state => (none, state)
  | .inr (.accept _), state => (none, state)
  | .inr (.build session _), state => (none, consumePending session state)
  | .inr (.finish _ _), state => (none, state)
  | .inr (.hmac _ _), state => (List.Vector.replicate 64 (0 : UInt8), state)
  | .inr (.hash _), state => (List.Vector.replicate 64 (0 : UInt8), state)
  | .inr (.serverSend _ _), state => (none, state)
  | .inr (.serverRaw _), state => (.None, state)
  | .inr (.beaconSend _ _), state => (none, state)
  | .inr (.beaconRaw _ _), state => (.None, state)

/-- Each Beacon supplies its own pinned numeric Server ID, including mismatching pins chosen at creation. -/
def normalizationSender (query : Spec.Domain) (state : PqxdhDeploymentNative.State KemSK) : Std.U64 :=
  match query with
  | .inr (.finish index _) =>
      match state.native.owners[index]? with
      | some owner => match owner.beacon.phase with
        | .initSent control _ _ _ => control.expected_server_binding.identity_key_id
        | _ => state.native.shared.2.server.identityKeyId
      | none => state.native.shared.2.server.identityKeyId
  | _ => state.native.shared.2.server.identityKeyId

noncomputable def normalizedBaseHandler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  fun query => CborCommandFilter.atState fun state => PqxdhDeploymentNative.handler setup
    (PqxdhBoundaryRecordPrelude.withReader (codec wire parse (normalizationSender query state))
      (nativeReader parse)) checks (RawCtxFrameDecoding.sender (nativeReader parse).model) seed query

noncomputable def normalizedBaseSource (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    PqxdhBoundaryProgram.Step Spec (PqxdhDeploymentNative.State KemSK) :=
  fun query state => PqxdhBoundaryDeploymentStep.sourceStep setup
    (codec wire parse (normalizationSender query state)) (nativeReader parse) erased checks seed query state

noncomputable def normalizedHandler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  CborCommandFilter.handler allowed reject (normalizedBaseHandler setup wire parse checks seed)

noncomputable def normalizedSource (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    PqxdhBoundaryProgram.Step Spec (PqxdhDeploymentNative.State KemSK) :=
  CborCommandFilter.source allowed reject (normalizedBaseSource setup wire parse erased checks seed)

noncomputable def baseHandler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  fun query => CborCommandFilter.atState fun state => PqxdhDeploymentNative.handler setup
    (PqxdhBoundaryRecordPrelude.withReader (commandCodec wire parse (normalizationSender query state) query)
      (nativeReader parse)) checks (RawCtxFrameDecoding.sender (nativeReader parse).model) seed query

noncomputable def baseSource (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    PqxdhBoundaryProgram.Step Spec (PqxdhDeploymentNative.State KemSK) :=
  fun query state => PqxdhBoundaryDeploymentStep.sourceStep setup
    (commandCodec wire parse (normalizationSender query state) query) (nativeReader parse) erased checks seed query state

noncomputable def handler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  CborCommandFilter.handler allowed reject (baseHandler setup wire parse checks seed)

noncomputable def source (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    PqxdhBoundaryProgram.Step Spec (PqxdhDeploymentNative.State KemSK) :=
  CborCommandFilter.source allowed reject (baseSource setup wire parse erased checks seed)

/-- Dynamic per-owner registration normalization preserves the original per-command model equality at every complete state. -/
theorem base_step_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (state : PqxdhDeploymentNative.State KemSK) :
    baseSource setup wire parse erased checks seed query state =
      PqxdhBoundaryProgram.liftStep (baseHandler setup wire parse checks seed) query state := by
  unfold baseSource PqxdhBoundaryProgram.liftStep baseHandler
  rw [PqxdhBoundaryDeploymentStep.step_exact]
  simp only [PqxdhBoundaryProgram.liftStep, StateT.run, CborCommandFilter.atState]

/-- Exact admission runs on both sides before the native primitive callbacks, with complete moved-token rejection effects. -/
theorem step_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (state : PqxdhDeploymentNative.State KemSK) :
    source setup wire parse erased checks seed query state =
      PqxdhBoundaryProgram.liftStep (handler setup wire parse checks seed) query state :=
  CborCommandFilter.step_exact allowed reject _ _ (base_step_exact setup wire parse erased checks seed) query state

/-- Complete adaptive operational composition includes every oversized command and every returned state. -/
theorem execute_exact {X : Type} (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option NativeFrame) (erased : Std.Array Std.U8 357#usize)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) (work : OracleComp Spec X)
    (state : PqxdhDeploymentNative.State KemSK) :
    PqxdhBoundaryProgram.execute (source setup wire parse erased checks seed) work state =
      (fun result => (.ok result.1, result.2)) <$>
        (simulateQ (handler setup wire parse checks seed) work).run state :=
  CborCommandFilter.execute_exact allowed reject _ _ (base_step_exact setup wire parse erased checks seed) work state

/-- The production reader's full decode is exactly the bounded complete native parser. -/
theorem decode_native (parse : Pqxdh.Bytes → Option NativeFrame) (raw : Pqxdh.Bytes) :
    RawCtxFrameDecoding.decode (nativeReader parse).model raw = frameDecoder parse raw := by
  by_cases bounded : raw.length ≤ CborSizing.maxMessageSize <;> cases parsed : parse raw <;>
    simp [RawCtxFrameDecoding.decode, RawCtxFrameDecoding.frameRoot, RawCtxFrameDecoding.complete,
      RawCtxNativeFramePrelude.Reader.model, nativeReader, frameDecoder, CborTransport.boundedDecoder,
      bounded, parsed, RawCtxNativeFramePrelude.sliceBytes, decoded, Slice.new]

/-- Header routing has exactly the full validation failure domain, including invalid payload fields. -/
theorem sender_native (parse : Pqxdh.Bytes → Option NativeFrame) (raw : Pqxdh.Bytes) :
    RawCtxFrameDecoding.sender (nativeReader parse).model raw =
      RawCtxReceive.DecodedFrame.sender <$> frameDecoder parse raw := by
  by_cases bounded : raw.length ≤ CborSizing.maxMessageSize <;> cases parsed : parse raw <;>
    simp [RawCtxFrameDecoding.sender, RawCtxFrameDecoding.frameRoot, RawCtxFrameDecoding.complete,
      RawCtxNativeFramePrelude.Reader.model, nativeReader, frameDecoder, CborTransport.boundedDecoder,
      bounded, parsed, RawCtxNativeFramePrelude.sliceBytes, decoded, Slice.new]

/-- A rejected by-value build consumes its token while preserving the live Server and primitive caches. -/
theorem reject_build_consumes (session : Nat) (payload : Option Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (reject (.inr (.build session payload)) state).1 = none ∧
      (reject (.inr (.build session payload)) state).2.native.shared.2.pending session = none ∧
      (reject (.inr (.build session payload)) state).2.native.shared.2.server = state.native.shared.2.server ∧
      (reject (.inr (.build session payload)) state).2.native.shared.2.ctx = state.native.shared.2.ctx := by
  simp [reject, consumePending]

/-- Oversized send rejection does not allocate or advance any live ratchet. -/
theorem reject_send_stutters (keyId : Std.U64) (index : Nat) (plaintext : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    reject (.inr (.serverSend keyId plaintext)) state = (none, state) ∧
      reject (.inr (.beaconSend index plaintext)) state = (none, state) := ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.CborProductionBoundary

/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.base_step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.base_step_exact
/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.step_exact
/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.execute_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.execute_exact
/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.decode_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.decode_native
/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.sender_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.sender_native
/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.reject_build_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.reject_build_consumes
/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.reject_send_stutters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.reject_send_stutters

/-- info: 'BeaconcryptCore.Computational.CborProductionBoundary.registration_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborProductionBoundary.registration_writer
