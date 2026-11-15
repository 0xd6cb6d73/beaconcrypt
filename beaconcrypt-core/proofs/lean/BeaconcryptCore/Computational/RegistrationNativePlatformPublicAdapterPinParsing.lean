-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativeConcreteReaders
import BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
import BeaconcryptCore.Refinement.RegistrationInputs
/-! The opaque Ed public-byte object has its explicit primitive representation contract. The ML pin width conversion is the actual extracted standard-library array conversion. Neither is an assumption about a complete protocol callback or about the CBOR parser. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing
open BeaconcryptCore.Refinement
variable [ed : AdapterInitEdPrimitive.Operations]
variable [material : PublicWrapperPlatform.Material]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

structure EdContract (view : AdapterPublicWrapperState.MaterialView source KemSK) where
  object : Std.Array U8 32#usize →ed.PublicKey
  error : ed.Error
  operation : ∀input,beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes input=.ok
    (match PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice input) with
    | none=>.Err error
    | some bytes=>.Ok (object bytes))
  publicBytes : ∀bytes,view.edPublic (object bytes)=bytes

omit material ed in
theorem mldsa (input : Slice U8) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy input=
    .ok (match RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice input) with
      | none=>.Err ()
      | some bytes=>.Ok bytes) := by
  have bytes : (TranscriptAuthParts.absSlice input).map ProtocolComposition.concreteByte=input.val := by
    have actual:=congrArg (fun bytes : Slice U8=>bytes.val) (AdapterPublicConcreteCodecs.input_roundtrip input)
    exact actual
  have widths : (TranscriptAuthParts.absSlice input).length=input.val.length := by
    simp only [TranscriptAuthParts.absSlice,List.length_map]
  obtain ⟨result,actual,values⟩:=RegistrationInputs.copied_slice_exact 1952#usize input
  rw [actual]
  unfold RegistrationNativeWire.parseMldsaPin
  cases result with
  | Err error=>
    change input.val.length≠1952 at values
    rw [dite_eq_right (by simpa only [widths] using values)]
  | Ok output=>
    obtain ⟨same,width⟩:=values
    change input.val.length=1952 at width
    rw [dite_eq_left (widths.trans width)]
    congr 2
    apply Subtype.ext
    exact same.trans bytes.symm

theorem ed_decoded (view : AdapterPublicWrapperState.MaterialView source KemSK) (contract : EdContract view)
    (input : Slice U8) (bytes : Std.Array U8 32#usize)
    (parsed : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice input)=some bytes) :
    beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes input=.ok (.Ok (contract.object bytes)) := by
  rw [contract.operation,parsed]

omit material ed in
theorem ml_decoded (input : Slice U8) (bytes : Std.Array U8 1952#usize)
    (parsed : RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice input)=some bytes) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy input=.ok (.Ok bytes) := by
  rw [mldsa,parsed]

variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (AdapterPublicWrapperRustT.RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT m)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT m)]

omit material ed [LawfulMonad m] children in
private theorem lift_ok {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : AdapterPublicWrapperRustT.RustT m A)=pure value := rfl

omit children in
theorem constructor {R Error : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : EdContract view) (generator : rand_core.TryCryptoRng R Error)
    (keyId : U64) (edPin mlPin : Slice U8) (rng : R) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng
      (m:=AdapterPublicWrapperRustT.RustT m) generator keyId edPin mlPin rng=
    match PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice edPin),
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlPin) with
    | some identity,some ml=>AdapterBeaconConstructorBody.withInputs generator keyId (contract.object identity) ml rng
    | _,_=>pure (.Err (),rng) := by
  rw [AdapterBeaconConstructorBody.body]
  unfold AdapterBeaconConstructorBody.source
  rw [contract.operation]
  cases PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice edPin) with
  | none=>simp only [lift_ok,pure_bind,AdapterBeaconConstructorBody.reject]
  | some identity=>
    simp only [lift_ok,pure_bind]
    rw [mldsa]
    cases RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlPin) <;>
      simp only [lift_ok,pure_bind,AdapterBeaconConstructorBody.reject]

omit children in
theorem rejected {R Error : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : EdContract view) (generator : rand_core.TryCryptoRng R Error)
    (keyId : U64) (edPin mlPin : Slice U8) (rng : R)
    (invalid : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice edPin)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlPin)=none) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng
      (m:=AdapterPublicWrapperRustT.RustT m) generator keyId edPin mlPin rng=pure (.Err (),rng) := by
  rw [constructor view contract]
  rcases invalid with first|second
  · rw [first]
  · rw [second]
    cases PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice edPin) <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.mldsa' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.mldsa
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.constructor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.ml_decoded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing.rejected
