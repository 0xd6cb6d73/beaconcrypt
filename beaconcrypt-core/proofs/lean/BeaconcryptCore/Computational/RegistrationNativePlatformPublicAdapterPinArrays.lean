-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage
/-! The selected primitive public-key object is a byte wrapper: every 32-byte array parses, while later conversion and verification retain their own rejection behavior. This follows from the explicit primitive representation contract and is not a curve-validity or protocol-security assumption. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays
open BeaconcryptCore.Refinement

theorem pin (bytes : Std.Array U8 32#usize) :
    PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice bytes.to_slice)=some bytes := by
  unfold PqxdhDeploymentInterface.parsePin PqxdhServerAuthExperiment.toWord32
  have width : (TranscriptAuthParts.absSlice bytes.to_slice).length=32 := by
    simp only [TranscriptAuthParts.absSlice,List.length_map,Std.Array.to_slice]
    exact bytes.property
  rw [dite_eq_left width]
  congr 1
  apply Subtype.ext
  have actual:=congrArg (fun value : Slice U8=>value.val) (AdapterPublicConcreteCodecs.input_roundtrip bytes.to_slice)
  exact actual

variable [ed : AdapterInitEdPrimitive.Operations] [material : PublicWrapperPlatform.Material]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

theorem parsed (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view) (bytes : Std.Array U8 32#usize) :
    AdapterPublicServerToken.ParsedKey bytes :=
  ⟨contract.object bytes,RegistrationNativePlatformPublicAdapterPinParsing.ed_decoded view contract bytes.to_slice bytes (pin bytes)⟩

theorem tokens (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (table : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput) :
    RegistrationNativePlatformPublicAdapterTokenLineage.Parsed table := by
  intro _index token _stored
  exact parsed view contract token.registration.agreement.binding.beacon_identity_public_key

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays.pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays.parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays.parsed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays.tokens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinArrays.tokens
