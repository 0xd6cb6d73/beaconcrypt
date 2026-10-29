-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarEager
import BeaconcryptCore.Computational.RegistrationNativeMainView

/-! Moving a selected scalar draw earlier does not introduce a read of omitted native/coin/record-request instrumentation. The actual constructor still executes every optional prefix and counted dummy draw before its pure roster-length choice. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarEagerView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (nativeView)
open RegistrationStateView (Stable)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The actual eager constructor retains every source branch while reading only the unchanged roster length. -/
theorem create_stable (setup : Setup base KemSK) (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeBeaconEnvView.Stable
      (RegistrationNativeScalarEager.create (n := n) setup source selected scalar edPin mlPin keyId) := by
  unfold RegistrationNativeScalarEager.create
  apply RegistrationNativeBeaconEnvView.bind_stable
  · exact RegistrationNativeBeaconEnvCreate.prepare_stable edPin mlPin keyId
  · intro prepared
    cases prepared with
    | fail error | div => exact RegistrationNativeBeaconEnvView.pure_stable _
    | ok prepared => cases prepared with
      | none => exact RegistrationNativeBeaconEnvView.pure_stable _
      | some prepared =>
          apply RegistrationNativeBeaconEnvView.bind_stable
          · exact RegistrationNativeBeaconEnvView.get_stable
          · intro owners
            exact RegistrationNativeBeaconEnvCreate.append_stable setup edPin keyId prepared.pin prepared.credentials
              prepared.identity (if owners.length = selected then scalar else prepared.prekey)

/-- Every actual eager typed query retains its literal native result after the explicitly named source view. -/
theorem handler_input (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Stable (nativeView (n := n))
      (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar query) := by
  cases query with
  | inl coin => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inl coin)
  | inr command => cases command with
    | create edPin mlPin keyId =>
        exact RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
          (create_stable setup selected scalar edPin mlPin keyId)
    | bundle owner => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.bundle owner))
    | accept packet => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.accept packet))
    | build handle application => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.build handle application))
    | finish owner packet => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.finish owner packet))
    | hmac key bytes => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.hmac key bytes))
    | hash bytes => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.hash bytes))
    | serverSend keyId plaintext => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.serverRaw raw))
    | beaconSend owner plaintext => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.beaconSend owner plaintext))
    | beaconRaw owner raw => exact RegistrationNativeMainView.handler_input setup checks wire route representation created credential (.inr (.beaconRaw owner raw))

/-- The original full secrecy compiler, or any other adaptive typed client, retains its entire eager native outcome under the stated source view. -/
theorem program_input (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Stable (nativeView (n := n))
      (simulateQ (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar) work) :=
  RegistrationStateView.program_stable nativeView RegistrationNativeMainViewLift.view_idempotent _
    (handler_input setup checks wire route representation created credential selected scalar) work

end BeaconcryptCore.Computational.RegistrationNativeScalarEagerView
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerView.create_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerView.create_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerView.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerView.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarEagerView.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarEagerView.program_input
