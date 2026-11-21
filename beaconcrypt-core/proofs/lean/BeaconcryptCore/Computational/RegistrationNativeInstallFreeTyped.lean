-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallRouting
import BeaconcryptCore.Computational.RegistrationNativePairedOther

/-! Every actual typed native command except build and finish has no installation capability of either role. This uses the concrete original create/bundle/accept prefixes and their literal routing; arbitrary trusted owner operations are not asserted installation-free. The exact successful descriptor list therefore remains unchanged through the original G2 observer under every supported callback execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeInstallPredicate (GlobalInstall)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (role : Role) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
  (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
  (before : RegistrationNativePublicFrontend.State source)
include quiet

/-- The complete actual create, bundle, accept, coin, HMAC, hash and record callbacks have zero installation bill of either role on every original frontend state. -/
theorem typed_free :
    ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  apply OracleComp.IsQueryBoundP.of_imp _
    (RegistrationNativePairedOther.other_free role setup checks wire sign selectedOwner selectedAccept publicPrekey query quiet before)
  intro request counted
  rcases request with (prepare | (demand | common) | kem) | record
  all_goals simp only [GlobalInstall, RegistrationNativePairedSafe.GlobalInstall] at counted ⊢
  exact counted

/-- Every supported original observed execution of a nonmaterial typed callback preserves the exact chronological successful descriptor list of this role. -/
theorem messages_free (trace : RegistrationNativeG2Trace.State)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeG2Trace.handler
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)).run trace)) :
    RegistrationNativeInstallOrdinals.messages role result.2.events = RegistrationNativeInstallOrdinals.messages role trace.events :=
  RegistrationNativeInstallTrace.free role _
    (typed_free role setup checks wire source sign selectedOwner selectedAccept publicPrekey query quiet before) trace result supported

end BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped.typed_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped.typed_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped.messages_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallFreeTyped.messages_free
