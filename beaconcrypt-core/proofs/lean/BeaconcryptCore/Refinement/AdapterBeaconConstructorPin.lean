-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The constructor uses the exact fixed-size Server pin directly, without a fingerprint callback or Beacon credential. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorPin
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m] [LawfulMonad m]
theorem source (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    (beaconcrypt_public_request.auth.server_pin (m := RustT m) binding publicKey).run =
      pure (.ok (.Some (⟨binding, publicKey⟩ : session.ServerAuthenticationPin))) := by
  exact AdapterPublicWrapperPin.pin_program binding publicKey

end BeaconcryptCore.Refinement.AdapterBeaconConstructorPin

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorPin.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorPin.source
