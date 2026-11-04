-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The constructor's checked fingerprint helper has the literal fixed-size pin result under its individual hash functional interpretation. All shared hash effects remain in the common monad. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorPin
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [children : ChildOperations (RustT m)]

theorem source (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request) :
    (beaconcrypt_public_request.auth.fingerprint_pin (m := RustT m) binding publicKey).run =
    (fun digest => RustM.ok (core.option.Option.Some (⟨binding, publicKey, RegistrationAuthenticationShared.digestArray digest⟩ : session.ServerAuthenticationPin))) <$>
      hash (.Single (Std.Array.to_slice publicKey)) := by
  rw [AdapterPublicWrapperPin.fingerprint_program binding publicKey _ hashLeaf]
  simp only [RegistrationNativeServerPinRecompute.program, RegistrationNativeServerPinRecompute.request,
    simulateQ_spec_query, simulateQ_map, bind_pure_comp,
    Functor.map_map, Aeneas.Std.bind_tc_ok, registration.PinFingerprint.resume, session.ServerAuthenticationPin.new]

end BeaconcryptCore.Refinement.AdapterBeaconConstructorPin

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorPin.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorPin.source
