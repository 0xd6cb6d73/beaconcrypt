-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleMaterial
import BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformCutLift
/-! Actual source ML vector/borrow conversion and the Ed attached-signature helper commute with the generic signing-cut interpreter. The complete publication erases only the private cut through any stateful actual encoder, retaining every native and base-monad poststate. This is the source primitive/reply publication fold; whole private owner installation is a separate composition. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundleNative
open BeaconcryptCore.Computational
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable {S Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable [ed : AdapterInitEdPrimitive.Operations]

def vector : RegistrationSigningShared.SignReply → Option (alloc.vec.Vec U8)
  | .none => .none
  | .some bytes => .some ⟨bytes.val, bytes.property⟩

omit ed [Monad m] [LawfulMonad m] in
theorem borrowed_vector (reply : RegistrationSigningShared.SignReply) :
    AdapterPublicInitPublication.borrowed (vector reply) = reply := by
  cases reply <;> rfl

omit ed in
private theorem map_lifted {A B : Type} (function : A → B) (work : StateT S m A) :
    liftWorld (function <$> work) = function <$> liftWorld work := by
  simpa only [map_eq_bind_pure_comp, Function.comp_def, RegistrationNativePlatformCutLift.pure_lifted] using
    RegistrationNativePlatformCutLift.bind_lifted work (fun value => pure (function value))

variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))

private theorem ed_lifted (publicKey : Std.Array U8 32#usize)
    (signer : Slice U8 → StateT S m (core.result.Result (alloc.vec.Vec U8) ed.Error))
    (request : registration.Ed25519SigningRequest) :
    AdapterPublicInitPublication.edMethod publicKey (fun message => liftWorld (signer message)) request =
      liftWorld (AdapterPublicInitPublication.edMethod publicKey signer request) := by
  unfold AdapterPublicInitPublication.edMethod
  split
  · exact (map_lifted _ _).symm
  · exact (RegistrationNativePlatformCutLift.pure_lifted _).symm

noncomputable def outgoing (publicKey : Std.Array U8 32#usize)
    (signer : Slice U8 → StateT S m (core.result.Result (alloc.vec.Vec U8) ed.Error)) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (State S) m) :=
  AdapterPublicInitPublication.outgoing (RegistrationNativePlatformCutJournal.hash impl)
    (AdapterPublicInitPublication.edMethod publicKey (fun message => liftWorld (signer message)))

theorem outgoing_source (publicKey : Std.Array U8 32#usize)
    (signer : Slice U8 → StateT S m (core.result.Result (alloc.vec.Vec U8) ed.Error)) :
    outgoing impl publicKey signer =
      RegistrationNativePlatformCutJournal.extended (RegistrationNativePlatformCutJournal.source impl (fun _ => pure .None))
        (fun request => liftWorld (AdapterPublicInitPublication.edMethod publicKey signer request)) := by
  funext query
  cases query with
  | inl query => cases query with
    | hash request => rfl
    | sign request payload digest => rfl
  | inr request => exact ed_lifted publicKey signer request

/-- Actual source reply conversions erase only the private ML hash cut through arbitrary stateful publication. -/
theorem publication (publicKey : Std.Array U8 32#usize)
    (signer : Slice U8 → StateT S m (core.result.Result (alloc.vec.Vec U8) ed.Error))
    (encode : registration.InitView → StateT S m (RustM (Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (before : State S) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (outgoing impl publicKey signer)
        (fun signed => liftWorld (encode signed)) control inputs coins pin).run before =
      (RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativePlatformCutWorld.beaconOutgoing impl (AdapterPublicInitPublication.edMethod publicKey signer))
        encode control inputs coins pin).run before.1 := by
  rw [outgoing_source]
  exact RegistrationNativePlatformCutWorld.beacon impl (fun _ => pure .None) _ encode control inputs coins pin before
end BeaconcryptCore.Refinement.AdapterPublicBundleNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleNative.borrowed_vector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleNative.borrowed_vector

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleNative.outgoing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleNative.outgoing_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleNative.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleNative.publication
