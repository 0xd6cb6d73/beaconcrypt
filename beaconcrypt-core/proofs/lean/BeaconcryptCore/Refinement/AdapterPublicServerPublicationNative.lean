-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleNative
import BeaconcryptCore.Refinement.AdapterPublicServerPublication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Request-only Server ML signing derives its actual payload and digest from the preceding Core hash cut. The source vector/borrow conversion and arbitrary stateful response writer erase only that private cut, retaining every real World and platform poststate. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative
open BeaconcryptCore.Computational
open RegistrationNativePlatformCutJournal (State)
open RegistrationNativePlatformCutErasure (liftWorld)
variable {S Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
variable (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)

noncomputable def primitives : AdapterPublicServerPublication.Primitives (StateT (State S) m) where
  hash := RegistrationNativePlatformCutJournal.hash impl
  sign := AdapterPublicBundleNative.sign impl fallback

theorem outgoing_source : AdapterPublicServerPublication.outgoing (primitives impl fallback) =
    RegistrationNativePlatformCutJournal.source impl fallback := by
  funext query
  cases query with
  | hash request => rfl
  | sign request payload digest =>
    change AdapterPublicInitPublication.borrowed <$> (AdapterPublicBundleNative.vector <$>
      RegistrationNativePlatformCutJournal.sign impl fallback request) = _
    simp only [Functor.map_map]
    have same : (fun reply => AdapterPublicInitPublication.borrowed (AdapterPublicBundleNative.vector reply)) = id := by
      funext reply
      exact AdapterPublicBundleNative.borrowed_vector reply
    rw [same, id_map]
    rfl

theorem publication
    (encode : registration.SignedResponseView → StateT S m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (before : State S) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformServerPublication.program
        (AdapterPublicServerPublication.outgoing (primitives impl fallback))
        (fun view => liftWorld (encode view)) pending).run before =
      (RegistrationNativePlatformServerPublication.program impl encode pending).run before.1 := by
  rw [outgoing_source]
  exact RegistrationNativePlatformCutWorld.server impl fallback encode pending before
end BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative.outgoing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative.outgoing_source
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPublicationNative.publication
