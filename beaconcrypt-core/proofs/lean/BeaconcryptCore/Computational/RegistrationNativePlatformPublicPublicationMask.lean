-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMask
/-! Selected-owner restoration commutes with the actual stateful Init publication. Crypto and extracted writer leaves execute in the same common monad; complete failed writer effects are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformPublicMask
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
variable {n : Nat} {KemSK Auxiliary A E : Type} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem program {I : Type} {spec : OracleSpec I}
    (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding)
    (handler : QueryImpl spec (RegistrationNativePlatformGenericBundle.M source Auxiliary m))
    (allowed : ∀ query, Equivariant selected scalar publicPrekey (handler query))
    (work : OracleComp spec A) :
    Equivariant selected scalar publicPrekey (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_equivariant selected scalar publicPrekey value
  | query_bind query next ih =>
      simpa only [simulateQ_bind, simulateQ_spec_query] using bind_equivariant selected scalar publicPrekey _ _ (allowed query) ih

noncomputable def joint {I : Type} {base : OracleSpec I}
    (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (RegistrationNativePlatformGenericBundle.M source Auxiliary m)
  | .inl query => RegistrationNativePlatformGenericBundle.liftLegacy implementation
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)
  | .inr query => StateT.lift (StateT.lift (writer query))

theorem publication_tree {I : Type} {base : OracleSpec I}
    (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    simulateQ (joint (Auxiliary := Auxiliary) implementation writer setup index owner)
      (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa) =
      RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy implementation
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoderWith writer) control inputs coins pin mldsa := by
  rw [RegistrationNativePlatformWriter.begin_interpret]
  simp only [joint]
  congr 1
  funext view
  exact simulateQ_liftTarget writer _

theorem publication {I : Type} {base : OracleSpec I}
    (implementation : QueryImpl (Trusted n KemSK) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (selected : Nat) (scalar : ScalarBytes) (publicPrekey : PeerEncoding) :
    Equivariant selected scalar publicPrekey
      (RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy implementation
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoderWith writer) control inputs coins pin mldsa :
          RegistrationNativePlatformGenericBundle.M source Auxiliary m _) := by
  rw [← publication_tree implementation writer setup index owner control inputs coins pin mldsa]
  apply program
  intro query
  cases query with
  | inl query => exact outgoing setup implementation index owner selected scalar publicPrekey query
  | inr query => exact lift_equivariant selected scalar publicPrekey _
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask.publication_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask.publication_tree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicPublicationMask.publication
