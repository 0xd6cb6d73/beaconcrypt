-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication
/-! The actual generated-owner outgoing callback has exactly its explicit hash cost. ML signing, indexed attached Ed signing, failed signatures and chronological source bookkeeping contribute no shared hash calls. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingHashBounds
open RegistrationNativePlatformIdentityFrontendHashBounds
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def IsOutgoingHash : RegistrationBeaconInitExecutor.Spec.Domain → Prop
  | .inl (.hash _) => True
  | _ => False
instance : DecidablePred IsOutgoingHash := fun query => by
  cases query with
  | inr query => simp only [IsOutgoingHash]; infer_instance
  | inl query => cases query <;> simp only [IsOutgoingHash] <;> infer_instance

private theorem indexed_sign_bound (owner : RegistrationNativeIdentityFrontend.Owner source) (message : Pqxdh.Bytes) :
    Bounded (StateT.lift (StateT.lift
      (RegistrationNativeIdentityInterface.sign (RegistrationNativeIdentityFrontend.Ambient n KemSK) owner.identity message)) :
      RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source _) 0 := by
  apply lift_free_bound
  simp [RegistrationNativeIdentityInterface.sign, IsHash]

/-- Every actual outgoing source branch consumes only its one explicit shared hash, if present. -/
theorem outgoing_bound (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Bounded (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query)
      (if IsOutgoingHash query then 1 else 0) := by
  cases query with
  | inl query => cases query with
    | hash request => exact hash_bound request
    | sign request payload digest =>
      unfold RegistrationNativeIdentityFrontend.outgoing
      exact bind_bound _ _ 0 0 (sample_bound _) (fun _ =>
        bind_bound _ _ 0 0 (update_env_bound _) (fun _ => pure_bound _ _))
  | inr request =>
    classical
    simp only [IsOutgoingHash, ite_false, RegistrationNativeIdentityFrontend.outgoing]
    split
    · apply bind_bound _ _ 0 0 (indexed_sign_bound _ _)
      intro reply
      cases reply with
      | none => exact pure_bound _ _
      | some signature =>
        exact bind_bound _ _ 0 0 (modify_bound _) (fun _ => pure_bound _ _)
    · exact pure_bound _ _
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingHashBounds.outgoing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingHashBounds.outgoing_bound
