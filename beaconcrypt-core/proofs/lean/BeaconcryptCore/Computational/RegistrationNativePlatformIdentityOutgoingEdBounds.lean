-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentitySourceEdBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityPublication
/-! The literal generated-owner outgoing callback issues at most one indexed Ed signing request precisely on its attached-signing branch. Rejected keys, missing signatures, ML work, hashes and bookkeeping keep their original source outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingEdBounds
open RegistrationNativePlatformIdentityFrontendEdBounds
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def IsOutgoingSign : RegistrationBeaconInitExecutor.Spec.Domain → Prop
  | .inr _ => True
  | _ => False
instance : DecidablePred IsOutgoingSign := fun query => by
  cases query with
  | inr query => simp only [IsOutgoingSign]; infer_instance
  | inl query => cases query <;> simp only [IsOutgoingSign] <;> infer_instance

private theorem indexed_sign_bound (owner : RegistrationNativeIdentityFrontend.Owner source) (message : Pqxdh.Bytes) :
    Bounded (StateT.lift (StateT.lift
      (RegistrationNativeIdentityInterface.sign (RegistrationNativeIdentityFrontend.Ambient n KemSK) owner.identity message)) :
      RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source _) 1 := by
  apply lift_free_bound
  simp [RegistrationNativeIdentityInterface.sign, IsSign]

theorem outgoing_bound (setup : Setup base KemSK) (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Bounded (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query)
      (if IsOutgoingSign query then 1 else 0) := by
  cases query with
  | inl query => cases query with
    | hash request => exact hash_bound request
    | sign request payload digest =>
      unfold RegistrationNativeIdentityFrontend.outgoing
      exact bind_bound _ _ 0 0 (sample_bound _) (fun _ =>
        bind_bound _ _ 0 0 (update_env_bound _) (fun _ => pure_bound _ _))
  | inr request =>
    classical
    simp only [IsOutgoingSign, ite_true, RegistrationNativeIdentityFrontend.outgoing]
    split
    · apply bind_bound _ _ 1 0 (indexed_sign_bound _ _)
      intro reply
      cases reply with
      | none => exact pure_bound _ _
      | some signature =>
        exact bind_bound _ _ 0 0 (modify_bound _) (fun _ => pure_bound _ _)
    · exact pure_bound _ _
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingEdBounds.outgoing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOutgoingEdBounds.outgoing_bound
