-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerMask

/-! The actual root-free response controller retains its physical owner address through every authentication, root, first-record and installation branch. Only phase fields change. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFinishFields
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}
private abbrev OM (Value : Type) := RegistrationBeaconReferenceFinish.OwnerM n KemSK Auxiliary mlSource Value
private def Keeps (expected : Nat) (work : OM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) Value) : Prop :=
  ∀ owner env result, owner.worldOwner = expected →
    result ∈ support ((work.run owner).run env) → result.1.2.worldOwner = expected

private theorem pure_keeps (expected : Nat) (value : Value) :
    Keeps expected (pure value : OM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) Value) := by
  intro owner env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps {Next : Type} (expected : Nat)
    (work : OM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) Value)
    (next : Value → OM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) Next)
    (first : Keeps expected work) (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owner env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owner env middle prior reached) continued

private theorem lift_keeps (expected : Nat)
    (work : M n KemSK Auxiliary Value) :
    Keeps expected (StateT.lift work : OM (mlSource := mlSource) Value) := by
  intro owner env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _, returned⟩ := supported
  cases returned
  exact prior

private theorem phase_keeps (expected : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Keeps expected ((modify fun (owner : SelectedOwner mlSource) => { owner with phase }) : OM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) Unit) := by
  intro owner env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem abort_keeps (expected : Nat) (owner : SelectedOwner mlSource) :
    Keeps expected (RegistrationBeaconReferenceFinish.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) := by
  exact bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _)

private theorem preparation_keeps (expected : Nat) (setup : Setup base KemSK)
    (packet : Option registration.ResponsePacket) :
    Keeps expected (finishPreparation (n := n) (Auxiliary := Auxiliary) setup mlSource packet) := by
  intro owner env result prior supported
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase <;> simp only [phase] at supported
  all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; exact prior }
  case initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div =>
        simp only [moved, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact prior
    | ok aborted =>
        simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, mem_support_bind_iff] at supported
        obtain ⟨accepted, reached, continued⟩ := supported
        have rest : ∀ answer : RustM RegistrationResponseExecutor.ResponseResult, Keeps (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) expected (match answer with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.Err _) => pure (.ok none)
          | .ok (.Ok authenticated) => StateT.lift (agreement (n := n) setup owner oneTime authenticated)) := by
          intro answer
          cases answer with
          | fail error | div => exact pure_keeps expected _
          | ok reply => cases reply with
            | Err error => exact pure_keeps expected _
            | Ok authenticated => exact lift_keeps expected _
        have unchanged := lift_keeps (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mlSource := mlSource) expected _
          { owner with phase := .aborted aborted } env accepted prior reached
        exact rest accepted.1.1 accepted.1.2 accepted.2 result unchanged continued

private theorem complete_keeps (expected : Nat)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready) :
    Keeps expected (RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source owner ready) := by
  unfold RegistrationBeaconReferenceFinish.complete
  apply bind_keeps expected _ _ (lift_keeps expected _)
  intro completed
  cases completed with
  | fail error | div => exact bind_keeps expected _ _ (abort_keeps expected owner) (fun _ => pure_keeps expected _)
  | ok reply => cases reply with
    | Err error => exact bind_keeps expected _ _ (abort_keeps expected owner) (fun _ => pure_keeps expected _)
    | Ok completed => exact bind_keeps expected _ _ (phase_keeps expected _) (fun _ => pure_keeps expected _)

/-- Every actual selected or ordinary response-controller path retains its physical owner address. -/
theorem finish_index (setup : Setup base KemSK) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × SelectedOwner mlSource) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationBeaconReferenceFinish.finish (n := n) setup mlSource packet).run owner).run env)) :
    result.1.2.worldOwner = owner.worldOwner := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase <;> simp only [phase] at supported
  all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl }
  case initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div =>
        simp only [moved, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        rfl
    | ok aborted =>
        exact (bind_keeps owner.worldOwner _ _ (preparation_keeps owner.worldOwner setup packet) (fun prepared => by
          cases prepared with
          | fail error | div => exact bind_keeps owner.worldOwner _ _ (abort_keeps owner.worldOwner owner) (fun _ => pure_keeps owner.worldOwner _)
          | ok reply => cases reply with
            | none => exact bind_keeps owner.worldOwner _ _ (abort_keeps owner.worldOwner owner) (fun _ => pure_keeps owner.worldOwner _)
            | some ready => exact complete_keeps owner.worldOwner setup.source owner ready)) owner env result rfl supported

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFinishFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFinishFields.finish_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFinishFields.finish_index
