-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement

/-! Public Beacon preparation changes its agreement-request log but never the separate record-request ledger. This is derived from the actual callbacks, including early rejection and the final prepare query. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceAgreementScope
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

private def Keeps {Index : Type} {target : OracleSpec Index}
    (work : StateT (EnvState Auxiliary) (OracleComp target) Value) : Prop :=
  ∀ before after value, (value, after) ∈ support (work.run before) →
    after.recordRequests = before.recordRequests

private theorem pure_keeps {Index : Type} {target : OracleSpec Index} (value : Value) :
    Keeps (pure value : StateT (EnvState Auxiliary) (OracleComp target) Value) := by
  intro before after returned supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem lift_keeps {Index : Type} {target : OracleSpec Index} (work : OracleComp target Value) :
    Keeps (StateT.lift work : StateT (EnvState Auxiliary) (OracleComp target) Value) := by
  intro before after value supported
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨reply, _reached, equal⟩ := supported
  cases equal
  rfl

private theorem bind_keeps {Index Next : Type} {target : OracleSpec Index}
    (work : StateT (EnvState Auxiliary) (OracleComp target) Value)
    (next : Value → StateT (EnvState Auxiliary) (OracleComp target) Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before after value supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1 middle.2 after value continued).trans (first before middle.2 middle.1 reached)

private theorem requests_keeps {Index : Type} {target : OracleSpec Index}
    (requests : List RegistrationAgreementExecutor.Request) :
    Keeps ((modify fun (env : EnvState Auxiliary) => { env with requests := env.requests ++ requests }) :
      StateT (EnvState Auxiliary) (OracleComp target) Unit) := by
  intro before after value supported
  simp only [StateT.run_modify, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem program_keeps {Index Query : Type} {target : OracleSpec Index} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (StateT (EnvState Auxiliary) (OracleComp target)))
    (step : ∀ query, Keeps (implementation query)) (work : OracleComp spec Value) :
    Keeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps _ _ (step query) ih

private theorem backend_keeps (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Keeps (backend (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) :=
  bind_keeps _ _ (requests_keeps _) (fun _ => lift_keeps _)

private theorem aux_keeps (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain) :
    Keeps (RegistrationBeaconRootInterpreter.auxImpl
      (backend (n := n) (Auxiliary := Auxiliary) setup owner oneTime) authenticated query) := by
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl]
  all_goals exact program_keeps _ (backend_keeps setup owner oneTime) _

private theorem prefix_keeps (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain) :
    Keeps (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) (Auxiliary := Auxiliary) setup owner oneTime) authenticated)
      visit query) := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl]
  all_goals first
    | exact aux_keeps setup owner oneTime authenticated _
    | exact bind_keeps _ _ (requests_keeps _) (fun _ => pure_keeps _)

/-- Public collection and actual prepare retain precisely the input record-request ledger on every supported result. -/
theorem agreement_keeps (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : EnvState Auxiliary)
    (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (supported : (result, after) ∈ support
      ((agreement (n := n) setup owner oneTime authenticated).run before)) :
    after.recordRequests = before.recordRequests := by
  have collector : Keeps (collect (n := n) (Auxiliary := Auxiliary) setup owner oneTime authenticated) :=
    program_keeps _ (prefix_keeps setup owner oneTime authenticated) _
  have complete : Keeps (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime authenticated) := by
    unfold agreement
    apply bind_keeps _ _ collector
    intro pending
    cases pending with
    | none => exact pure_keeps _
    | some pending => exact lift_keeps _
  exact complete before after result supported

end BeaconcryptCore.Computational.RegistrationBeaconReferenceAgreementScope

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceAgreementScope.agreement_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceAgreementScope.agreement_keeps
