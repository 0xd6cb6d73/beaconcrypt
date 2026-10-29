-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceRequestBase

/-! The actual public Server acceptance path appends native agreement requests while retaining the separate record-request markers. Mandatory verification, replay, reservation, every ordinary primitive and indexed KEM getter, root preparation and one-use-capability retention are followed directly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceAcceptRequests
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationServerOpenReferenceCompiler (M)
open RegistrationBeaconReferenceCompiler (Spec)
open RegistrationServerReferenceRequestBase (forward_support)
attribute [local irreducible] RegistrationAuthenticationCompiler.program
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}

private theorem old_backend_keeps (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) :
    RegistrationServerReferenceRequestBase.Keeps (RegistrationServerReferenceCompiler.backend (n := n) setup checks query) := by
  intro env result supported
  have raw := forward_support RegistrationServerReferenceCompiler.effect
    ((RegistrationWorldAgreementCompiler.compiler setup.source (RegistrationServerRoleBackend.localBackend setup checks) query).run env) result supported
  simp only [RegistrationWorldAgreementCompiler.compiler, StateT.run, support_map] at raw
  obtain ⟨inner, _, rfl⟩ := raw
  rfl

private theorem backend_keeps (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) :
    RegistrationServerReferenceRequestBase.Keeps (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks query) := by
  intro env result supported
  cases query with
  | encapsulate key =>
      simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run, support_map] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      rfl
  | _ =>
      exact old_backend_keeps setup checks _ env result
        (forward_support RegistrationNativeKemReferenceCompiler.lift
          ((RegistrationServerReferenceCompiler.backend setup checks _).run env) result supported)

private theorem visit_keeps (point : PqxdhBeaconPhase2Preparation.Word32) :
    RegistrationServerReferenceRequestBase.Keeps (RegistrationNativeKemReferenceCompiler.visit (n := n) (KemSK := KemSK) point) := by
  intro env result supported
  simp only [RegistrationNativeKemReferenceCompiler.visit, RegistrationNativeKemReferenceCompiler.ordinary,
    RegistrationServerReferenceCompiler.visit, StateT.run, simulateQ_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem prefix_keeps (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain) :
    RegistrationServerReferenceRequestBase.Keeps (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
      RegistrationNativeKemReferenceCompiler.visit query) := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact RegistrationServerReferenceRequestBase.program_keeps _ (backend_keeps setup checks) _
    | exact RegistrationServerReferenceRequestBase.bind_keeps _ _ (visit_keeps _) (fun _ => RegistrationServerReferenceRequestBase.pure_keeps _)

private theorem collect_keeps (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    RegistrationServerReferenceRequestBase.Keeps (RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated) :=
  RegistrationServerReferenceRequestBase.program_keeps _ (prefix_keeps setup checks) _

private def Keeps (work : M n KemSK Value) : Prop :=
  ∀ before env result, result ∈ support ((work.run before).run env) → result.2.recordRequests = env.recordRequests

private theorem pure_keeps (value : Value) : Keeps (pure value : M n KemSK Value) := by
  intro before env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (work : M n KemSK Value) (next : Value → M n KemSK Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before env middle reached)

private theorem lift_keeps (work : StateT Environment (OracleComp (Spec n KemSK)) Value)
    (law : RegistrationServerReferenceRequestBase.Keeps work) : Keeps (StateT.lift work : M n KemSK Value) := by
  intro before env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, reached, rfl⟩ := supported
  exact law env middle reached

private theorem get_keeps : Keeps (get : M n KemSK RegistrationServerMaterialFrontend.State) := by
  intro before env result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem agreement_keeps (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Keeps (RegistrationServerOpenReferenceCompiler.agreement (n := n) setup checks packet authenticated) := by
  unfold RegistrationServerOpenReferenceCompiler.agreement
  apply bind_keeps _ _ (lift_keeps _ (collect_keeps setup checks packet authenticated))
  intro pending
  cases pending with
  | none => exact pure_keeps _
  | some pending => exact lift_keeps _ (RegistrationServerReferenceRequestBase.lift_keeps _)

private theorem retain_keeps (ready : RegistrationServerReferenceRoot.Ready) :
    Keeps (RegistrationServerOpenReferenceCompiler.retain (n := n) (KemSK := KemSK) ready) := by
  intro before env result supported
  cases actual : RegistrationServerMaterialFrontend.retain ready before with
  | fail error | div =>
      simp only [RegistrationServerOpenReferenceCompiler.retain, StateT.run, actual] at supported
      cases supported
      rfl
  | ok returned =>
      rcases returned with ⟨reply, after⟩
      simp only [RegistrationServerOpenReferenceCompiler.retain, StateT.run, actual] at supported
      cases supported
      rfl

private theorem after_keeps (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Keeps (RegistrationServerOpenReferenceCompiler.afterAuthentication (n := n) setup checks packet authenticated) := by
  unfold RegistrationServerOpenReferenceCompiler.afterAuthentication
  apply bind_keeps _ _ get_keeps
  intro before
  split
  · exact pure_keeps _
  · split
    · apply bind_keeps _ _ (agreement_keeps setup checks packet authenticated)
      intro result
      cases result with
      | fail error | div => exact pure_keeps _
      | ok pending => cases pending with
        | none => exact pure_keeps _
        | some ready => exact retain_keeps ready
    · exact pure_keeps _

/-- Every actual public accept result preserves the caller's record-request marker list, including rejected verification, replay and all later failures. -/
theorem accept_keeps (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment)
    (result : (RustM (Option Nat) × RegistrationServerMaterialFrontend.State) × Environment)
    (supported : result ∈ support (((RegistrationServerOpenReferenceCompiler.accept (n := n) setup checks verify packet).run before).run env)) :
    result.2.recordRequests = env.recordRequests := by
  have law : Keeps (RegistrationServerOpenReferenceCompiler.accept (n := n) setup checks verify packet) := by
    unfold RegistrationServerOpenReferenceCompiler.accept
    apply bind_keeps _ _ get_keeps
    intro current
    apply bind_keeps _ _ (lift_keeps _ (RegistrationServerReferenceRequestBase.lift_keeps _))
    intro checked
    cases checked with
    | fail error | div => exact pure_keeps _
    | ok answer =>
        rcases answer with ⟨events, verdict⟩
        cases verdict with
        | Accepted authenticated => exact after_keeps setup checks packet authenticated
        | _ => exact pure_keeps _
  exact law before env result supported

end BeaconcryptCore.Computational.RegistrationServerReferenceAcceptRequests
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceAcceptRequests.accept_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceAcceptRequests.accept_keeps
