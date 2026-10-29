-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportProfile

/-! The actual generated-startup native client has an ordinary finite joint Ed25519/converted-static-DH origin bound under its existing whole-adversary NativeInterface.Respects contract. The source creation cap is proved structurally before finite routing. The loss is only the sum over generated identity positions; no field, report-position or public-key alias factor is introduced. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Budget)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def reduction (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (count : Nat)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (target : Fin (count + 1)) :=
  PqxdhJointIdentityFreshness.globalReduction setup.joint target ordinaryFallback
    (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
      (PqxdhDynamicIdentityReports.reportExtractor setup.joint (count + 1) fallback
        (PqxdhJointPhase1Reports.routedClient setup.joint (count + 1)
          (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit
            identityIndex serverKeyId bounds mode adversary event))))

/-- Actual source-field origin detection is bounded by the concrete ordinary joint-use weak-EUF reductions, with finite routing justified on every client reply. -/
theorem field_origin_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (budget : Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint (count + 1)
      (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit
        identityIndex serverKeyId bounds mode adversary event))}[result.2.1.occurred = true] ≤
      ∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (reduction (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
          bounds mode adversary event count fallback ordinaryFallback target) := by
  have creates := (RegistrationNativeIdentityProfileCreateCaps.client_bound (n := n) setup checks wire route representation source ensureInit
    identityIndex serverKeyId bounds mode adversary event budget bounded).mono room
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint count _ fallback ordinaryFallback creates

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginBound.field_origin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginBound.field_origin_bound
