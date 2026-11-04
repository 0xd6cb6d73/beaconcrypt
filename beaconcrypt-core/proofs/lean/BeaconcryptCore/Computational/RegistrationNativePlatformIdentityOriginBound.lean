-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginBound

/-! The current runtime's concrete generated joint-Ed client has the ordinary finite field-origin monitor bound. Its value marginal is the literal initialized dynamic-writer profile with the whole P poststate. This is the unsigned-field monitor bound; causal successful-publication origin still requires failed-signature suppression and its hidden-ROM recognition argument. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (FreshBounds Budget)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value Next : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def reduction (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) (count : Nat)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (target : Fin (count + 1)) :=
  PqxdhJointIdentityFreshness.globalReduction setup.joint target ordinaryFallback
    (PqxdhDynamicIdentityRouting.routedAdversary count ordinaryFallback
      (PqxdhDynamicIdentityReports.reportExtractor setup.joint (count + 1) fallback
        (PqxdhJointPhase1Reports.routedClient setup.joint (count + 1)
          (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit
            identityIndex serverKeyId bounds mode adversary event previous))))

/-- The ordinary field-origin monitor keeps exactly the actual initialized runtime value and external poststate. -/
theorem native_value (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) (count : Nat) :
    Prod.fst <$> PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit
        identityIndex serverKeyId bounds mode adversary event previous) =
      (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit
        identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (fun result => event (result.1, (result.2.1, ())))).run previous := by
  have projected := congrArg (fun distribution => Prod.fst <$> distribution)
    (RegistrationNativeIdentityReportSource.run_source setup.joint count
      (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit
        identityIndex serverKeyId bounds mode adversary event previous))
  simp only [Functor.map_map, Prod.map_def, id_eq] at projected
  change _ = (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
    (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit
      identityIndex serverKeyId bounds mode adversary event previous)).run' PqxdhDynamicIdentityPool.initialState at projected
  rw [RegistrationNativePlatformIdentityMainProfile.client_source] at projected
  exact projected

/-- Finite routing of the exact actual client uses qCreate and adds only the explicit generated-identity sum, without a query/event/source-game premise. -/
theorem field_origin_bound (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (previous : Platform) (budget : Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint (count + 1)
      (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit
        identityIndex serverKeyId bounds mode adversary event previous))}[result.2.1.occurred = true] ≤
      ∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId
          bounds mode adversary event previous count fallback ordinaryFallback target) := by
  have creates := (RegistrationNativePlatformIdentityMainBounds.client_creates (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit
    identityIndex serverKeyId bounds mode adversary event previous budget bounded).mono room
  exact PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum setup.joint count _ fallback ordinaryFallback creates

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound.native_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound.native_value
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound.field_origin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound.field_origin_bound
