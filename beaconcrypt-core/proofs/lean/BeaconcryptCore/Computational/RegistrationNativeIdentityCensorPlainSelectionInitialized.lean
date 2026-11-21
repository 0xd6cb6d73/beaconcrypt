-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative
/-! The literal initialized plain-source first-selector event has exactly the checked guarded physical event mass and therefore the same named ordinary weak-EUF bound. Startup and all independent auxiliary material stay inside E. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (CoreModels.core.result.Result Unit E))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)


noncomputable def game (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) : ProbComp Bool := by
  classical
  exact do
    let initialized←RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
    match initialized with
    | none=>pure false
    | some initial=>do
      let result←RegistrationNativeIdentityCensorPlainSelection.coupled setup.joint selected placeholder
        (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder
          (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation initial.created initial.credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
          RegistrationNativeIdentityTemplateNativeClient.defaults
          (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
            initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
          (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
            ({knownInputs:=[PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0))
        ⟨PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]),none,none,none⟩
      pure (decide (RegistrationNativeIdentityCensorPlainSelection.Success setup.joint selected result))

/-- Policy-only ghost erasure commutes with literal startup and the actual normalized source visitor, retaining the same warm physical private state. -/
theorem probability (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous selected bundle accept placeholder)}[result=true]=
    Pr{let result←(RegistrationNativeIdentityTemplateGuardedPhysicalNative.game (n := n) setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous
        selected bundle accept placeholder)}[result=true] := by
  classical
  unfold game RegistrationNativeIdentityTemplateGuardedPhysicalNative.game
  apply prEvent_bind_congr
  intro initialized
  cases initialized with
  | none=>rfl
  | some initial=>
    simp only [bind_pure_comp,prEvent_map,decide_eq_true_eq]
    exact RegistrationNativeIdentityCensorPlainSelection.probability setup.joint selected bundle accept placeholder
      (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation initial.created initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
      RegistrationNativeIdentityTemplateNativeClient.defaults
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
        ({knownInputs:=[PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0)
      ({},⟨PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]),none,none,none⟩)

/-- The literal initialized plain first-selector success mass pays the named ordinary guarded adversary, with startup and other-key sampling inside E and no privately supplied state. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (target : Fin (budget.create+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result←(game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous target.val bundle accept placeholder)}[result=true] ≤
    PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativeIdentityTemplateGuardedLateNativeClient.reduction (n := n) setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous target bundle accept placeholder fallback) := by
  rw [probability]
  exact RegistrationNativeIdentityTemplateGuardedPhysicalNative.bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded target bundle accept placeholder fallback

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized.probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized.bound
