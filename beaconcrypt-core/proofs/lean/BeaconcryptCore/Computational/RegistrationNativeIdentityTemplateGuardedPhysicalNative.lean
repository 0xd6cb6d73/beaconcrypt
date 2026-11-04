-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedFamilyWins
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateNativeClient
/-! The actual initialized physical first-selection event is bounded by the named ordinary weak-EUF adversary. Its literal startup, warm cache and raw create budget are derived internally. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative
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

noncomputable def physical (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) :=
  RegistrationNativeIdentityTemplateVisitorProbability.coupled setup.joint selected bundle accept placeholder
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
    RegistrationNativeIdentityTemplateNativeClient.defaults
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
    (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
      ({knownInputs := [PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0)
    ({},⟨PqxdhDynamicIdentityPool.initialState,
      (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]),none,none,none⟩)

/-- Literal supported startup supplies the warm cache provenance, while original Respects supplies the entire guarded family's create cap. -/
theorem conditional (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public))
    (target : Fin (budget.create+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (physical (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous target.val bundle accept placeholder initial)}[
        RegistrationNativeIdentityTemplateLatePhysical.Success setup.joint target.val result.1 result.2.1] ≤
    PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativeIdentityTemplateGuardedLateNativeClient.conditional (n := n) setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve source bounds mode adversary previous target bundle accept placeholder fallback (some initial)) := by
  have warm := RegistrationNativeIdentityCensorCacheProvenance.initialized setup ensureInit identityIndex serverKeyId initial started
  have loss := RegistrationNativeIdentityTemplateGuardedWins.loss setup target.val bundle accept placeholder
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
    RegistrationNativeIdentityTemplateNativeClient.defaults
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
    (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
      ({knownInputs := [PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0)
    rfl ({},⟨PqxdhDynamicIdentityPool.initialState,
      (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]),none,none,none⟩)
    ⟨⟨rfl,fun _=>rfl⟩,rfl,warm⟩ rfl
  have bill := RegistrationNativeIdentityTemplateLateNativeClient.code_create_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer
    reserveFrame erased helper reserve source bounds mode adversary previous target.val bundle accept placeholder initial budget bounded
  have primitiveBound := RegistrationNativeIdentityTemplateGuardedFamilyWins.source_bound setup.joint target
    (RegistrationNativeIdentityTemplateLateNativeClient.code setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous target.val bundle accept placeholder initial)
    (RegistrationNativeIdentityTemplateLateNativeClient.code_safe setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous target.val bundle accept placeholder initial)
    (bill.mono (Nat.le_succ _)) (RegistrationNativeIdentityTemplateLateNativeClient.publicBefore source initial) fallback
  exact loss.trans primitiveBound

noncomputable def game (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) : ProbComp Bool := by
  classical
  exact do
    let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
    match initialized with
    | none => pure false
    | some initial => do
        let result ← physical (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          source bounds mode adversary previous selected bundle accept placeholder initial
        pure (decide (RegistrationNativeIdentityTemplateLatePhysical.Success setup.joint selected result.1 result.2.1))

/-- The full actual physical success probability pays one named ordinary adversary. Startup refusal, warm cache, original raw resource allowance and all auxiliary-key sampling are retained inside the checked construction. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (target : Fin (budget.create+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let accepted ← (game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous target.val bundle accept placeholder)}[accepted=true] ≤
    PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativeIdentityTemplateGuardedLateNativeClient.reduction (n := n) setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous target bundle accept placeholder fallback) := by
  classical
  unfold RegistrationNativeIdentityTemplateGuardedLateNativeClient.reduction
  rw [←RegistrationNativeIdentityCensorChosenReduction.sampled_advantage]
  unfold game
  apply prEvent_bind_mono_of_forall_le_of_support
  intro initialized reached
  cases initialized with
  | none =>
    simp only [prEvent_pure,Bool.false_eq_true,ite_false]
    exact zero_le
  | some initial =>
    simp only [bind_pure_comp,prEvent_map,decide_eq_true_eq]
    exact conditional setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous initial reached budget (bounded initial.public) target bundle accept placeholder fallback

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative.conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative.conditional

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedPhysicalNative.bound
