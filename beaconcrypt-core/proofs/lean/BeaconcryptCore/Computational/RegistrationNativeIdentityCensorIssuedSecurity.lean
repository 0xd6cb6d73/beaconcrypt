-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCollectorSuccess
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionInitialized
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorNormalizedInput
import BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The original initialized concrete mandatory-ML runtime satisfies unsigned-tuple publication strictly before acceptance, under its original broad final-owner event. The explicit bound consists only of named ordinary joint weak-EUF advantages: every primitive client samples independent startup and auxiliary material inside E. The causal source/selector/ROM/history connection is derived, with all failed attempts and later callbacks retained. This does not claim exact six-field or randomized ML-signature byte origin. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
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

local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve


/-- The exact initialized retained observation pays the same plain first-selector game at its normalized initial public input. This is the last source-state normalization before the ordinary primitive bound. -/
private theorem retained_conditional (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedRetained.run setup checks route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle accept placeholder true
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
        (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))))}[
          RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint selected result] ≤
    Pr{let result←(RegistrationNativeIdentityCensorPlainSelection.coupled setup.joint selected placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder
        (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks canonical route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
        RegistrationNativeIdentityTemplateNativeClient.defaults
        (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
        (((RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder (RegistrationNativeIdentityMainProfile.fromInitial initial,previous)),
          ({knownInputs:=[PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0))
      ⟨PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]),none,none,none⟩)}[
        RegistrationNativeIdentityCensorPlainSelection.Success setup.joint selected result] := by
  rw [RegistrationNativeIdentityCensorIssuedCollector.probability]
  exact RegistrationNativeIdentityCensorCollectorSuccess.bound setup checks route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle accept placeholder RegistrationNativeIdentityTemplateNativeClient.defaults
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
        ({knownInputs:=[PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)
        ((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
          (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])))) [] 0 rfl rfl

noncomputable def loss (budget : PqxdhDeploymentInterface.Budget) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (fallback : PqxdhJointIdentity.Forgery) : ℝ≥0∞ :=
  ∑ identity : Fin (budget.create+1),∑ accept : Fin budget.accept,∑ bundle : Fin budget.bundle,
    PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativeIdentityTemplateGuardedLateNativeClient.reduction (n := n) setup checks canonical route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous
          identity bundle.val accept.val placeholder fallback)

/-- Literal startup and exact initial joint-view erasure identify the retained-run upper bound with the same ordinary primitive first-selector experiment. -/
theorem physical_bound (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedRetainedInitialized.game (n := n) setup checks route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous selected bundle accept placeholder)}[
        RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint selected result] ≤
    Pr{let result←(RegistrationNativeIdentityCensorPlainSelectionInitialized.game (n := n) setup checks canonical route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous selected bundle accept placeholder)}[result=true] := by
  classical
  unfold RegistrationNativeIdentityCensorIssuedRetainedInitialized.game RegistrationNativeIdentityCensorPlainSelectionInitialized.game
  apply prEvent_bind_mono_of_forall_le_of_support
  intro initialized _started
  cases initialized with
  | none=>
    simp only [RegistrationNativeIdentityCensorIssuedRetained.Event,Option.elim_none,prEvent_pure,Bool.false_eq_true,ite_false]
    exact le_rfl
  | some initial=>
    simp only [bind_pure_comp,prEvent_map,decide_eq_true_eq]
    have original := retained_conditional setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous initial selected bundle accept placeholder
    rw [RegistrationNativeIdentityCensorNormalizedInput.visit setup checks canonical route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle accept placeholder RegistrationNativeIdentityTemplateNativeClient.defaults
        (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
        (RegistrationNativeIdentityMainProfile.fromInitial initial,previous)
        ({knownInputs:=[PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode) 0] at original
    exact original

/-- Each unchanged original initialized fixed identity/accept/bundle mass pays one named ordinary guarded joint-Ed adversary. Startup and independent auxiliary material are sampled inside that executable adversary. -/
theorem fixed_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (identity : Fin (budget.create+1)) (accept : Fin budget.accept) (bundle : Fin budget.bundle)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result←(RegistrationNativeIdentityIssuedOriginalFinite.cutGame (n := n) setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous bundle.val)}[
        RegistrationNativeIdentityIssuedOriginalFinite.Matched setup wire source budget identity accept bundle result] ≤
    PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativeIdentityTemplateGuardedLateNativeClient.reduction (n := n) setup checks canonical route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve source ensureInit identityIndex serverKeyId bounds mode adversary previous
          identity bundle.val accept.val placeholder fallback) := by
  apply (RegistrationNativeIdentityCensorIssuedRetainedInitialized.bound setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget identity accept bundle placeholder).trans
  apply (physical_bound setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous identity.val bundle.val accept.val placeholder).trans
  exact RegistrationNativeIdentityCensorPlainSelectionInitialized.bound setup checks canonical route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded identity bundle.val accept.val placeholder fallback

/-- The unchanged original initialized Issued event pays exactly the finite public identity/accept/bundle family of named ordinary joint weak-EUF adversaries. No native eligibility or prior-issuance condition is strengthened. -/
theorem issued_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result←(RegistrationNativeIdentityUnissuedOriginalInitialized.game (n := n) setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous)}[
        RegistrationNativeIdentityOriginalCausalInitialized.Issued setup wire source budget result] ≤
    loss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget placeholder fallback := by
  apply (RegistrationNativeIdentityIssuedOriginalFinite.cut_bound setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded).trans
  unfold loss
  apply Finset.sum_le_sum
  intro identity _identity
  apply Finset.sum_le_sum
  intro accept _accept
  apply Finset.sum_le_sum
  intro bundle _bundle
  exact fixed_bound setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded identity accept bundle placeholder fallback

/-- Original unsigned-tuple publication strictly before acceptance, on the literal initialized concrete mandatory-ML ordinary runtime. Eligibility is the original final-owner event, including aliases and owners created after the acceptance. The bound uses only named ordinary joint weak-EUF advantages of executable clients. -/
theorem causal_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (shortRejects : ∀ (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64 → setup.source.crypto.verify publicKey.toList bytes=none)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result←((RegistrationNativePlatformOrdinaryExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (RegistrationNativeIdentityOriginalCausalInitialized.event (n := n) setup wire source)).run previous)}[result.1=true] ≤
    RegistrationNativeIdentityUnissuedInitialized.loss (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget fallback+
    loss (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget placeholder fallback := by
  apply (RegistrationNativeIdentityOriginalCausalInitialized.unissued_bound setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded shortRejects fallback).trans
  exact add_le_add le_rfl (issued_bound setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded placeholder fallback)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.physical_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.physical_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.fixed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.issued_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.issued_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.causal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedSecurity.causal_bound
