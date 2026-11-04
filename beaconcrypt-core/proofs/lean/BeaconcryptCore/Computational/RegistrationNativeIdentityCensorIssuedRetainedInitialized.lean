-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained
import BeaconcryptCore.Computational.RegistrationNativeIdentityIssuedOriginalFinite
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The actual initialized physical first-selection event is bounded by the named ordinary weak-EUF adversary. Its literal startup, warm cache and raw create budget are derived internally. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized
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

noncomputable def game (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none=>pure none
  | some initial=>(RegistrationNativeIdentityCensorIssuedRetained.run setup checks route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle accept placeholder true
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
        (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))))

/-- Actual empty-roster source ownership and the checked canonical-wire dictionary law discharge the retained bound at every initialized native state. -/
theorem conditional (initial : RegistrationNativeExperiment.Initial n KemSK source) (budget : PqxdhDeploymentInterface.Budget)
    (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint
      (RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation initial.created initial.credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer) bundle
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
        (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))))}[
        RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint canonical budget selected accept bundle result] ≤
    Pr{let result←(RegistrationNativeIdentityCensorIssuedRetained.run setup checks route representation initial.created initial.credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle accept placeholder true
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
        (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey]))))}[
          RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint selected result] := by
  have initialOwned := RegistrationNativePlatformIdentityCtxInitial.initial_owned setup.joint initial previous PqxdhDynamicIdentityPool.initialState
  have sourceLaw := RegistrationNativePlatformIdentityCtxCanonicalWire.handler (n := n) setup wire reserveFrame checks route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer erased helper writer
  rw [←sourceLaw]
  exact RegistrationNativeIdentityCensorIssuedRetained.bound setup checks route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve initial.created.server.server.metadata.sender bounds mode (adversary initial.public) budget
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),
        (PqxdhDynamicIdentityPool.initialState,(RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])))
      rfl rfl ⟨initialOwned,List.nodup_nil⟩ selected bundle accept placeholder

/-- The fixed original initialized i/a/b mass is bounded by the same literal startup and censored retained experiment; startup refusal and the exact warm cache remain inside this game. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget) (identity : Fin (budget.create+1))
    (accept : Fin budget.accept) (bundle : Fin budget.bundle) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityIssuedOriginalFinite.cutGame (n := n) setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous bundle.val)}[
        RegistrationNativeIdentityIssuedOriginalFinite.Matched setup wire source budget identity accept bundle result] ≤
    Pr{let result←(game (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous identity.val bundle.val accept.val placeholder)}[
        RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint identity.val result] := by
  classical
  unfold RegistrationNativeIdentityIssuedOriginalFinite.cutGame game
  apply prEvent_bind_mono_of_forall_le_of_support
  intro initialized _started
  cases initialized with
  | none=>
    simp only [RegistrationNativeIdentityIssuedOriginalFinite.Matched,RegistrationNativeIdentityCensorIssuedRetained.Event,Option.elim_none,prEvent_pure,ite_false]
    exact le_rfl
  | some initial=>
    simp only [prEvent_map,RegistrationNativeIdentityIssuedOriginalFinite.Matched,Option.elim_some]
    exact conditional setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous initial budget identity.val bundle.val accept.val placeholder

/-- The unchanged original initialized Issued event has an explicit finite i/a/b upper bound by actual censored retained runs. Final-owner eligibility and original failed attempts are unchanged. -/
theorem issued_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityUnissuedOriginalInitialized.game (n := n) setup checks wire route representation view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous)}[
        RegistrationNativeIdentityOriginalCausalInitialized.Issued setup wire source budget result] ≤
      ∑ identity : Fin (budget.create+1),∑ accept : Fin budget.accept,∑ bundle : Fin budget.bundle,
        Pr{let result←(game (n := n) setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          source ensureInit identityIndex serverKeyId bounds mode adversary previous identity.val bundle.val accept.val placeholder)}[
            RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint identity.val result] := by
  apply (RegistrationNativeIdentityIssuedOriginalFinite.cut_bound setup checks wire route representation view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded).trans
  apply Finset.sum_le_sum
  intro identity _identity
  apply Finset.sum_le_sum
  intro accept _accept
  apply Finset.sum_le_sum
  intro bundle _bundle
  exact bound setup checks route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget identity accept bundle placeholder

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized.conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized.conditional
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized.issued_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetainedInitialized.issued_bound
