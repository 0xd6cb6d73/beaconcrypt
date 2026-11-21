-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateNativeClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateChosen
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal
/-! The concrete late-key ordinary adversary samples the literal independent native startup internally. Its future identity keys are discovered solely from public protocol replies. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient
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
local notation "params" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation


noncomputable def code (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) :=
  RegistrationNativeIdentityTemplateCensorRecognition.packetProgram selected bundle accept placeholder
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation initial.created initial.credential view failure
      allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder)
    RegistrationNativeIdentityTemplateNativeClient.defaults
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
    (RegistrationNativeIdentityMainProfile.fromInitial initial,previous) [PqxdhRefinement.absBytes initial.credential.publicKey]

def publicBefore (initial : RegistrationNativeExperiment.Initial n KemSK source) : RegistrationNativeIdentityTemplatePolicy.Public :=
  ({},RegistrationNativeIdentityTemplatePublicCtx.install (RegistrationNativeWorldCache.cache initial.state,
    [PqxdhRefinement.absBytes initial.credential.publicKey]))

noncomputable def conditional {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery)
    (initialized : Option (RegistrationNativeExperiment.Initial n KemSK source)) :=
  match initialized with
  | none => fun (_identity : PqxdhJointIdentity.PublicIdentity) => (pure fallback : OracleComp PqxdhJointIdentity.AdversarySpec _)
  | some initial => RegistrationNativeIdentityTemplateLateChosen.reduction setup.joint target
      (code setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        source bounds mode adversary previous target.val bundle accept placeholder initial)
      RegistrationNativeIdentityTemplatePublicRegistry.empty (publicBefore source initial) fallback

noncomputable def reduction {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :=
  RegistrationNativeIdentityCensorChosenReduction.sampled
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
    (conditional setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous target bundle accept placeholder fallback)

noncomputable def observed {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial => do
      let result ← RegistrationNativeIdentityTemplateLateFamily.run setup.joint (count+1) target.val
        (code setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          source bounds mode adversary previous target.val bundle accept placeholder initial)
        RegistrationNativeIdentityTemplatePublicRegistry.empty (publicBefore source initial)
      pure (PqxdhJointIdentity.wins setup.joint (PqxdhJointIdentityFamily.familyPublic setup.joint result.1 target)
        ((result.2.1.1.map Prod.snd).getD fallback) (result.2.2.2.histories target))

/-- The actual normalized native source discharges the late client's no-reveal syntax internally. -/
theorem code_safe (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    (code setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous selected bundle accept placeholder initial).AllQueriesSatisfy
        RegistrationNativeIdentityTemplateChosenSource.TemplateAllowed := by
  exact RegistrationNativeIdentityTemplateVisitorNoReveal.visit setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle placeholder accept RegistrationNativeIdentityTemplateNativeClient.defaults
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
    (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
      ({knownInputs := [PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0)

/-- Every original raw mode supplies the actual create cap used to reserve the late client's family. -/
theorem code_create_bound (selected bundle accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget (adversary initial.public)) :
    (code setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source bounds mode adversary previous selected bundle accept placeholder initial).IsQueryBoundP
        RegistrationNativeIdentityTemplateCreateCounts.TargetCreate (budget.cap 1) := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
    (adversary initial.public) budget bounded 1
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact RegistrationNativeIdentityTemplateVisitorCreateBounds.visit setup checks wire route representation initial.created initial.credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected bundle placeholder accept RegistrationNativeIdentityTemplateNativeClient.defaults
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public)) (budget.cap 1) bill
    (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),
      ({knownInputs := [PqxdhRefinement.absBytes initial.credential.publicKey]} : RegistrationNativeIdentityCensorCompiler.Mode)),0)

/-- The actual late-key native client has one ordinary joint weak-EUF bill, with independent native startup and all auxiliary keys sampled inside E. -/
theorem bound {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (observed (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous target bundle accept placeholder fallback)}[result = true] ≤
    PqxdhJointIdentity.advantage setup.joint
      (reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        source ensureInit identityIndex serverKeyId bounds mode adversary previous target bundle accept placeholder fallback) := by
  unfold reduction
  rw [←RegistrationNativeIdentityCensorChosenReduction.sampled_advantage]
  unfold observed
  apply prEvent_bind_mono_of_forall_le
  intro initialized
  cases initialized with
  | none =>
    simp only [prEvent_pure,Bool.false_eq_true,ite_false]
    exact zero_le
  | some initial =>
    have same := RegistrationNativeIdentityTemplateLateChosen.probability_eq setup.joint target
      (code setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        source bounds mode adversary previous target.val bundle accept placeholder initial)
      (code_safe setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        source bounds mode adversary previous target.val bundle accept placeholder initial)
      RegistrationNativeIdentityTemplatePublicRegistry.empty (publicBefore source initial) fallback
    simpa only [conditional,bind_pure_comp,prEvent_map,PqxdhJointIdentity.advantage] using le_of_eq same

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient.code_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient.code_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient.code_create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient.code_create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateNativeClient.bound
