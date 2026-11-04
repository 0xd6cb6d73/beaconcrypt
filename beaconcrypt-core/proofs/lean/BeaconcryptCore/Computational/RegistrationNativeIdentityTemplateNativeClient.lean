-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The actual issued-message ordinary adversary samples the independent native startup and other reserved identities inside E. It then runs the original raw adversary and actual normalized frontend with fixed public bundle/accept ordinals and the seed-free template/recognition compiler. The challenged identity seed and canonical hidden signature remain solely in the primitive/source interpreters. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateNativeClient
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


/-- Public no-effect replies used only after the before-accept stop. -/
def defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query
  | .inl coin => (0 : Fin (coin+1))
  | .inr (.create _ _ _) => .ok none
  | .inr (.bundle _) => .ok none
  | .inr (.accept _) => .ok none
  | .inr (.build _ _) => .ok none
  | .inr (.finish _ _) => .ok none
  | .inr (.hmac _ _) => PqxdhSecretInputKdf.zeroSalt
  | .inr (.hash _) => List.Vector.replicate 64 0
  | .inr (.serverSend _ _) => none
  | .inr (.serverRaw _) => .None
  | .inr (.beaconSend _ _) => none
  | .inr (.beaconRaw _ _) => .None

def initialCache (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    RegistrationNativeIdentityTemplateCensorRecognition.Cache :=
  (RegistrationNativeIdentityTemplatePublicCtx.install (RegistrationNativeWorldCache.cache initial.state,
    [PqxdhRefinement.absBytes initial.credential.publicKey])).1

def initialAuxiliary (count : Nat) : RegistrationNativeIdentityChosenPublicRouter.Auxiliary count :=
  (PqxdhDynamicIdentityRouting.initialPublicState,PqxdhJointIdentityFamily.emptyHistory count)

noncomputable def client {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) : RegistrationNativeIdentityCensorChosenReduction.Client setup.joint count :=
  fun _others identity => RegistrationNativeIdentityTemplateCensorRecognition.packetClient setup.joint target.val bundle accept placeholder
    (RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation initial.created initial.credential view failure
      allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder) defaults
    (fun _publicIdentity => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
    (RegistrationNativeIdentityMainProfile.fromInitial initial,previous) [PqxdhRefinement.absBytes initial.credential.publicKey] identity

noncomputable def conditional {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery)
    (initialized : Option (RegistrationNativeExperiment.Initial n KemSK source)) :
    PqxdhJointIdentity.PublicIdentity → OracleComp PqxdhJointIdentity.AdversarySpec PqxdhJointIdentity.Forgery :=
  match initialized with
  | none => fun _identity => pure fallback
  | some initial => RegistrationNativeIdentityCensorChosenReduction.reduction setup.joint target placeholder fallback
      (client setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        source bounds mode adversary previous target bundle accept placeholder initial) (initialCache source initial) (initialAuxiliary count)

/-- Both independent startup and auxiliary family sampling occur in the executable ordinary adversary. No selected private seed, hidden signature, or physical hidden address is a constructor argument. -/
noncomputable def reduction {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    PqxdhJointIdentity.PublicIdentity → OracleComp PqxdhJointIdentity.AdversarySpec PqxdhJointIdentity.Forgery :=
  RegistrationNativeIdentityCensorChosenReduction.sampled
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
    (conditional setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve source
      bounds mode adversary previous target bundle accept placeholder fallback)

noncomputable def observed {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure false
  | some initial =>
      RegistrationNativeIdentityCensorChosenReduction.observed setup.joint target placeholder
        (client setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          source bounds mode adversary previous target bundle accept placeholder initial) (initialCache source initial) (initialAuxiliary count)

/-- This initialized actual client has one explicit ordinary joint weak-EUF bill for its fixed public i/a/b guesses. Startup refusal and every failed callback remain part of the experiment. Original causal-event inclusion is separate. -/
theorem bound {count : Nat} (target : Fin (count+1)) (bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let accepted ← (observed (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      source ensureInit identityIndex serverKeyId bounds mode adversary previous target bundle accept placeholder)}[accepted = true] ≤
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
    exact RegistrationNativeIdentityCensorChosenReduction.bound setup.joint target placeholder fallback
      (client setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        source bounds mode adversary previous target bundle accept placeholder initial) (initialCache source initial) (initialAuxiliary count)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateNativeClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateNativeClient.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateNativeClient.bound
