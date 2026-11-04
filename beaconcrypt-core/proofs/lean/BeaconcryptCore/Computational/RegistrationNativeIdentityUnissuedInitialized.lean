-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedEvents
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamily
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! One genuine initialized source run supplies the same eagerly sampled identity family and unchanged observed call journal for the finite unissued-field union. All startup failures, warm cache, source/P state and future-created aliases are retained. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
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
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)

abbrev Front (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeIdentityMain.State n KemSK source × Platform
abbrev Observed (n : Nat) (KemSK Platform Value : Type) (source : RegistrationNativeMldsa.Source) :=
  (Value × RegistrationNativeLedger.State) ×
    ((Front n KemSK Platform source × RegistrationNativePlatformIdentityCtxSigningLog.Trace) ×
      List (RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec
        (Front n KemSK Platform source × RegistrationNativePlatformIdentityCtxSigningLog.Trace)))
abbrev Result (count n : Nat) (KemSK Platform Value : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformIdentityCtxFamily.Result count (Observed n KemSK Platform Value source)

noncomputable def tree (initial : RegistrationNativeExperiment.Initial n KemSK source) :=
  (simulateQ (RegistrationNativeObservedStageTrace.handler id
    (RegistrationNativePlatformIdentityCtxSigningTrace.wrap
      (RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)))
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      initial.created.server.server.metadata.sender bounds mode (adversary initial.public))).run
      (((RegistrationNativeIdentityMainProfile.fromInitial initial,previous),{}),[])

noncomputable def game (budget : PqxdhDeploymentInterface.Budget) :
    ProbComp (Option (Result (budget.create+1) n KemSK Platform Value source)) := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initialized with
  | none => pure none
  | some initial =>
      some <$> RegistrationNativePlatformIdentityCtxFamily.run setup.joint (budget.create+1)
        (tree setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source bounds mode adversary previous initial)
        (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])

def At (budget : PqxdhDeploymentInterface.Budget) (identity : Fin (budget.create+1)) (accept : Fin budget.accept) (tag : Fin 3)
    (result : Option (Result (budget.create+1) n KemSK Platform Value source)) : Prop :=
  result.elim False (fun result => RegistrationNativeIdentityUnissuedEvents.At setup.joint
    (PqxdhJointIdentityFamily.familyPublic setup.joint result.1) identity accept.val tag result.2.1.1)

def Any (budget : PqxdhDeploymentInterface.Budget)
    (result : Option (Result (budget.create+1) n KemSK Platform Value source)) : Prop :=
  ∃ identity : Fin (budget.create+1), ∃ accept : Fin budget.accept, ∃ tag : Fin 3,
    At setup source budget identity accept tag result

noncomputable def loss (budget : PqxdhDeploymentInterface.Budget) (fallback : PqxdhJointIdentity.Forgery) : ℝ≥0∞ :=
  ∑ identity : Fin (budget.create+1), ∑ accept : Fin budget.accept, ∑ tag : Fin 3,
    PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativeIdentityUnissuedNativeClient.reduction (n := n) (count := budget.create)
        setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous identity accept.val tag fallback)

/-- The genuine initialized source run has exactly the finite identity/accept/field union on that same unchanged distribution. -/
theorem finite_union (budget : PqxdhDeploymentInterface.Budget) :
    Pr{let result ← (game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget)}[Any setup source budget result] ≤
      ∑ identity : Fin (budget.create+1), ∑ accept : Fin budget.accept, ∑ tag : Fin 3,
        Pr{let result ← (game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous budget)}[At setup source budget identity accept tag result] := by
  let work := game (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget
  have identities := prEvent_exists_le work (fun identity : Fin (budget.create+1) => fun result =>
    ∃ accept : Fin budget.accept, ∃ tag : Fin 3, At setup source budget identity accept tag result)
  apply identities.trans
  apply Finset.sum_le_sum
  intro identity _identity
  have positions := prEvent_exists_le work (fun accept : Fin budget.accept => fun result =>
    ∃ tag : Fin 3, At setup source budget identity accept tag result)
  apply positions.trans
  exact Finset.sum_le_sum (fun accept _accept => prEvent_exists_le work
    (fun tag : Fin 3 => fun result => At setup source budget identity accept tag result))

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized.finite_union' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedInitialized.finite_union
