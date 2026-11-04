-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishHashBounds
import BeaconcryptCore.Computational.FinitePartitionQueryBounds
/-! Concrete physical shared-hash budgets for every actual current-runtime typed callback and the original full public command compiler. These bounds retain all optional failures, native/P poststates and all-reply adaptive continuations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxHashBoundsCore (Bounded ContextBounded ordinary_bound)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "ambient" => RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

def cost (kind : Fin 12) : Nat :=
  match kind.val with
  | 0 | 6 => 0
  | 1 => 1
  | 2 | 5 => 2
  | 3 => 4
  | 4 => 10
  | _ => 1

omit primitives in
/-- The finite weighted API bill exposes every command multiplicity and charges no public coins or HMAC as shared hashes. -/
theorem bill_eq (budget : Fin 12 → Nat) :
    (∑ kind, cost kind * budget kind) =
      budget 1 + 2 * budget 2 + 4 * budget 3 + 10 * budget 4 + 2 * budget 5 +
        budget 7 + budget 8 + budget 9 + budget 10 + budget 11 := by
  simp [Fin.sum_univ_succ, cost, Nat.add_assoc]

omit primitives in
/-- The complete corrected assigned-ID finish has its one response and one first-record hash. -/
theorem finish_bound (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded (RegistrationNativePlatformIdentityCtxLifecycle.finish (n := n) setup checks representation created
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source _) 2 :=
  RegistrationNativePlatformIdentityCtxFrontendHashBounds.beacon_bound setup checks representation created _ 2
    (RegistrationNativePlatformIdentitySourceHashBounds.native_bound _ 2
      (RegistrationNativePlatformIdentityFinishHashBounds.finish_bound setup _ index packet))

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step

/-- Every literal typed callback has its concrete physical shared hash bill on every outcome. -/
theorem handler_bound (query : TypedSpec.Domain) : Bounded (callback query) (cost (RegistrationNativeRawAdapter.kind query)) := by
  cases query with
  | inl coin => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin)
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxLifecycleHashBounds.create_bound setup checks representation created edPin mlPin keyId
    | bundle index => exact RegistrationNativePlatformIdentityCtxLifecycleHashBounds.bundle_bound setup checks representation created writer index
    | finish index packet => exact finish_bound setup checks wire representation created index packet
    | accept packet =>
        unfold RegistrationNativePlatformIdentityCtxTyped.handler
        exact RegistrationNativePlatformIdentityCtxHashBoundsCore.bind_bound _ _ 0 4
          (RegistrationNativePlatformIdentityCtxLifecycleHashBounds.report_bound packet)
          (fun _ => RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)))
    | build session application => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build session application))
    | hmac key message => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message))
    | hash bytes => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes))
    | serverSend keyId plaintext => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw))
    | beaconSend index plaintext => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext))
    | beaconRaw index raw => exact RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw))

/-- Separate public API caps yield one shared weighted physical-hash allowance through every adaptive reply. -/
theorem program_bound {A : Type} (work : OracleComp TypedSpec A) (budget : Fin 12 → Nat)
    (bounded : ∀ kind, work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = kind) (budget kind)) :
    Bounded (simulateQ callback work) (∑ kind, cost kind * budget kind) := by
  intro before
  exact FinitePartitionQueryBounds.weighted_bound RegistrationNativeRawAdapter.kind cost budget callback
    RegistrationNativePlatformIdentityCtxBackend.IsHash work bounded
    (handler_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) before

/-- The original full public compiler's derived typed caps instantiate the same concrete physical resource bill. -/
theorem raw_bound {A : Type} (serverKeyId : U64) (fresh : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) :
    Bounded (simulateQ callback (RegistrationNativeFullCompiler.compile setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId fresh mode work))
      (∑ kind, cost kind * (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost fresh kind full * budget.cap full)) :=
  program_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ _
    (RegistrationNativeFullCompiler.compile_bound setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId fresh mode work budget bounded)
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.bill_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.bill_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.finish_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHashBounds.raw_bound
