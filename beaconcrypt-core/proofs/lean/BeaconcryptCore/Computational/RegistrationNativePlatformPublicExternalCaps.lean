-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalRecords
import BeaconcryptCore.Computational.FinitePartitionQueryBounds
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicExternalLocal (IsExternal IsLocalExternal)
variable {n : Nat} {E Platform I KemSK A : Type} {base : OracleSpec I}
structure Caps where
  registration : Nat
  peer : Nat
  bytes : Nat
  packet : Nat

def cost (caps : Caps) (kind : Fin 12) : Nat :=
  match kind.val with
  | 2 => caps.packet
  | 3 => caps.registration
  | 4 => 4 * (caps.peer + (4 * caps.bytes + 3 * caps.packet))
  | 8 | 10 => caps.bytes
  | _ => 0

/-- Every external allowance has its concrete public API multiplicity, with conservative source syntax factors displayed for build. -/
theorem bill_eq (caps : Caps) (budget : Fin 12 → Nat) :
    (∑ kind, cost caps kind * budget kind) =
      caps.packet * budget 2 + caps.registration * budget 3 +
      4 * (caps.peer + (4 * caps.bytes + 3 * caps.packet)) * budget 4 +
      caps.bytes * budget 8 + caps.bytes * budget 10 := by
  simp [Fin.sum_univ_succ, cost, Nat.add_assoc]
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private def Bounded {source : RegistrationNativeMldsa.Source} (work : M n KemSK Platform source A) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP (IsExternal (KemSK := KemSK)) cap
private theorem execute_bound {source : RegistrationNativeMldsa.Source} (work : LocalM n KemSK Platform source A)
    (cap : Nat) (bounded : ∀ before, (work.run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap) :
    Bounded (executeLocal work) cap := by
  intro before
  exact RegistrationNativePlatformPublicExternalLocal.embed_bound _ cap (bounded before)
private theorem effect_zero {source : RegistrationNativeMldsa.Source} (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State source Platform) :
    (((StateT.lift (effect (KemSK := KemSK) query) : LocalM n KemSK Platform source _).run before)).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) 0 := by
  simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, effect]
  simpa only [simulateQ_spec_query] using RegistrationNativePlatformPublicExternalLocal.local_zero false
    (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query (.inr (.inl (.inr (.inr query)))) ) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _)

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript) (caps : Caps)
variable (registrationBound : ∀ before, (reserveRegistration.run before).IsTotalQueryBound caps.registration)
variable (peerBound : ∀ before, (reservePeer.run before).IsTotalQueryBound caps.peer)
variable (bytesBound : ∀ amount before, ((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
variable (packetsBound : ∀ amount before, ((reservePackets amount).run before).IsTotalQueryBound caps.packet)
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "callback" => handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer
include registrationBound peerBound bytesBound packetsBound in
/-- Every literal corrected callback has a derived external-coin bound from four individual public samplers. Source helper, seal and ordinary frame share one capacity-only reservation and persistent P. -/
theorem handler_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Bounded (callback query) (cost caps (RegistrationNativeRawAdapter.kind query)) := by
  cases query with
  | inl coin => exact execute_bound _ 0 (effect_zero (.inl coin))
  | inr query => cases query with
    | create edPin mlPin keyId =>
      apply execute_bound _ 0
      intro before
      simp only [beacon, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicExternalLocal.create_zero setup source selectedOwner publicPrekey edPin mlPin keyId _ _ _
    | bundle index =>
      apply execute_bound _ caps.packet
      intro before
      simp only [map_apply, isQueryBoundP_map_iff, beacon, StateT.run]
      exact RegistrationNativePlatformPublicExternalPublication.owner_bundle_bound setup reservePackets caps.packet packetsBound selectedOwner publicPrekey index _ _ _
    | accept packet =>
      apply execute_bound _ caps.registration
      intro before
      simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
      simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicExternalAccept.accept_bound (n := n) (KemSK := KemSK) (Platform := Platform)
        (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration setup checks source.verify packet caps.registration registrationBound
        before.1.server before.1.environment before.2
    | build handle application =>
      exact execute_bound _ _ (RegistrationNativePlatformPublicExternalFrontend.build_bound view failure reserveBytes reservePackets caps.bytes caps.packet bytesBound packetsBound sign erased setup reservePeer caps.peer peerBound handle application source)
    | finish index packet =>
      apply execute_bound _ 0
      intro before
      simp only [beacon, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicExternalLocal.finish_zero setup wire source index packet _ _ _
    | hmac key bytes =>
      intro before
      trivial
    | hash bytes => exact execute_bound _ 0 (effect_zero (.inr (.hash bytes)))
    | serverSend keyId plaintext =>
      intro before
      exact RegistrationNativePlatformPublicExternalRecords.record_bound reserveBytes (.inl (.inl (plaintext, keyId))) caps.bytes bytesBound before
    | serverRaw raw =>
      intro before
      exact RegistrationNativePlatformPublicExternalRecords.record_bound reserveBytes (.inl (.inr raw)) caps.bytes bytesBound before
    | beaconSend index plaintext =>
      intro before
      exact RegistrationNativePlatformPublicExternalRecords.record_bound reserveBytes (.inr (index, .inl plaintext)) caps.bytes bytesBound before
    | beaconRaw index raw =>
      intro before
      exact RegistrationNativePlatformPublicExternalRecords.record_bound reserveBytes (.inr (index, .inr raw)) caps.bytes bytesBound before

include registrationBound peerBound bytesBound packetsBound in
/-- Arbitrary adaptive typed executions use one explicit weighted public-site bill on all replies and reached states. -/
theorem program_bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (budget : Fin 12 → Nat)
    (bounded : ∀ kind, work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = kind) (budget kind)) :
    Bounded (simulateQ callback work) (∑ kind, cost caps kind * budget kind) := by
  intro before
  exact FinitePartitionQueryBounds.weighted_bound RegistrationNativeRawAdapter.kind (cost caps) budget callback
    (IsExternal (KemSK := KemSK)) work bounded
    (handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure reserveRegistration reservePeer reserveBytes reservePackets erased caps registrationBound peerBound bytesBound packetsBound) before
include registrationBound peerBound bytesBound packetsBound in
/-- The actual all-mode raw source frontend inherits these concrete external bills from its derived typed API budgets; neither a callback budget nor a whole Frame is assumed. -/
theorem run_bound (serverKeyId : U64) (fresh : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source Platform) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveBytes erased helper writer serverKeyId fresh mode work before).IsQueryBoundP
      (IsExternal (KemSK := KemSK))
      (∑ kind, cost caps kind * (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost fresh kind full * budget.cap full)) :=
  program_bound setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
    selectedOwner selectedAccept publicPrekey view failure reserveRegistration reservePeer reserveBytes reservePackets erased
    caps registrationBound peerBound bytesBound packetsBound _ _
    (RegistrationNativeFullCompiler.compile_bound setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId fresh mode work budget bounded) before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.bill_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.bill_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps.run_bound
