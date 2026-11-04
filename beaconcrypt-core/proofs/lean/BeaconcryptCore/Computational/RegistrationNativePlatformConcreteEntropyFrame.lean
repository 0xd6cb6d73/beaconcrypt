-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame
import BeaconcryptCore.Computational.RegistrationNativeEntropyFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
import BeaconcryptCore.Computational.FinitePartitionQueryBounds
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftBudget (WorldEffect)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePlatformPublicExternalCaps (Caps)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
variable {n : Nat} {E Platform I KemSK ProviderState A : Type} {base : OracleSpec I}
open RegistrationNativePlatformConcreteWorldFrame (cost)
open PqxdhRecordLiftInterface (EnvEffects effectKind effectLift)
def allowance (qGenerate qSign qKem : Nat) (caps : Caps) (tag : Fin 14) (kind : EffectKind) :=
  if small : tag.val < 12 then cost qGenerate qSign qKem caps kind ⟨tag.val, small⟩ else 0

private theorem effect_lift_iff (work : OracleComp (EnvEffects n) A) (kind : EffectKind) (cap : Nat) :
    (simulateQ effectLift work).IsQueryBoundP (WorldEffect kind) cap ↔
      work.IsQueryBoundP (fun query => effectKind query = kind) cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => constructor <;> intro _ <;> trivial
  | query_bind query next ih =>
      simp only [simulateQ_query_bind, effectLift, OracleQuery.input_query, monadLift_self, isQueryBoundP_query_bind_iff, WorldEffect, ih, OracleQuery.cont_query, id_eq]
      rfl

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
variable (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
variable (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
variable (selectedOwner selectedAccept : Nat)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript) (qGenerate qSign qKem : Nat) (caps : Caps)
variable (generation : source.generate.IsTotalQueryBound qGenerate)
variable (signing : ∀ key request, (source.sign key request).IsTotalQueryBound qSign)
variable (kem : ∀ query before, ((provider query).run before).IsTotalQueryBound qKem)
variable (registrationBound : ∀ before, (reserveRegistration.run before).IsTotalQueryBound caps.registration)
variable (peerBound : ∀ before, (reservePeer.run before).IsTotalQueryBound caps.peer)
variable (bytesBound : ∀ amount before, ((reserveBytes amount).run before).IsTotalQueryBound caps.bytes)
variable (packetsBound : ∀ amount before, ((reservePackets amount).run before).IsTotalQueryBound caps.packet)
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "owned" => RegistrationNativeMldsa.owned source credential
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "callback" => RegistrationNativePlatformPublicFrontend.handler (n := n) setup checks canonical source owned
  selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer
local notation "actual" => RegistrationNativePlatformSelectiveEntropyExecution.handler (n := n) setup checks wire source credential
  seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer

include generation signing kem registrationBound peerBound bytesBound packetsBound in
/-- The real raw adapter performs at most its one typed callback, so the complete concrete World bill has exactly the raw command's cost-table entry. -/
theorem raw_bound (query : RegistrationNativeInterface.Spec.Domain)
    (before : State n KemSK ProviderState Platform source) (kind : EffectKind) :
    ((simulateQ actual (RegistrationNativeRawAdapter.adapter canonical query)).run before).IsQueryBoundP (WorldEffect kind)
      (cost qGenerate qSign qKem caps kind (RegistrationNativeLedgerCaps.coreKind query)) := by
  have bounded := RegistrationNativePlatformConcreteWorldFrame.program_bound setup checks wire source credential seed scalar candidate provider
    selectedOwner selectedAccept view failure reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps
    generation signing kem registrationBound peerBound bytesBound packetsBound
    (RegistrationNativeRawAdapter.adapter canonical query)
    (fun tag => if RegistrationNativeLedgerCaps.coreKind query = tag then 1 else 0)
    (fun tag => RegistrationNativeRawAdapter.query_bound canonical query tag) before kind
  simpa using bounded
include generation signing kem registrationBound peerBound bytesBound packetsBound in
/-- Every actual corrected restricted-environment callback has its derived concrete bill, retaining all source/private/platform failure poststates. -/
theorem step_bound (query : RegistrationNativeEntropyInterface.EnvQuery)
    (before : State n KemSK ProviderState Platform source) (kind : EffectKind) :
    ((RegistrationNativePlatformSelectiveEntropyEnvironment.step setup checks canonical source credential seed scalar candidate provider
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer query).run before).IsQueryBoundP
      (fun effect => effectKind effect = kind)
      (allowance qGenerate qSign qKem caps (RegistrationNativeInterface.queryClass (.inl (.inr query.val))) kind) := by
  apply (effect_lift_iff _ kind _).mp
  rw [RegistrationNativePlatformSelectiveEntropyEnvironment.step_source]
  rw [isQueryBoundP_map_iff]
  have complete := raw_bound setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure
    reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps generation signing kem
    registrationBound peerBound bytesBound packetsBound (.inr query.val) before kind
  have whole := simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativePlatformSelectiveEntropyBackend.handler setup canonical owned seed scalar candidate provider)
    callback (RegistrationNativeRawAdapter.adapter canonical (.inr query.val)) before.1 before.2
  have transported := congrArg (fun work => work.IsQueryBoundP (WorldEffect kind)
      (cost qGenerate qSign qKem caps kind (RegistrationNativeLedgerCaps.coreKind (.inr query.val)))) whole
  have first : (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup canonical owned seed scalar candidate provider)
      ((RegistrationNativePlatformPublicFrontendCaps.raw setup checks canonical source owned selectedOwner selectedAccept
        (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer (.inr query.val)).run before.1)).run before.2
      |>.IsQueryBoundP (WorldEffect kind) (cost qGenerate qSign qKem caps kind (RegistrationNativeLedgerCaps.coreKind (.inr query.val))) := by
    simpa only [RegistrationNativePlatformPublicFrontendCaps.raw, QueryImpl.apply_compose, RegistrationNativePlatformSelectiveEntropyExecution.handler,
      isQueryBoundP_map_iff] using (transported.mpr (by simpa only [isQueryBoundP_map_iff, RegistrationNativePlatformSelectiveEntropyExecution.handler] using complete))
  have same := RegistrationNativeLedgerCaps.core_class (.inr query.val)
  have small : (RegistrationNativeInterface.queryClass (.inl (.inr query.val))).val < 12 := by
    rw [same]
    exact (RegistrationNativeLedgerCaps.coreKind (.inr query.val)).isLt
  have classes : allowance qGenerate qSign qKem caps (RegistrationNativeInterface.queryClass (.inl (.inr query.val))) kind =
      cost qGenerate qSign qKem caps kind (RegistrationNativeLedgerCaps.coreKind (.inr query.val)) := by
    unfold allowance
    rw [dite_eq_left small]
    congr 1
    exact Fin.ext same
  simpa only [classes] using first
include generation signing kem registrationBound peerBound bytesBound packetsBound in
/-- The environment Frame is constructed from individual actual callback bills and the separate startup draw receipt. -/
theorem frame (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState Platform source)))
    (startupCoins : Nat) (startupBound : startup.IsTotalQueryBound startupCoins) :
    RegistrationNativeEntropyFrame.Frame
      (RegistrationNativePlatformSelectiveEntropyEnvironment.environment setup checks canonical source credential seed scalar candidate provider
        selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer startup)
      startupCoins (allowance qGenerate qSign qKem caps) :=
  ⟨startupBound, fun query before kind => step_bound setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
    view failure reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps generation signing kem
    registrationBound peerBound bytesBound packetsBound query before kind⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame.raw_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame.step_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteEntropyFrame.frame
