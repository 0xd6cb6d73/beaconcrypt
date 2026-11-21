-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicNativeCaps
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftBudget (WorldEffect)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePlatformPublicExternalCaps (Caps)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
variable {n : Nat} {E Platform I KemSK ProviderState A : Type} {base : OracleSpec I}
def cost (qGenerate qSign qKem : Nat) (caps : Caps) (kind : EffectKind) (tag : Fin 12) :=
  RegistrationNativePlatformPublicNativeCaps.cost qGenerate qSign qKem kind tag +
    coinCost (RegistrationNativePlatformPublicExternalCaps.cost caps tag) kind
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
/-- Every actual corrected callback has its fully derived shared-World coin/hash/admin bill, using the concrete source capacity dictionary and narrow primitive sampler caps. -/
theorem handler_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK ProviderState Platform source) (kind : EffectKind) :
    ((actual query).run before).IsQueryBoundP (WorldEffect kind)
      (cost qGenerate qSign qKem caps kind (RegistrationNativeRawAdapter.kind query)) := by
  have signed := RegistrationNativePrimitiveCosts.signing_bound source qSign signing credential
  have native := RegistrationNativePlatformPublicNativeCaps.handler_bound (n := n) setup checks canonical source owned
    selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveBytes
    helper writer erased qGenerate qSign qKem generation signing signed query before.1 kind
  have external := RegistrationNativePlatformPublicExternalCaps.handler_bound (n := n) setup checks canonical source owned
    selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure reserveRegistration reservePeer reserveBytes reservePackets
    erased caps registrationBound peerBound bytesBound packetsBound query before.1
  have combined := RegistrationNativePlatformPublicWorldBills.combine_bound qSign qKem kind ((callback query).run before.1)
    _ _ native external
  have world := RegistrationNativePlatformPublicWorldBills.program_bound setup canonical owned seed scalar candidate provider
    qSign qKem signed kem ((callback query).run before.1) _ kind combined before.2
  rcases before with ⟨front, hidden⟩
  simpa only [cost, RegistrationNativePlatformSelectiveEntropyExecution.handler, QueryImpl.flattenStateT_mapStateTBase_apply_run,
    isQueryBoundP_map_iff] using world
include generation signing kem registrationBound peerBound bytesBound packetsBound in
/-- Adaptive typed API budgets close to concrete World effects on every reached source/platform/private state, without a caller Frame. -/
theorem program_bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (budget : Fin 12 → Nat)
    (bounded : ∀ tag, work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = tag) (budget tag))
    (before : State n KemSK ProviderState Platform source) (kind : EffectKind) :
    ((simulateQ actual work).run before).IsQueryBoundP (WorldEffect kind)
      (∑ tag, cost qGenerate qSign qKem caps kind tag * budget tag) :=
  FinitePartitionQueryBounds.weighted_bound RegistrationNativeRawAdapter.kind (cost qGenerate qSign qKem caps kind) budget actual
    (WorldEffect kind) work bounded
    (fun query current => handler_bound setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
      view failure reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps
      generation signing kem registrationBound peerBound bytesBound packetsBound query current kind) before
include generation signing kem registrationBound peerBound bytesBound packetsBound in
/-- The complete all-mode raw source compiler has its explicit concrete shared-World resource bill, with the original full ledger and every failed operation retained. -/
theorem run_bound (serverKeyId : U64) (fresh : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (before : State n KemSK ProviderState Platform source) (kind : EffectKind) :
    (RegistrationNativePlatformSelectiveEntropyExecution.run setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveBytes erased helper writer
      serverKeyId fresh mode work before).IsQueryBoundP (WorldEffect kind)
      (∑ tag, cost qGenerate qSign qKem caps kind tag *
        (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost fresh tag full * budget.cap full)) :=
  program_bound setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure
    reserveRegistration reservePeer reserveBytes reservePackets erased qGenerate qSign qKem caps
    generation signing kem registrationBound peerBound bytesBound packetsBound _ _
    (RegistrationNativeFullCompiler.compile_bound setup.source.crypto canonical serverKeyId fresh mode work budget bounded) before kind
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteWorldFrame.run_bound
