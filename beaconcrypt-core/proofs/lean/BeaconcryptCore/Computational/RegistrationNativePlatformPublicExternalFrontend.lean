-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendRequestBounds
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend
open BeaconcryptCore.Refinement
open RegistrationNativePlatformEffectCompiler (Spec effect)
open RegistrationNativePlatformPublicExternalBuild (IsExternal)
variable {n : Nat} {E Platform A B S : Type}
private def Bounded (work : StateT S (OracleComp (Spec n)) A) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsExternal cap
private theorem pure_bound (value : A) (cap : Nat) :
    Bounded (pure value : StateT S (OracleComp (Spec n)) A) cap := by
  intro before
  trivial
private theorem bind_bound (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (firstCap laterCap : Nat)
    (first : Bounded work firstCap) (later : ∀ value, Bounded (next value) laterCap) :
    Bounded (work >>= next) (firstCap + laterCap) := by
  intro before
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (first before) (fun result _ => later result.1 result.2)
private theorem bind_tail_zero (work : StateT S (OracleComp (Spec n)) A)
    (next : A → StateT S (OracleComp (Spec n)) B) (cap : Nat)
    (first : Bounded work cap) (later : ∀ value, Bounded (next value) 0) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.add_zero] using bind_bound work next cap 0 first later
private theorem effect_program_zero (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    Bounded (simulateQ (effect (Platform := S)) work) 0 := by
  intro before
  apply (isQueryBoundP_false work 0).simulateQ_run_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _ current
    simp [effect, StateT.run_lift, IsExternal, isQueryBoundP_query_iff]
variable [primitive : AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (byteCap packetCap : Nat)
variable (bytesBound : ∀ amount before, ((reserveBytes amount).run before).IsTotalQueryBound byteCap)
variable (packetsBound : ∀ amount before, ((reservePackets amount).run before).IsTotalQueryBound packetCap)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (erased : commitment.CommitmentTranscript)
local notation "allocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "pairTarget" => RegistrationNativePlatformPairedServerCompiler.target (n := n) source view failure allocation erased helper sign writer
private theorem paired_forward_zero (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    Bounded (simulateQ (pairTarget initial output) (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work)) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : (pairTarget initial output) ∘ₛ RegistrationNativePlatformPairedServerCompiler.forward = effect := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformPairedServerCompiler.forward,
      simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.target]
  rw [leaves]
  exact effect_program_zero work
include bytesBound packetsBound in
private theorem paired_known (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded (simulateQ (pairTarget initial output) (RegistrationNativePlatformPairedServerCompiler.known (n := n) control))
      (4 * byteCap + 3 * packetCap) := by
  unfold RegistrationNativePlatformPairedServerCompiler.known
  simp only [simulateQ_bind, simulateQ_spec_query]
  exact bind_tail_zero _ _ _
    (RegistrationNativePlatformPublicExternalBuild.bound_publication source view failure reserveBytes reservePackets byteCap packetCap bytesBound packetsBound sign erased initial output)
    (fun _ => paired_forward_zero source view failure reserveBytes reservePackets sign erased initial output _)
include bytesBound packetsBound in
private theorem paired_hidden (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    Bounded (simulateQ (pairTarget initial output) (RegistrationNativePlatformPairedServerCompiler.hidden control slot))
      (4 * byteCap + 3 * packetCap) := by
  unfold RegistrationNativePlatformPairedServerCompiler.hidden
  simp only [simulateQ_bind, simulateQ_spec_query]
  exact bind_tail_zero _ _ _
    (RegistrationNativePlatformPublicExternalBuild.bound_publication source view failure reserveBytes reservePackets byteCap packetCap bytesBound packetsBound sign erased initial output)
    (fun _ => paired_forward_zero source view failure reserveBytes reservePackets sign erased initial output _)
include bytesBound packetsBound in
/-- Both actual material-reply branches keep the same explicit source reservation bill, including failed publication and installation. -/
theorem branch_bound (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) :
    Bounded (RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice)
      (4 * byteCap + 3 * packetCap) := by
  cases choice with
  | known output => exact paired_known source view failure reserveBytes reservePackets byteCap packetCap bytesBound packetsBound sign erased control initial output
  | hidden reference => exact paired_hidden source view failure reserveBytes reservePackets byteCap packetCap bytesBound packetsBound sign erased control reference.slot initial _

variable {KemSK : Type}
omit primitive in
private def effectsToLocal : QueryImpl (Spec n) (OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK)) :=
  RegistrationNativePlatformPublicFrontend.buildEmbedding ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed
omit primitive in
private theorem effects_to_local_bound (work : OracleComp (Spec n) A) (cap : Nat)
    (bounded : work.IsQueryBoundP IsExternal cap) :
    (simulateQ (effectsToLocal (KemSK := KemSK)) work).IsQueryBoundP
      (RegistrationNativePlatformPublicExternalLocal.IsLocalExternal (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ IsExternal _ _ cap bounded
  intro query
  cases query with
  | inl query =>
    simpa only [effectsToLocal, QueryImpl.apply_compose, RegistrationNativePlatformServerFrontendCompiler.embed,
      simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.buildEmbedding,
      RegistrationNativePlatformPublicFrontend.effect, IsExternal, ite_false] using
      RegistrationNativePlatformPublicExternalLocal.local_zero false
        (((RegistrationBeaconReferenceCompiler.Spec n KemSK).query (.inr (.inl (.inr (.inr query)))) ) : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) _)
  | inr coin =>
    simp [effectsToLocal, QueryImpl.apply_compose, RegistrationNativePlatformServerFrontendCompiler.embed,
      RegistrationNativePlatformPublicFrontend.buildEmbedding,
      RegistrationNativePlatformPublicFrontend.localCoin, IsExternal,
      RegistrationNativePlatformPublicExternalLocal.IsLocalExternal, isQueryBoundP_query_iff]
omit primitive in
private theorem lifted_effects_bound (work : StateT (RegistrationNativePlatformBoundCompiler.PublicState Platform) (OracleComp (Spec n)) A)
    (cap : Nat) (bounded : Bounded work cap) (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    (simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.liftEffects work).run before)).IsQueryBoundP
        (RegistrationNativePlatformPublicExternalLocal.IsLocalExternal (KemSK := KemSK)) cap := by
  unfold RegistrationNativePlatformServerFrontendCompiler.liftEffects StateT.run
  rw [← QueryImpl.simulateQ_compose]
  exact effects_to_local_bound (work.run before) cap (bounded before)
omit primitive in
private theorem pin_zero (current : session.ServerAuthenticationPin) :
    Bounded (RegistrationNativePlatformServerRestrictedService.pin (n := n) (Platform := Platform) current) 0 := by
  unfold RegistrationNativePlatformServerRestrictedService.pin
  apply bind_tail_zero _ _ 0
  · intro before
    simp [effect, StateT.run_lift, IsExternal, isQueryBoundP_query_iff]
  · intro reply
    exact pure_bound _ 0

include bytesBound packetsBound in
private theorem target_bound (reservePeer : StateT Platform ProbComp Bool) (peerCap : Nat)
    (peerBound : ∀ before, (reservePeer.run before).IsTotalQueryBound peerCap)
    (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    (((RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK)).mapStateTBase
      (RegistrationNativePlatformServerFrontendCompiler.target (n := n) source view failure allocation erased helper sign writer reservePeer) query).run before).IsQueryBoundP
        (RegistrationNativePlatformPublicExternalLocal.IsLocalExternal (KemSK := KemSK))
          (peerCap + (4 * byteCap + 3 * packetCap)) := by
  change (simulateQ (RegistrationNativePlatformPublicFrontend.buildEmbedding (KemSK := KemSK))
    ((RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reservePeer query).run before)).IsQueryBoundP _ _
  cases query with
  | pin current => exact (lifted_effects_bound _ 0 (pin_zero current) before).mono (Nat.zero_le _)
  | reserve =>
    have reserved : Bounded (RegistrationNativePlatformBoundCompiler.liftPlatform
        (RegistrationNativePlatformEffectCompiler.compile (n := n) reservePeer)) peerCap := by
      intro current
      simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicExternalBuild.compile_bound reservePeer peerCap peerBound current.2
    exact (lifted_effects_bound _ peerCap reserved before).mono (Nat.le_add_right _ _)
  | present keyId =>
    have present : Bounded (effect (n := n) (Platform := RegistrationNativePlatformBoundCompiler.PublicState Platform) (.inr (.peerPresent keyId))) 0 := by
      intro current
      simp [effect, StateT.run_lift, IsExternal, isQueryBoundP_query_iff]
    exact (lifted_effects_bound _ 0 present before).mono (Nat.zero_le _)
  | service control initial message =>
    simp only [RegistrationNativePlatformServerFrontendCompiler.target,
      RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind, StateT.run_lift,
      simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.buildEmbedding,
      RegistrationNativePlatformPublicFrontend.localQuery, bind_assoc, pure_bind]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [RegistrationNativePlatformPublicExternalLocal.IsLocalExternal], ?_⟩
    intro selected
    cases selected with
    | none => trivial
    | some choice =>
      exact (lifted_effects_bound _ (4 * byteCap + 3 * packetCap)
        (branch_bound source view failure reserveBytes reservePackets byteCap packetCap bytesBound packetsBound sign erased control initial choice) before).mono (Nat.le_add_left _ _)

variable {I : Type} {base : OracleSpec I}
include bytesBound packetsBound in
/-- The literal corrected public Server build has an explicit conservative external budget from its four frontend leaves and individual capacity/peer samplers. It retains one-use cancellation, failure histories and the entire reached platform state. -/
theorem build_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (reservePeer : StateT Platform ProbComp Bool) (peerCap : Nat)
    (peerBound : ∀ before, (reservePeer.run before).IsTotalQueryBound peerCap)
    (handle : Nat) (application : Option (Slice U8)) (identitySource : RegistrationNativeMldsa.Source)
    (before : RegistrationNativePlatformPublicFrontend.State identitySource Platform) :
    ((RegistrationNativePlatformPublicFrontend.build (n := n) setup sign view failure allocation erased helper writer reservePeer handle application identitySource).run before).IsQueryBoundP
      (RegistrationNativePlatformPublicExternalLocal.IsLocalExternal (KemSK := KemSK))
        (4 * (peerCap + (4 * byteCap + 3 * packetCap))) := by
  simp only [RegistrationNativePlatformPublicFrontend.build, StateT.run, isQueryBoundP_map_iff]
  have freeBound := RegistrationNativePlatformPublicExternalBuild.simulate_scaled
    (RegistrationNativePlatformPublicExternalLocal.IsLocalExternal (n := n) (KemSK := KemSK))
    ((RegistrationNativePlatformPublicFrontend.buildEmbedding (n := n) (KemSK := KemSK)).mapStateTBase
      (RegistrationNativePlatformServerFrontendCompiler.target setup.source view failure allocation erased helper sign writer reservePeer))
    (peerCap + (4 * byteCap + 3 * packetCap))
    (target_bound (n := n) (KemSK := KemSK) setup.source view failure reserveBytes reservePackets byteCap packetCap bytesBound packetsBound sign erased reservePeer peerCap peerBound)
    ((RegistrationNativePlatformServerFrontendProgram.program handle application).run before.1.server)
    4 (RegistrationNativePlatformServerFrontendRequestBounds.program handle application before.1.server)
    (before.1.environment.receipts, before.2)
  rw [← QueryImpl.simulateQ_mapStateTBase_run] at freeBound
  exact freeBound
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend.branch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend.branch_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalFrontend.build_bound
