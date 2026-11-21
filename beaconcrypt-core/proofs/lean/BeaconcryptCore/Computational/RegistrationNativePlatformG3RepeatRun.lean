-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3AliasAudit
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedWhole
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps
/-! The actual corrected all-mode source run has its guarded mark bounded by the repeated-role event of that same chronological run. The concrete source theorem supplies paired safety internally; the full returned ledger, frontend/P, provider and World state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeG3AuditTraceRun (cold)
variable {n : Nat} {I KemSK ProviderState Reader Response Platform E Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

/-- The actual selective World backend forwards the new external coin branch through the same physical coin request. -/
theorem backend :
    RegistrationNativeSelectiveHiddenInterpreter.handler (n := n) setup wire sign seed scalar candidate provider ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed =
      RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider := by
  funext query
  cases query with
  | inl query => simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicCoinEmbedding.embed,
      simulateQ_spec_query, RegistrationNativePlatformSelectiveEntropyBackend.handler]
  | inr coin =>
    funext before
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformPublicCoinEmbedding.embed,
      RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
      RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
      RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect,
      RegistrationNativePlatformSelectiveEntropyBackend.handler, StateT.run_lift, bind_pure_comp,
      PqxdhRecordLiftInterface.effectLift, Functor.map_map]
    rfl

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (front : RegistrationNativePlatformPublicFrontend.State source Platform)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (world : PqxdhRecordLiftWorld.State n)

local notation "actualTree" => RegistrationNativePlatformMaterializedWhole.tree (n := n) setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
local notation "actualWorld" => RegistrationNativePlatformMaterializedWhole.world setup wire sign seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front

/-- The embedded actual PF.run is exactly the literal current selective-entropy World runner, without an old callback identity or a counter erasure. -/
theorem world_source :
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider) actualTree).run frame = actualWorld frame := by
  simp only [RegistrationNativePlatformMaterializedWhole.tree, RegistrationNativePlatformMaterializedWhole.world,
    ← QueryImpl.simulateQ_compose, backend]

noncomputable def original := RegistrationNativeG3GuardedCoupling.audit setup codec route seeds (actualWorld (cold frame materials)) world
noncomputable def traced := RegistrationNativePlatformG3AliasAudit.traced setup codec route seeds (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider actualTree frame materials world
noncomputable def known := RegistrationNativePlatformG3AliasAudit.known setup codec route seeds (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider actualTree frame materials world

/-- The actual source audit has the generic same-tree audit form with its complete original state and replies. -/
theorem original_source :
    original setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame materials world =
      RegistrationNativePlatformG3AliasAudit.original setup codec route seeds (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider actualTree frame materials world := by
  unfold original RegistrationNativePlatformG3AliasAudit.original
  rw [world_source]

/-- All actual allocator/writer outcomes and original modes satisfy the same-run repeated-role audit bound, with paired safety derived from the corrected source bodies. -/
theorem mark_bound (unused : ∀ slot role, world.used slot role = false) :
    Pr{let result ← original setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame materials world}[result.2.2 = true] ≤
      Pr{let result ← known setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front frame materials world}[
        RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate) result.1.2.events] := by
  rw [original_source]
  exact RegistrationNativePlatformG3AliasAudit.mark_bound setup codec route seeds (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign seed scalar candidate provider actualTree frame materials world
    (RegistrationNativePlatformPublicPairedSafety.run setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front) unused

omit primitive in
private theorem demand_embedding {A : Type} (tree : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A)
    (cap : Nat) (bounded : tree.IsQueryBoundP (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) cap) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed tree).IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ tree cap bounded
  intro query
  cases query with
  | inl query =>
    simp only [RegistrationNativePlatformPublicCoinEmbedding.embed, isQueryBoundP_query_iff,
      RegistrationNativePlatformPublicMaterialCaps.IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand]
    intro counted
    simp only [counted, ite_true]
    decide
  | inr coin => simp [RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
      RegistrationNativePublicFrontend.liftLocal, RegistrationNativePlatformPublicMaterialCaps.IsDemand,
      RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]

/-- The actual embedded source tree derives qBuild+qFinish material requests from the original raw-mode budget, including failed reservations and writers. -/
theorem demand_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (actualTree).IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (n := n) (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  unfold RegistrationNativePlatformMaterializedWhole.tree
  exact demand_embedding _ _ (RegistrationNativePlatformPublicMaterialCaps.run_bound setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded front)
end BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.backend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.world_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.original_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.original_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.mark_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.mark_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.demand_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RepeatRun.demand_bound
