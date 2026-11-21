-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditMaterialized
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy

/-! The actual marked cold G3 repeat audit is bounded by the candidate-observed repeat event of the original native open-key client under its literal actual provider and lazy108-byte service. The same original ledger/frontend/chronological result passes through every source equation, and the original Respects supplies all demand and table-capacity bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditOpenKey
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Platform E Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
  (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
  (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
  (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
  (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
  (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
  (checks : Checks) (source : RegistrationNativeMldsa.Source)
  (selectedOwner selectedAccept : Nat)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativePlatformPublicFrontend.State source Platform)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

def Event {A : Type} (result : A × RegistrationNativeG2Trace.State) : Prop :=
  RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate) result.2.events

/-- The actual cold marked repeat audit transports to the same candidate-observed chronological event of the complete original open-key client, with no source, trace, readiness or capacity assumption. -/
theorem bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    {ProviderState : Type} (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (frame : RegistrationNativeHiddenInterpreter.State (budget.cap 4 + budget.cap 5) KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (unused : ∀ slot role, world.used slot role = false) :
    Pr{let marked ← (do
       let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable (budget.cap 4 + budget.cap 5)
       let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable (budget.cap 4 + budget.cap 5)
       let result ← (RegistrationNativePlatformG3RepeatRun.original setup (RegistrationNativeWire.ledgerCodec canonical) route seeds wire sign seed scalar candidate provider checks source
         selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front (frame, ∅)
         (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) world)
       pure result.2.2)}[marked = true] ≤
      Pr{let result ← ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
          (RegistrationNativeG3MaterializedRetainedLazy.client setup canonical route sign seed scalar
            (RegistrationNativeG2Trace.program
              (RegistrationNativePlatformMaterializedWhole.tree setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)) frame world)).run'
              (frame.pool, frame.provider))).run' ∅)}[Event setup seed scalar candidate result] := by
  classical
  let program := RegistrationNativeG2Trace.program
    (RegistrationNativePlatformMaterializedWhole.tree (n := budget.cap 4 + budget.cap 5) setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)
  have cap : program.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
    apply RegistrationNativeG2Trace.program_bound
    exact RegistrationNativePlatformG3RepeatRun.demand_bound setup wire sign scalar checks source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front budget bounded
  have law := RegistrationNativeG3MaterializedRetainedLazy.program_source setup canonical route sign seed scalar candidate provider program cap frame world
  have probability := (LazyOracleDiscard.LawEq.evalDist_eq (LazyOracleDiscard.LawEq.map
    (fun result => decide (Event setup seed scalar candidate result)) law))
  have eventEq := congrArg (fun distribution => distribution {true}) probability
  simp only [← prEvent_eq_evalDist_singleton, prEvent_map, decide_eq_true_eq] at eventEq
  rw [← eventEq]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun materials => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun seeds => ?_
  simpa only [program, RegistrationNativePlatformG3AuditMaterialized.full, StateT.run'_eq, Event, bind_pure_comp, prEvent_map] using
    RegistrationNativePlatformG3AuditMaterialized.mark_bound materials setup (RegistrationNativeWire.ledgerCodec canonical) route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front (frame, ∅) world unused

end BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditOpenKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditOpenKey.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3AuditOpenKey.bound
