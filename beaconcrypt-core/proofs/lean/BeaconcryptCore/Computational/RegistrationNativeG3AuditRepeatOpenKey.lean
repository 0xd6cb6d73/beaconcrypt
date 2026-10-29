-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy

/-! The actual marked cold G3 repeat audit is bounded by the candidate-observed repeat event of the original native open-key client under its literal actual provider and lazy108-byte service. The same original ledger/frontend/chronological result passes through every source equation, and the original Respects supplies all demand and table-capacity bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatOpenKey
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (checks : Checks) (source : RegistrationNativeMldsa.Source)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativePublicFrontend.State source)

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
       let result ← (RegistrationNativeG3AuditRepeatEvent.original setup (RegistrationNativeWire.ledgerCodec wire) route seeds wire sign seed scalar candidate provider checks source
         selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front (frame, ∅)
         (RegistrationNativeG3LocalMaterialCompletedSource.cache materials) world)
       pure result.2.2)}[marked = true] ≤
      Pr{let result ← ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
          (RegistrationNativeG3MaterializedRetainedLazy.client setup wire route sign seed scalar
            (RegistrationNativeG2Trace.program
              (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)) frame world)).run'
              (frame.pool, frame.provider))).run' ∅)}[Event setup seed scalar candidate result] := by
  classical
  let program := RegistrationNativeG2Trace.program
    (RegistrationNativePublicFrontend.run (n := budget.cap 4 + budget.cap 5) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)
  have cap : program.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
    apply RegistrationNativeG2Trace.program_bound
    exact RegistrationNativePublicCaps.run_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front
  have law := RegistrationNativeG3MaterializedRetainedLazy.program_source setup wire route sign seed scalar candidate provider program cap frame world
  have probability := (LazyOracleDiscard.LawEq.evalDist_eq (LazyOracleDiscard.LawEq.map
    (fun result => decide (Event setup seed scalar candidate result)) law))
  have eventEq := congrArg (fun distribution => distribution {true}) probability
  simp only [← prEvent_eq_evalDist_singleton, prEvent_map, decide_eq_true_eq] at eventEq
  rw [← eventEq]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun materials => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun seeds => ?_
  simpa only [program, RegistrationNativeG3AuditRepeatMaterialized.full, StateT.run'_eq, Event, bind_pure_comp, prEvent_map] using
    RegistrationNativeG3AuditRepeatMaterialized.mark_bound materials setup (RegistrationNativeWire.ledgerCodec wire) route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front (frame, ∅) world unused

end BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatOpenKey
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatOpenKey.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatOpenKey.bound
