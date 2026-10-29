-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatEvent
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedProgram
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedProtocol

/-! The actual marked G3 repeat event transports to the actual complete known108-byte frontend through its literal original G2 chronology. The finite paired source equations preserve that chronology jointly with the original full ledger, so only private World and key-service bookkeeping is erased. The actual startup World and completed material cache remain explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditTraceRun (cold)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
  (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (checks : Checks) (source : RegistrationNativeMldsa.Source)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativePublicFrontend.State source)
  (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
  (world : PqxdhRecordLiftWorld.State n)

noncomputable def full :=
  Prod.fst <$> (simulateQ
    (RegistrationNativeG3MaterializedLocal.handler true table seeds setup codec route wire sign seed scalar candidate provider)
    (RegistrationNativeG2Trace.program
      (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run
    (cold frame ∅, world)

/-- The full known108-byte native frontend has exactly the same original ledger, frontend and G2 chronology as the actual known-side selective World interpretation. -/
theorem known_source :
    full table setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept publicPrekey serverKeyId
      bounds mode work front frame world =
      Prod.fst <$> RegistrationNativeG3AuditRepeatEvent.known setup codec route seeds wire sign seed scalar candidate provider checks source
        selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame
        (RegistrationNativeG3LocalMaterialCompletedSource.cache table) world := by
  let program : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)
      ((((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State)) :=
    RegistrationNativeG2Trace.program
    (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)
  let before : RegistrationNativeG3LocalKeys.State n KemSK ProviderState := (cold frame ∅, world)
  have mixed := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3MaterializedTracedProgram.frontend_source table setup codec route wire sign seed scalar candidate provider
      source checks selectedOwner selectedAccept publicPrekey seeds
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)
      front RegistrationNativeG2Trace.initial before)
  have actual := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3LocalMaterialCompletedSource.world_source table setup codec route wire sign seed scalar candidate provider
      (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds) program) before)
  have pulled := congrArg (fun actual =>
    (fun result => result.1.1) <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) actual).run world)
    (RegistrationNativeG3MaterializedSelectivePullback.program_source setup wire sign seed scalar candidate provider seeds program
      (RegistrationNativeG3LocalMaterialCompletion.put before (RegistrationNativeG3LocalMaterialCompletedSource.cache table)).1)
  simp only [RegistrationNativeG3MaterializedLocal.handler, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq] at mixed actual
  have sameRealize : RegistrationNativeG3GuardedMaterializedWorld.realize seeds =
      RegistrationNativeG3MaterializedWorld.realize seeds := rfl
  have combined := mixed.trans (actual.symm.trans pulled.symm)
  simpa only [full, RegistrationNativeG3AuditRepeatEvent.known,
    RegistrationNativeG3GuardedCoupling.known, RegistrationNativeG3GuardedMaterializedWorld.source,
    RegistrationNativeG3MaterializedLocal.handler, sameRealize, QueryImpl.simulateQ_compose,
    RegistrationNativePublicFrontend.run, RegistrationNativeG2Trace.program,
    RegistrationNativeG3LocalMaterialCompletion.put, RegistrationNativeG3LocalMaterialFrame.put,
    before, program, cold, Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using combined

/-- The actual cold marked G3 repeat audit is bounded by the selected-input repeat event of the same original full known108-byte native frontend execution. -/
theorem mark_bound (unused : ∀ slot role, world.used slot role = false) :
    Pr{let result ← (RegistrationNativeG3AuditRepeatEvent.original setup codec route seeds wire sign seed scalar candidate provider checks source
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame
      (RegistrationNativeG3LocalMaterialCompletedSource.cache table) world)}[result.2.2 = true] ≤
      Pr{let result ← (full table setup codec route seeds wire sign seed scalar candidate provider checks source selectedOwner selectedAccept publicPrekey serverKeyId
        bounds mode work front frame world)}[RegistrationNativeG2Trace.RepeatedRoleAttempt
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeSelectiveHiddenService.selected
            (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate) result.2.events] := by
  rw [known_source, prEvent_map]
  exact RegistrationNativeG3AuditRepeatEvent.mark_bound setup codec route seeds wire sign seed scalar candidate provider checks source
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front frame
    (RegistrationNativeG3LocalMaterialCompletedSource.cache table) world unused

end BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized.known_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized.mark_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditRepeatMaterialized.mark_bound
