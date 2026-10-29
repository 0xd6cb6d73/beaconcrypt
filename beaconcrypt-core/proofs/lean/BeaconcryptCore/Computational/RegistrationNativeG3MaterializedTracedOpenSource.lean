-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedLazy
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedStartup
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupFields
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource

/-! The cold known108 protocol retains the same full result, frontend and installation trace when its genuine selected material and seed tables are replaced by the ordinary lazy108 open-key source. Only empty completed caches are simplified; the entire reached startup World, including its shared ML-pin hash cache, is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedOpenSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
variable {ι KemSK P Value : Type} {base : OracleSpec ι}

/-- The complete known108 original frontend has the same joint full-ledger and chronological law as its actual lazy108 open-key client. -/
theorem frontend_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK P) (providerState : P)
    (selectedOwner selectedAccept : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (front : RegistrationNativePublicFrontend.State source)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (seeds_empty : world.seeds = PqxdhRecordLiftLazyTable.initial) :
    LazyOracleDiscard.LawEq
      (RegistrationNativeG3MaterializedTracedProtocolLazy.fullGame setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider source checks
        selectedOwner selectedAccept (setup.dh.publicKey scalar)
        (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) front
        (RegistrationNativeSelectiveHiddenInterpreter.initial providerState, world))
      ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)
          (RegistrationNativeG3MaterializedRetainedLazy.client setup wire route sign seed scalar
            (RegistrationNativeG2Trace.program (RegistrationNativePublicFrontend.run setup checks wire source sign
              selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work front))
            (RegistrationNativeHiddenInterpreter.initial providerState) world)).run' (PqxdhLiveKemBirth.empty, providerState))).run' ∅) := by
  have bills :
      (RegistrationNativeG2Trace.program (RegistrationNativePublicFrontend.run (n := budget.cap 4 + budget.cap 5) setup checks wire source sign
        selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work front)).IsQueryBoundP
          (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
    apply RegistrationNativeG2Trace.program_bound
    exact RegistrationNativePublicCaps.run_bound setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
      serverKeyId bounds mode work budget bounded front
  have compared := RegistrationNativeG3MaterializedRetainedLazy.program_source setup wire route sign seed scalar candidate provider
    (RegistrationNativeG2Trace.program (RegistrationNativePublicFrontend.run setup checks wire source sign
      selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work front)) bills
    (RegistrationNativeHiddenInterpreter.initial providerState) world
  have overlay (seeds : RegistrationNativeG3AuditedWorld.Seeds (budget.cap 4 + budget.cap 5)) :
      RegistrationNativeG3GuardedCoupling.overlay world seeds = seeds := by
    funext slot
    simp [RegistrationNativeG3GuardedCoupling.overlay, seeds_empty, PqxdhRecordLiftLazyTable.initial, OracleComp.completeTable]
  simpa only [RegistrationNativeG3MaterializedTracedProtocolLazy.fullGame, RegistrationNativeG3MaterializedTracedProtocol.fullGame,
    RegistrationNativeG3MaterializedTracedProtocol.full, RegistrationNativeG3MaterializedTracedProtocol.publicProgram,
    RegistrationNativePublicFrontend.run, RegistrationNativeSelectiveHiddenInterpreter.initial,
    RegistrationNativeHiddenInterpreter.initial, RegistrationNativeHiddenService.initial,
    OracleComp.completeTable_empty, overlay, StateT.run'_eq, RegistrationNativeG3AuditTraceRun.cold] using compared

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedOpenSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedOpenSource.frontend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedOpenSource.frontend_source
