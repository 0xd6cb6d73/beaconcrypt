-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordViewCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
/-! The actual crypto-produced frames and raw-attempt coordinates have the literal all-real record-package law beside the original complete result. This permits the original source event to use the ordered record reductions without an observer equality supplied by the caller. CTX-cache inspection is outside this narrower record-event observation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPackageSource
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeEntropyRun (Outcome)
open RegistrationNativeRecordPackage (Extra View encode decode client)
variable {n : Nat} {I KemSK Reader Response E Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (Outcome E Value))
    (observe : Outcome E Value → List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) → PqxdhRecordLiftWorld.RawCounters → Bool)

/-- The actual full result, produced-stage frames and literal raw attempts are exactly the all-real record-package observation. -/
theorem real_source :
    (fun result => observe result.result result.produced result.raw) <$>
      RegistrationNativeRecordViewCrypto.real setup codec route work =
      (fun result => observe result.1 result.2.produced (PqxdhRecordLiftWorld.rawCounters result.2)) <$>
        (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run PqxdhRecordLiftWorld.initial := by
  have original := congrArg (Functor.map (fun (result : PqxdhRecordLiftLaterWorlds.Outcome (Extra E) Value × PqxdhRecordLiftWorld.State n) =>
    observe (decode result.1) result.2.produced (PqxdhRecordLiftWorld.rawCounters result.2)))
    (CborRawRecordLiftCrypto.real_source setup codec route (client work))
  have packaged : (fun result => observe result.result result.produced result.raw) <$>
      RegistrationNativeRecordViewCrypto.real setup codec route work =
        (fun (result : PqxdhRecordLiftLaterWorlds.Outcome (Extra E) Value × PqxdhRecordLiftWorld.State n) =>
          observe (decode result.1) result.2.produced (PqxdhRecordLiftWorld.rawCounters result.2)) <$>
          (Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ PqxdhRecordLiftProtocol.rejoin) <$>
            PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route (client work) := by
    simp only [RegistrationNativeRecordViewCrypto.real,Functor.map_map]
    congr 1
    funext result
    simp only [Function.comp_def,Prod.map_def,id_eq]
    rw [← PqxdhRecordLiftWorldCompiler.rawCounters_erasure]
    rcases result with ⟨⟨outcome,control⟩,secretState⟩
    cases outcome <;> cases existing : control.server <;>
      simp only [RegistrationNativeRecordPackage.view,PqxdhRecordLiftIdeal.chainView,PqxdhRecordLiftIdeal.viewOf,
        decode,PqxdhRecordLiftProtocol.rejoin,PqxdhRecordLiftProtocol.join,
        PqxdhRecordLiftWorldCompiler.rawCounters,PqxdhRecordLiftProtocol.rawCounters,existing,
        Option.map_none,Option.map_some] <;> rfl
  rw [packaged]
  rw [original]
  simp only [client,RegistrationNativeEntropyProgram.cursor_map,simulateQ_map,StateT.run_map,Functor.map_map]
  have guarded := congrArg (Functor.map (fun result => observe result.1 result.2.produced
    (PqxdhRecordLiftWorld.rawCounters result.2)))
    (CborRecordWorldSimulation.client_simulation setup codec route work PqxdhRecordLiftWorld.initial)
  simpa only [RegistrationNativeRecordPackage.decode_encode,CborRecordWorldCursor.initial_shell] using guarded

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPackageSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPackageSource.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPackageSource.real_source
