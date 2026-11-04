-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStateInterpreter
import BeaconcryptCore.Computational.RegistrationNativeKemClientObservation
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHandler

/-! The same actual typed-call journal is retained through the complete counted KEM interpreter. Snapshots keep the private client and external platform; the complete KEM pool remains in the separate live interpreter state. This joint source equation retains chronology, origin/cache observations and every actual source cost, rather than only a final-state marginal. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemServerState (State ofNative toNative)
open RegistrationNativePlatformKemCountedBundle (project)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeWire (Wire)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Platform Value E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Client" => State n source
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "View" => Client × Platform
local notation "Journal" => List (Call TypedSpec View)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

private theorem interpret_packed (setup : Setup base KemSK)
    (work : StateT Client (RegistrationNativePlatformKemCountedProgram.M KemSK Platform) Value) :
    RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
        (RegistrationNativePlatformPackedState.pack work) = RegistrationNativePlatformKemCountedProgram.execute setup work := by
  funext before
  simp only [RegistrationNativeStateInterpreter.interpret, RegistrationNativePlatformPackedState.pack,
    RegistrationNativePlatformInterpret.state, RegistrationNativePlatformKemCountedProgram.execute,
    RegistrationNativePlatformKemCountedProgram.runState, RegistrationNativeKemCountedProgram.evaluate,
    StateT.run, simulateQ_map, map_apply, Functor.map_map,
    Prod.map, id_eq]
  rfl

def observe (before : Native × Platform) : View := (ofNative before.1, before.2)
def unarrange (before : ((View × Pool KemSK) × Journal)) : (View × Journal) × Pool KemSK :=
  ((before.1.1, before.2), before.1.2)
def projected (before : (Native × Platform) × Journal) : (View × Journal) × Pool KemSK :=
  (((ofNative before.1.1, before.1.2), before.2), before.1.1.pool)
def restore (before : (View × Journal) × Pool KemSK) : (Native × Platform) × Journal :=
  ((toNative before.1.1.1 before.2, before.1.1.2), before.1.2)

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def free : QueryImpl TypedSpec (StateT View (OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK))) :=
  fun query => RegistrationNativePlatformPackedState.pack
    (RegistrationNativePlatformOrdinaryKemHandler.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)

noncomputable def actual : QueryImpl TypedSpec (StateT (Native × Platform) ProbComp) :=
  fun query => RegistrationNativePlatformPackedState.pack
    (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)

/-- The counted source and literal native callback share the same complete current state and projected chronological journal. -/
theorem source_program (work : OracleComp TypedSpec Value) (before : (Native × Platform) × Journal) :
    (RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
      (simulateQ (RegistrationNativeObservedStageTrace.handler id
        (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work)).run
      (projected before) =
      Prod.map id projected <$>
        (simulateQ (RegistrationNativeObservedStageTrace.handler observe
          (actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work).run before := by
  have step (query : TypedSpec.Domain) (current : Native × Platform) :
      Prod.map id project <$>
        (actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run current =
      (RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
        (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)).run (project current) := by
    rw [free, interpret_packed]
    exact (RegistrationNativePlatformOrdinaryKemHandler.query_source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query current.1 current.2).symm
  have sourceLaw := RegistrationNativeObservedStageTrace.project
    (actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (fun query => RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
      (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query))
    project observe Prod.fst step (fun _ => rfl) work before
  have privateLaw := RegistrationNativeStateInterpreter.observed_program
    (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem) id
    (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    work (projected before)
  have law := congrArg (fun distribution => Prod.map id unarrange <$> distribution) (privateLaw.trans sourceLaw.symm)
  simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeStateInterpreter.arrange, projected, project, unarrange] at law
  change id <$> _ = _ at law
  rw [id_map] at law
  exact law

/-- Lossless private-pool reassembly yields the literal actual current native/platform state together with that same client journal. -/
theorem native (work : OracleComp TypedSpec Value) (before : (Native × Platform) × Journal) :
    Prod.map id restore <$>
      (RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
        (simulateQ (RegistrationNativeObservedStageTrace.handler id
          (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work)).run
        (projected before) =
      (simulateQ (RegistrationNativeObservedStageTrace.handler observe
        (actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work).run before := by
  rw [RegistrationNativePlatformOrdinaryKemClientJournal.source_program, Functor.map_map]
  change id <$> _ = _
  exact id_map _

/-- Projecting snapshots of the actual full-state source journal matches the counted free client journal, retaining the whole live private state. -/
theorem full (work : OracleComp TypedSpec Value)
    (before : (Native × Platform) × List (Call TypedSpec (Native × Platform))) :
    Prod.map id (fun result => (result.1, result.2.map (RegistrationNativeObservedStageTrace.mapCall observe))) <$>
      (simulateQ (RegistrationNativeStageTrace.handler
        (actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work).run before =
    Prod.map id restore <$>
      (RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
        (simulateQ (RegistrationNativeObservedStageTrace.handler id
          (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work)).run
        (projected (before.1, before.2.map (RegistrationNativeObservedStageTrace.mapCall observe))) := by
  rw [native]
  exact RegistrationNativeObservedStageTrace.full_project observe _ work before
/-- The one original chronological origin-or-final-cache exception has exactly the same mass in the counted client journal. -/
theorem origin_or_collision (work : OracleComp TypedSpec Value)
    (before : (Native × Platform) × List (Call TypedSpec (Native × Platform))) :
    Pr{let result ← (RegistrationNativeStateInterpreter.interpret (RegistrationNativeKemCountedProgram.handler setup.baseImpl setup.kem)
      (simulateQ (RegistrationNativeObservedStageTrace.handler id
        (free setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work)).run
        (projected (before.1, before.2.map (RegistrationNativeObservedStageTrace.mapCall observe)))}[
      RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) credential result.2.1.2 ∨
        CacheHasCollision (RegistrationNativeWorldCache.cache (toNative result.2.1.1.1 result.2.2))] =
    Pr{let result ← (simulateQ (RegistrationNativeStageTrace.handler
      (actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)) work).run before}[
      RegistrationNativePlatformMldsaOriginJournal.BadCalls credential result.2.2 ∨
        CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1)] := by
  have callBad (calls : List (Call TypedSpec (Native × Platform))) :
      RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) credential (calls.map (RegistrationNativeObservedStageTrace.mapCall observe)) ↔
        RegistrationNativePlatformMldsaOriginJournal.BadCalls credential calls :=
    RegistrationNativeKemClientObservation.bad_calls credential calls
  have law := congrArg (fun distribution => Pr{let result ← distribution}[
      RegistrationNativeKemClientObservation.BadCalls (KemSK := KemSK) credential result.2.2 ∨
        CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1.1)])
    (full setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before)
  simp only [prEvent_map, Prod.map, id_eq, restore, callBad] at law
  exact law.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.source_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.origin_or_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal.origin_or_collision
