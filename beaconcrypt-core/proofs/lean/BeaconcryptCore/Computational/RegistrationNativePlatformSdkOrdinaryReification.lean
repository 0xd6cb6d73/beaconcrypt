-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
/-! Actual ordinary KDF, seal, open, hash and fallible writer calls ignore only the masked administrative bill. Every other native/effect/uniform counter, shared cache, writer frame and persistent platform state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver (Primitive State)
variable {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

def primitive (before : Primitive) : Primitive :=
  ({before.1 with effects :=Function.update before.1.effects .administrative 0},before.2)

def journal (before : State) : State := (primitive before.1,before.2)

theorem primitive_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : Primitive) :
    Prod.map id primitive <$> (PqxdhRecordLiftWorld.primitives setup codec query).run before=
      (PqxdhRecordLiftWorld.primitives setup codec query).run (primitive before) := by
  simp only [PqxdhRecordLiftWorld.primitives,StateT.run,primitive,bind_pure_comp,Functor.map_map]
  rfl

private theorem lifted (work : StateT Primitive ProbComp A)
    (law : ∀before,Prod.map id primitive <$>work.run before=work.run (primitive before))
    (before : Primitive) (previous : Platform) :
    Prod.map (Prod.map id primitive) id <$>
      ((StateT.lift (work.run before) : StateT Platform ProbComp _).run previous)=
      (StateT.lift (work.run (primitive before)) : StateT Platform ProbComp _).run previous := by
  rw [StateT.run_lift,StateT.run_lift]
  simp only [bind_pure_comp,Functor.map_map]
  have equation:=congrArg (fun run =>(fun result =>(result,previous)) <$>run) (law before)
  simp only [Functor.map_map] at equation
  exact equation

theorem platform_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : Primitive) (previous : Platform) :
    Prod.map (Prod.map id primitive) id <$>
      (((RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve query).run before).run previous)=
      (((RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve query).run (primitive before)).run previous) := by
  rcases query with request | (sealed | (opened | (bytes | frame)))
  · exact lifted (PqxdhRecordLiftWorld.primitives setup codec (.inl request)) (primitive_query setup codec (.inl request)) before previous
  · exact lifted (PqxdhRecordLiftWorld.primitives setup codec (.inr (.inl sealed))) (primitive_query setup codec (.inr (.inl sealed))) before previous
  · exact lifted (PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inl opened)))) (primitive_query setup codec (.inr (.inr (.inl opened)))) before previous
  · exact lifted (PqxdhRecordLiftWorld.primitives setup codec (.inr (.inr (.inr (.inl bytes))))) (primitive_query setup codec (.inr (.inr (.inr (.inl bytes))))) before previous
  · rw [RegistrationNativePlatformOrdinaryWorld.writer_joint,RegistrationNativePlatformOrdinaryWorld.writer_joint,
      Functor.map_map]
    rfl

theorem journal_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State) (previous : Platform) :
    Prod.map (Prod.map id journal) id <$>
      (((RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve query).run before).run previous)=
      (((RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve query).run (journal before)).run previous) := by
  have equation:=congrArg (fun work =>(fun result =>((result.1.1,(result.1.2,
      RegistrationNativePlatformOrdinaryLogged.framesAfter query before.2)),result.2)) <$>work)
    (platform_query setup codec reserve query before.1 previous)
  change Prod.map (Prod.map id journal) id <$>
    (((fun reply =>(reply.1,(reply.2,RegistrationNativePlatformOrdinaryLogged.framesAfter query before.2))) <$>
      (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve query).run before.1).run previous)=
    (((fun reply =>(reply.1,(reply.2,RegistrationNativePlatformOrdinaryLogged.framesAfter query before.2))) <$>
      (RegistrationNativePlatformOrdinaryWorld.primitives setup codec reserve query).run (primitive before.1)).run previous)
  simp only [StateT.run_map,Functor.map_map]
  simp only [Functor.map_map] at equation
  exact equation

private theorem mapped {B : Type} (observe : A →B) (work : StateT Primitive ProbComp A)
    (law : ∀before,Prod.map id primitive <$>work.run before=work.run (primitive before))
    (before : Primitive) :
    Prod.map id primitive <$> (observe <$>work).run before=(observe <$>work).run (primitive before) := by
  have equation:=congrArg (fun run =>(fun result =>(observe result.1,result.2)) <$>run) (law before)
  simp only [StateT.run_map,Functor.map_map]
  simp only [Functor.map_map] at equation
  exact equation

theorem journal_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (before : State) (previous : Platform) :
    Prod.map (Prod.map id journal) id <$>
      ((simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve) work).run before).run previous=
      ((simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve) work).run (journal before)).run previous := by
  have query (selected : RawCtxMixedOwner.NativeSpec.Domain) (current : State) :
      Prod.map id journal <$> (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve selected).run current=
        (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve selected).run (journal current) := by
    funext platformState
    change (Prod.map id journal <$> (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve selected).run current).run platformState=_
    rw [StateT.run_map]
    exact journal_query setup codec reserve selected current platformState
  have equation:=OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve)
    (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve) journal query work before
  have run:=congrArg (fun result =>result.run previous) equation
  rw [StateT.run_map] at run
  exact run

private theorem native_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (before : Primitive) :
    Prod.map id primitive <$> (RegistrationNativeExtractedReceive.primitives setup codec query).run before=
      (RegistrationNativeExtractedReceive.primitives setup codec query).run (primitive before) := by
  rcases query with request | (bytes | input)
  all_goals simp only [RegistrationNativeExtractedReceive.primitives,QueryImpl.apply_compose,
    RawCtxMixedOwner.receiveLift,simulateQ_spec_query]
  · exact primitive_query setup codec (.inl request) before
  · exact primitive_query setup codec (.inr (.inr (.inr (.inl bytes)))) before
  · exact primitive_query setup codec (.inr (.inr (.inl input))) before

private theorem typed_query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.NativeSpec.Domain) (before : Primitive) :
    Prod.map id primitive <$>
      ((BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.typed
        (RegistrationNativeExtractedReceive.primitives setup codec) query).run before)=
      ((BeaconcryptCore.Refinement.AdapterRecordNativeRepresentation.typed
        (RegistrationNativeExtractedReceive.primitives setup codec) query).run (primitive before)) := by
  rcases query with request | (bytes | input)
  · exact native_query setup codec (.inl request) before
  · exact mapped _ (RegistrationNativeExtractedReceive.primitives setup codec (.inr (.inl bytes)))
      (native_query setup codec (.inr (.inl bytes))) before
  · exact mapped _ (RegistrationNativeExtractedReceive.primitives setup codec (.inr (.inr input)))
      (native_query setup codec (.inr (.inr input))) before

theorem receive_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (work : OracleComp BeaconcryptCore.Refinement.AdapterRecordRequestMonad.Spec A)
    (before : Primitive) :
    Prod.map id primitive <$>
      ((simulateQ (RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.replies setup codec erased) work).run before)=
      ((simulateQ (RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.replies setup codec erased) work).run (primitive before)) := by
  unfold RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.replies
  rw [QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ primitive (typed_query setup codec) _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.primitive_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.primitive_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.platform_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.platform_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.journal_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.journal_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.journal_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.journal_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.receive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryReification.receive_program
