-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedWorld
import BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore

/-! The known interpretation of the materialized Tag AST is the actual guarded fixed-table World interpreter, after erasing only private seed and success-audit role bookkeeping. Ordinary callbacks and every native counter, record, populated AD and CTX field remain literal. This source projection does not assert that repeated attempts are unlikely. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorld
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftWorld (State)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeHiddenWorldInstall (view)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

noncomputable def realize (seeds : Seeds n) : QueryImpl (WorldSpec n) (OracleComp (WorldSpec n))
  | .inr (.inl (.inr (.installServer keyId binding (.hidden slot)))) =>
      (WorldSpec n).query (.inr (.inl (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot)))))))
  | .inr (.inl (.inr (.installBeacon owner shell (.hidden slot)))) =>
      (WorldSpec n).query (.inr (.inl (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot)))))))
  | query => (WorldSpec n).query query

noncomputable def source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) :=
  CborRecordWorldSimulation.guarded setup codec route ∘ₛ realize seeds

/-- The actual guarded known callback ignores only private seed/use fields, retaining every public refusal and complete result. -/
theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (allowed : RegistrationNativeG3KnownWorldFrameCore.Allowed query) (before : State n) :
    Prod.map id view <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      Prod.map id view <$> (CborRecordWorldSimulation.guarded setup codec route query).run (view before) := by
  have shell : CborRecordWorldCursor.worldShell (view before) = CborRecordWorldCursor.worldShell before := rfl
  simp only [CborRecordWorldSimulation.guarded, StateT.run, shell]
  cases refusal : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply =>
      simp only [map_pure, Prod.map_def, id_eq]
      rfl
  | none => exact RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route query allowed before

private theorem audit_forget (role : PqxdhRecordLiftInterface.Role) (slot : PqxdhRecordLiftInterface.Slot n)
    (result : Bool × State n) :
    Prod.map id view (RegistrationNativeG3AuditedInstall.audit role slot result) = Prod.map id view result := by
  apply Prod.ext
  · exact (RegistrationNativeG3AuditedInstall.audit_fields role slot result).1
  · exact (RegistrationNativeG3AuditedInstall.audit_fields role slot result).2

private theorem audit_map (role : PqxdhRecordLiftInterface.Role) (slot : PqxdhRecordLiftInterface.Slot n) :
    (fun result => Prod.map id view (RegistrationNativeG3AuditedInstall.audit role slot result)) = Prod.map id view :=
  funext (audit_forget role slot)

private theorem ordinary (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (WorldSpec n).Domain)
    (allowed : RegistrationNativeG3KnownWorldFrameCore.Allowed query)
    (real : realize seeds query = (WorldSpec n).query query)
    (tag : RegistrationNativeG3Materialize.materialize query =
      (RegistrationNativeG3AuditedWorld.Spec n).query (.ordinary query allowed)) (before : State n) :
    Prod.map id view <$> (source setup codec route seeds query).run before =
      Prod.map id view <$>
        (simulateQ (RegistrationNativeG3GuardedWorld.step setup codec route seeds true)
          (RegistrationNativeG3Materialize.materialize query)).run (view before) := by
  simp only [source, QueryImpl.apply_compose, real, tag, simulateQ_spec_query, RegistrationNativeG3GuardedWorld.step]
  exact handler_input setup codec route query allowed before

/-- The actual fixed-table callback has exactly the materialized known Tag interpretation after forgetting its private success audit. -/
theorem query_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id view <$> (source setup codec route seeds query).run before =
      Prod.map id view <$>
        (simulateQ (RegistrationNativeG3GuardedWorld.step setup codec route seeds true)
          (RegistrationNativeG3Materialize.materialize query)).run (view before) := by
  rcases query with created | (coin | capability) | record
  · exact ordinary setup codec route seeds (.inl created) trivial rfl rfl before
  · exact ordinary setup codec route seeds (.inr (.inl (.inl coin))) trivial rfl rfl before
  · cases capability with
    | installServer keyId binding ref => cases ref with
      | hidden slot =>
          have actual := handler_input setup codec route
            (.inr (.inl (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot))))))) (by exact id) before
          simpa only [source, realize, QueryImpl.apply_compose, RegistrationNativeG3Materialize.materialize,
            simulateQ_spec_query, RegistrationNativeG3GuardedWorld.step, RegistrationNativeG3AuditedWorld.step, ite_true, StateT.run,
            Functor.map_map, Function.comp_def, audit_map, CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler] using actual
      | known kernel =>
          exact ordinary setup codec route seeds
            (.inr (.inl (.inr (.installServer keyId binding (.known kernel))))) (by exact id) rfl rfl before
    | installBeacon owner shell ref => cases ref with
      | hidden slot =>
          have actual := handler_input setup codec route
            (.inr (.inl (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot))))))) (by exact id) before
          simpa only [source, realize, QueryImpl.apply_compose, RegistrationNativeG3Materialize.materialize,
            simulateQ_spec_query, RegistrationNativeG3GuardedWorld.step, RegistrationNativeG3AuditedWorld.step, ite_true, StateT.run,
            Functor.map_map, Function.comp_def, audit_map, CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler] using actual
      | known kernel =>
          exact ordinary setup codec route seeds
            (.inr (.inl (.inr (.installBeacon owner shell (.known kernel))))) (by exact id) rfl rfl before
    | peerPresent keyId => exact ordinary setup codec route seeds (.inr (.inl (.inr (.peerPresent keyId)))) (by exact id) rfl rfl before
    | ownerPresent owner => exact ordinary setup codec route seeds (.inr (.inl (.inr (.ownerPresent owner)))) (by exact id) rfl rfl before
    | appendOwner identity keyId phase =>
        exact ordinary setup codec route seeds
          (.inr (.inl (.inr (.appendOwner identity keyId phase)))) (by exact id) rfl rfl before
    | advanceOwner owner phase => exact ordinary setup codec route seeds (.inr (.inl (.inr (.advanceOwner owner phase)))) (by exact id) rfl rfl before
    | hash bytes => exact ordinary setup codec route seeds (.inr (.inl (.inr (.hash bytes)))) (by exact id) rfl rfl before
  · exact ordinary setup codec route seeds (.inr (.inr record)) trivial rfl rfl before

end BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorld.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorld.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorld.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMaterializedWorld.query_project
