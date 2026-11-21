-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling
import BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame

/-! The actual guarded known-side repetition audit retains a chronological slot/role history. Its log is private instrumentation: erasing it recovers the literal existing marked interpreter. The used-role update below is derived from the actual known installation and its success audit, including refusal. Relating these slot events to demanded root descriptors remains a separate frontend provenance obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory
open PqxdhRecordLiftInterface (Slot Role WorldSpec)
open PqxdhRecordLiftWorld (State)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedWorld (Request Spec Seeds seeded repeated)
open RegistrationNativeG3GuardedWorld (step marked)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

inductive Event (n : Nat) where
  | attempt (slot : Slot n) (role : Role)
  | success (slot : Slot n) (role : Role)
  deriving DecidableEq

def events : (query : Request n) → (Spec n).Range query → List (Event n)
  | .ordinary .., _ => []
  | .server _ _ slot, reply => .attempt slot .server :: if (show Bool from reply) then [.success slot .server] else []
  | .beacon _ _ slot, reply => .attempt slot .beacon :: if (show Bool from reply) then [.success slot .beacon] else []

def updateUsed : (query : Request n) → (Spec n).Range query → (Slot n → Role → Bool) → (Slot n → Role → Bool)
  | .ordinary .., _, used => used
  | .server _ _ slot, reply, used => if (show Bool from reply) then Function.update used slot (Function.update (used slot) .server true) else used
  | .beacon _ _ slot, reply, used => if (show Bool from reply) then Function.update used slot (Function.update (used slot) .beacon true) else used

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) :
    QueryImpl (Spec n) (StateT ((State n × Bool) × List (Event n)) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2, before.2 ++ events query result.1))) <$>
    (marked setup codec route seeds true query).run before.1

private theorem ordinary_used (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (allowed : RegistrationNativeG3KnownWorldFrameCore.Allowed query) (before : State n)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((CborRecordWorldSimulation.guarded setup codec route query).run before)) :
    result.2.used = before.used := by
  simp only [CborRecordWorldSimulation.guarded, StateT.run] at supported
  cases refusal : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | none =>
      simp only [refusal] at supported
      exact RegistrationNativeG3AuditWorldFrame.used_keeps setup codec route query allowed before result supported
  | some reply =>
      simp only [refusal, mem_support_pure_iff] at supported
      cases supported
      rfl

private theorem audit_used (role : Role) (slot : Slot n) (result : Bool × State n) :
    (RegistrationNativeG3AuditedInstall.audit role slot result).2.used =
      if result.1 then Function.update result.2.used slot (Function.update (result.2.used slot) role true) else result.2.used := by
  cases result with | mk reply world => cases reply <;> rfl

/-- The literal guarded marked callback updates a used bit exactly when its actual role installation succeeds. -/
theorem query_used (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : Request n)
    (before : State n × Bool) (result : (Spec n).Range query × (State n × Bool))
    (supported : result ∈ support ((marked setup codec route seeds true query).run before)) :
    result.2.1.used = updateUsed query result.1 before.1.used := by
  simp only [marked, StateT.run, support_map] at supported
  obtain ⟨reached, actual, equal⟩ := supported
  cases equal
  cases query with
  | ordinary query allowed =>
      exact ordinary_used setup codec route query allowed (seeded seeds before.1) reached actual
  | server keyId binding slot =>
      simp only [step, RegistrationNativeG3AuditedWorld.step, ite_true, StateT.run, support_map] at actual
      obtain ⟨installed, possible, equal⟩ := actual
      cases equal
      have old := RegistrationNativeG3AuditWorldFrame.used_keeps setup codec route
        (.inr (.inl (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot)))))))
        (by exact id) (seeded seeds before.1) installed possible
      simp only [RegistrationNativeG3AuditedInstall.view, updateUsed, audit_used,
        RegistrationNativeG3AuditedInstall.audit_fields, old, seeded]
  | beacon owner shell slot =>
      simp only [step, RegistrationNativeG3AuditedWorld.step, ite_true, StateT.run, support_map] at actual
      obtain ⟨installed, possible, equal⟩ := actual
      cases equal
      have old := RegistrationNativeG3AuditWorldFrame.used_keeps setup codec route
        (.inr (.inl (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot)))))))
        (by exact id) (seeded seeds before.1) installed possible
      simp only [RegistrationNativeG3AuditedInstall.view, updateUsed, audit_used,
        RegistrationNativeG3AuditedInstall.audit_fields, old, seeded]

/-- Erasing only the chronological role history leaves the actual marked callback unchanged. -/
theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : Request n)
    (before : (State n × Bool) × List (Event n)) :
    Prod.map id Prod.fst <$> (handler setup codec route seeds query).run before =
      (marked setup codec route seeds true query).run before.1 := by
  simp only [handler, StateT.run, Functor.map_map, Prod.map_def, id_eq, id_map']

/-- The history instrumentation preserves the whole actual adaptive program and complete original marked state. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : (State n × Bool) × List (Event n)) :
    Prod.map id Prod.fst <$> (simulateQ (handler setup codec route seeds) work).run before =
      (simulateQ (marked setup codec route seeds true) work).run before.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (query_source setup codec route seeds) work before

end BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory.query_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory.query_used
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditHistory.program_source
