-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditedInstall
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore

/-! A private materialized World program exposes ordinary actual World requests and the two concrete canonical installation requests. Its known side audits successful slot/role use; its hidden side uses the actual native hidden capability. Both stop before a repeated-role installation. Completing a fixed private seed table before a callback is explicit in this proof game. The exact stopped-program equality below does not assert seed-delay, native-frontend materialization, or a probability bound on repetition; those are separate composition obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld
open PqxdhRecordLiftInterface (Slot WorldSpec PeerBinding BeaconShell Role)
open PqxdhRecordLiftWorld (State kernel)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedInstall (audit view)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

inductive Request (n : Nat) where
  | ordinary (query : (WorldSpec n).Domain) (allowed : RegistrationNativeG3KnownWorldFrameCore.Allowed query)
  | server (keyId : Std.U64) (binding : PeerBinding) (slot : Slot n)
  | beacon (owner : Nat) (shell : BeaconShell) (slot : Slot n)

def Spec (n : Nat) : OracleSpec (Request n)
  | .ordinary query _ => (WorldSpec n).Range query
  | .server .. | .beacon .. => Bool

abbrev Seeds (n : Nat) := Slot n → PqxdhRecordLiftSeed.Seed

def seeded (seeds : Seeds n) (before : State n) : State n :=
  { before with seeds := (⟨fun slot => some (seeds slot)⟩, ⟨0, 0⟩) }

def repeated : Request n → State n → Bool
  | .ordinary .., _ => false
  | .server _ _ slot, before => before.used slot .server
  | .beacon _ _ slot, before => before.used slot .beacon

noncomputable def step (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (known : Bool) :
    QueryImpl (Spec n) (StateT (State n) ProbComp)
  | .ordinary query _ => PqxdhRecordLiftWorld.handler setup codec route query
  | .server keyId binding slot => if known then fun before =>
      audit .server slot <$> (PqxdhRecordLiftWorld.effects
        (.inr (.installServer keyId binding (.known (kernel .server (seeds slot)))))).run before
    else PqxdhRecordLiftWorld.effects (.inr (.installServer keyId binding (.hidden slot)))
  | .beacon owner shell slot => if known then fun before =>
      audit .beacon slot <$> (PqxdhRecordLiftWorld.effects
        (.inr (.installBeacon owner shell (.known (kernel .beacon (seeds slot)))))).run before
    else PqxdhRecordLiftWorld.effects (.inr (.installBeacon owner shell (.hidden slot)))

noncomputable def stopped (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (known : Bool) :
    QueryImpl (Spec n) (OptionT (StateT (State n) ProbComp)) := fun query =>
  OptionT.mk (fun before => if repeated query before then pure (none, view before)
    else (fun result => (some result.1, view result.2)) <$>
      (step setup codec route seeds known query).run (seeded seeds before))

/-- Fixed private completion changes only the seed table and its logical accounting. The complete role history is retained. -/
theorem seeded_view (seeds : Seeds n) (before : State n) :
    view (seeded seeds before) = view before ∧ (seeded seeds before).used = before.used := ⟨rfl, rfl⟩

/-- Before repetition, the actual audited known and actual hidden callback have identical seed-erased outcomes. -/
theorem step_eq (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (query : (Spec n).Domain) (before : State n) (fresh : repeated query before = false) :
    Prod.map id view <$> (step setup codec route seeds true query).run (seeded seeds before) =
      Prod.map id view <$> (step setup codec route seeds false query).run (seeded seeds before) := by
  cases query with
  | ordinary query allowed => rfl
  | server keyId binding slot =>
      simpa only [step, ite_true, Bool.false_eq_true, ite_false, StateT.run, Functor.map_map, Function.comp_def] using
        RegistrationNativeG3AuditedInstall.server_effect keyId binding slot (seeds slot) (seeded seeds before) rfl fresh
  | beacon owner shell slot =>
      simpa only [step, ite_true, Bool.false_eq_true, ite_false, StateT.run, Functor.map_map, Function.comp_def] using
        RegistrationNativeG3AuditedInstall.beacon_effect owner shell slot (seeds slot) (seeded seeds before) rfl fresh

/-- Repetition is checked before either installation callback. All other branches use the exact native stateful callback. -/
theorem stopped_eq (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) :
    stopped setup codec route seeds true = stopped setup codec route seeds false := by
  funext query
  apply OptionT.ext
  funext before
  change (if repeated query before then pure (none, view before) else
    (fun result => (some result.1, view result.2)) <$>
      (step setup codec route seeds true query).run (seeded seeds before)) =
    (if repeated query before then pure (none, view before) else
      (fun result => (some result.1, view result.2)) <$>
        (step setup codec route seeds false query).run (seeded seeds before))
  by_cases bad : repeated query before = true
  · simp only [bad, ite_true]
  · have fresh : repeated query before = false := Bool.eq_false_iff.mpr bad
    simp only [fresh, Bool.false_eq_true, ite_false]
    have same := congrArg (fun distribution => (fun result => (some result.1, result.2)) <$> distribution)
      (step_eq setup codec route seeds query before fresh)
    simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_def] using same

/-- Any adaptive materialized World continuation has the same full seed-erased stopped law, preserving used roles, CTX, records, counters and produced frames. -/
theorem program_eq (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n) :
    ((simulateQ (stopped setup codec route seeds true) work).run).run before =
      ((simulateQ (stopped setup codec route seeds false) work).run).run before := by
  rw [stopped_eq]

end BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.seeded_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.seeded_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.step_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.step_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.stopped_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.stopped_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.program_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditedWorld.program_eq
