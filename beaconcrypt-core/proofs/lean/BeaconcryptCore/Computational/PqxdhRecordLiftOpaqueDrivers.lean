-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler

/-! Private source programs retain labeled opening and sealing capabilities until interpretation. Coordinate lookup replies reveal no derived bytes; full-state interpretation recovers the existing complete source drivers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler
variable {Slot OpenContext Plaintext SealContext Output PrimitiveState : Type}

abbrev LabeledOpening (Slot Context : Type) :=
  RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context
abbrev LabeledSeal (Slot Context : Type) :=
  RawCtxChainSend.Seal (Label Slot) (Label Slot) (Label Slot) Context

/-- These services are private compiler operations. Unit lookup replies expose no full76 value or projection to the source continuation. -/
abbrev ServiceSpec (Slot OpenContext Plaintext SealContext Output : Type) :=
  (Label Slot →ₒ Unit) +
    ((LabeledOpening Slot OpenContext →ₒ core.option.Option Plaintext) +
      (LabeledSeal Slot SealContext →ₒ Option Output))

/-- The source receive follows literal control transitions and returns the actual opening reply. No seed, byte-key interpretation or table is an argument. -/
noncomputable def receiveProgram (effect : Effect Slot OpenContext) :
    OracleComp (ServiceSpec Slot OpenContext Plaintext SealContext Output)
      (LabeledKernel Slot × core.option.Option Plaintext) :=
  match effect with
  | .rejected entry _ => pure (entry, .None)
  | .openRequested pending => do
      let reply ← (ServiceSpec Slot OpenContext Plaintext SealContext Output).query (.inr (.inl pending))
      pure (RawCtxChainReceive.normalFinish pending reply)
  | .kdfRequested pending => do
      let _ ← (ServiceSpec Slot OpenContext Plaintext SealContext Output).query (.inl pending.request)
      receiveProgram (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request))
termination_by RawCtxChainReceive.effectRank effect
decreasing_by exact RawCtxChainReceive.normalResume_rank _ _

/-- Source send advances before handing its whole labeled sealing capability to the private service, retaining the real optional result. -/
noncomputable def sendProgram (start : Start Slot SealContext) :
    OracleComp (ServiceSpec Slot OpenContext Plaintext SealContext Output)
      (LabeledKernel Slot × Option Output) :=
  match start with
  | .exhausted entry _ => pure (entry, none)
  | .requested pending => do
      let _ ← (ServiceSpec Slot OpenContext Plaintext SealContext Output).query (.inl pending.request)
      let ready := RawCtxChainSend.ready pending (advance pending.request 1, pending.request)
      let sealed ← (ServiceSpec Slot OpenContext Plaintext SealContext Output).query (.inr (.inr ready))
      pure (ready.advanced, sealed)

/-- Only the private interpreter reads concrete bytes. Opening/sealing erase their complete pending context at the actual current table and retain all primitive effects. -/
noncomputable def interpreter (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState) :
    QueryImpl (ServiceSpec Slot OpenContext Plaintext SealContext Output)
      (StateT (Execution Slot PrimitiveState) ProbComp)
  | .inl coordinate => (fun _ => ()) <$> lookup coordinate
  | .inr (.inl pending) => fun state => do
      let reply ← (opening (eraseOpening seeds state.1 pending)).run state.2
      pure (reply.1, (state.1, reply.2))
  | .inr (.inr pending) => fun state => do
      let reply ← (sealing (eraseSeal seeds state.1 pending)).run state.2
      pure (reply.1, (state.1, reply.2))

/-- Interpreting the entire recursive private receive gives the exact existing source driver, including the table, full native state and actual optional plaintext. -/
theorem receive_interpretation (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (effect : Effect Slot OpenContext) (state : Execution Slot PrimitiveState) :
    (simulateQ (interpreter seeds lookup opening sealing) (receiveProgram effect)).run state =
      (receive seeds lookup opening effect).run state := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      simp only [receiveProgram, simulateQ_pure, StateT.run, receive]
      rfl
    | openRequested pending =>
      simp only [receiveProgram, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        interpreter, StateT.run, receive]
      change ((do
        let reply ← opening (eraseOpening seeds state.1 pending) state.2
        pure (reply.1, (state.1, reply.2))) >>= fun reply =>
          pure (RawCtxChainReceive.normalFinish pending reply.1, reply.2)) = _
      simp only [bind_assoc, pure_bind]
    | kdfRequested pending =>
      simp only [receiveProgram, simulateQ_bind, simulateQ_spec_query, interpreter,
        bind_map_left, StateT.run, receive]
      exact bind_congr fun (reply : PqxdhFullSecretInputKdf.FullOutput × Execution Slot PrimitiveState) => ih _
        (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ reply.2 rfl

/-- Interpreting the entire private send gives the exact source driver, including advancement on sealing failure and all native effects. -/
theorem send_interpretation (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (start : Start Slot SealContext) (state : Execution Slot PrimitiveState) :
    (simulateQ (interpreter seeds lookup opening sealing) (sendProgram start)).run state =
      (send seeds lookup sealing start).run state := by
  cases start with
  | exhausted entry context =>
    simp only [sendProgram, simulateQ_pure, StateT.run, send]
    rfl
  | requested pending =>
    simp only [sendProgram, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      interpreter, bind_map_left, StateT.run, send]
    change ((lookup pending.request state) >>= fun reply =>
      (do
        let sealed ← sealing (eraseSeal seeds reply.2.1
          (RawCtxChainSend.ready pending (advance pending.request 1, pending.request))) reply.2.2
        pure (sealed.1, (reply.2.1, sealed.2))) >>= fun sealed =>
          pure (((RawCtxChainSend.ready pending (advance pending.request 1, pending.request)).advanced,
            sealed.1), sealed.2)) = _
    simp only [bind_assoc, pure_bind]

/-- The receive equality holds before any adaptive private continuation, evaluated at the complete actual poststate. -/
theorem receive_continuation {Result : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (effect : Effect Slot OpenContext) (state : Execution Slot PrimitiveState)
    (continuation : LabeledKernel Slot × core.option.Option Plaintext →
      OracleComp (ServiceSpec Slot OpenContext Plaintext SealContext Output) Result) :
    (simulateQ (interpreter seeds lookup opening sealing) (receiveProgram effect >>= continuation)).run state =
      (do
        let reply ← (receive seeds lookup opening effect).run state
        (simulateQ (interpreter seeds lookup opening sealing) (continuation reply.1)).run reply.2) := by
  rw [simulateQ_bind, StateT.run_bind, receive_interpretation]

/-- The send equality includes every adaptive private continuation, using the actual optional sealing reply and complete poststate. -/
theorem send_continuation {Result : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (start : Start Slot SealContext) (state : Execution Slot PrimitiveState)
    (continuation : LabeledKernel Slot × Option Output →
      OracleComp (ServiceSpec Slot OpenContext Plaintext SealContext Output) Result) :
    (simulateQ (interpreter seeds lookup opening sealing) (sendProgram start >>= continuation)).run state =
      (do
        let reply ← (send seeds lookup sealing start).run state
        (simulateQ (interpreter seeds lookup opening sealing) (continuation reply.1)).run reply.2) := by
  rw [simulateQ_bind, StateT.run_bind, send_interpretation]

/-- The full source receive starts with the actual admission decision, including its rejection branches. -/
noncomputable def admittedReceive (entry : LabeledKernel Slot) (target : Std.U64) (context : OpenContext) :
    OracleComp (ServiceSpec Slot OpenContext Plaintext SealContext Output)
      (LabeledKernel Slot × core.option.Option Plaintext) :=
  receiveProgram (RawCtxChainReceive.normalBegin entry target context)

/-- The full source send starts with the actual source exhaustion decision. -/
noncomputable def admittedSend (entry : LabeledKernel Slot) (context : SealContext) :
    OracleComp (ServiceSpec Slot OpenContext Plaintext SealContext Output)
      (LabeledKernel Slot × Option Output) :=
  sendProgram (RawCtxChainSend.normalBegin entry context)

/-- Every target, entry kernel and admission outcome has the same complete evaluated receive distribution. -/
theorem admitted_receive_interpretation (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (entry : LabeledKernel Slot) (target : Std.U64) (context : OpenContext)
    (state : Execution Slot PrimitiveState) :
    (simulateQ (interpreter seeds lookup opening sealing) (admittedReceive entry target context)).run state =
      (receive seeds lookup opening (RawCtxChainReceive.normalBegin entry target context)).run state :=
  receive_interpretation seeds lookup opening sealing _ state

/-- Every entry kernel and source exhaustion outcome has the same complete evaluated send distribution. -/
theorem admitted_send_interpretation (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (entry : LabeledKernel Slot) (context : SealContext) (state : Execution Slot PrimitiveState) :
    (simulateQ (interpreter seeds lookup opening sealing) (admittedSend entry context)).run state =
      (send seeds lookup sealing (RawCtxChainSend.normalBegin entry context)).run state :=
  send_interpretation seeds lookup opening sealing _ state

end BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.receive_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.receive_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.send_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.send_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.receive_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.receive_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.send_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.send_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.admitted_receive_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.admitted_receive_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.admitted_send_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers.admitted_send_interpretation
