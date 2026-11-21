-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordFlat

/-! The full cursor-aware native execution retains the actual private service state and cursor updates. Equal-length hidden sends in the zeroed world have identical complete executions, including a refusal; uniform ledger coins leave the public cursor unchanged. These functional laws support the actual byte-shift and test-bit couplings. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.CborRawRecordFlatSemantics
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (Spec Handle)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (KnownAt zeros coinStep)
open CborRawRecordFlat (NativeState nativeImpl clientImpl project sendRefusal nextSend)
variable {n : Nat} {ι : Type} {base : OracleSpec ι} {KemSK Reader Response E : Type}

def withShell (shell : CborRecordWorldClient.Shell) (state : PqxdhRecordLiftFlat.NativeState n E) : NativeState n E :=
  (((state.1.1, shell), state.1.2), state.2)

theorem native_program_run {Result : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (work : OracleComp Spec Result) (state : NativeState n E) :
    (simulateQ (nativeImpl modes replace setup codec route env) work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (ctxInterpreter modes replace setup codec)
          ((simulateQ (clientImpl env codec route) work).run state.1)).run state.2 := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map, Prod.mk.eta]
  change _ = id <$> _
  exact (id_map _).symm

private theorem original_program_run {Result : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (work : OracleComp Spec Result) (state : PqxdhRecordLiftFlat.NativeState n E) :
    (simulateQ (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env) work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (ctxInterpreter modes replace setup codec)
          ((simulateQ (PqxdhRecordLiftFlat.clientImpl env codec route) work).run state.1)).run state.2 := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map, Prod.mk.eta]
  change _ = id <$> _
  exact (id_map _).symm

/-- The complete send retains its reached public cursor and all private native effects, or stutters before a refused record call. -/
theorem native_send_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes) (state : NativeState n E) :
    (simulateQ (nativeImpl modes replace setup codec route env) (PqxdhDeploymentSecrecy.send handle plaintext)).run state =
      match sendRefusal (n := n) handle plaintext state.1.1.2 with
      | some reply => pure (reply, state)
      | none => (fun result => (result.1,
          withShell (nextSend (n := n) handle plaintext result.1 state.1.1.2) result.2)) <$>
        (simulateQ (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run (project state) := by
  have observed := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (ctxInterpreter modes replace setup codec) work).run state.2)
      (CborRawRecordFlat.clientImpl_send env codec route handle plaintext state.1)
  rw [native_program_run]
  cases refused : sendRefusal (n := n) handle plaintext state.1.1.2 with
  | none =>
    rw [refused] at observed
    simp only
    rw [original_program_run]
    simpa only [simulateQ_map, StateT.run_map, Functor.map_map,
      CborRawRecordFlat.clientWithShell, CborRawRecordFlat.clientProject, project, withShell] using observed
  | some reply =>
    rw [refused] at observed
    simpa only [refused, simulateQ_pure, StateT.run_pure, map_pure] using observed

theorem nextSend_length (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (reply₁ reply₂ : Option RawCtxSourceSend.Encrypted) (shell : CborRecordWorldClient.Shell) :
    nextSend (n := n) handle first reply₁ shell = nextSend (n := n) handle second reply₂ shell := by
  cases handle with
  | peer keyId => exact CborRawRecordFlat.next_length (n := n) (.peer keyId) first second length reply₁ reply₂ shell
  | owner owner => exact CborRawRecordFlat.next_length (n := n) (.owner owner) first second length reply₁ reply₂ shell

/-- Zeroed hidden sends depend on the plaintext length, including their native CBOR admission and cursor update. -/
theorem nativeImpl_send_zeros (modes : Label n → KeyMode) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (state : NativeState n E) (notKnown : ¬KnownAt state.1.2 handle) :
    (simulateQ (nativeImpl modes zeros setup codec route env) (PqxdhDeploymentSecrecy.send handle first)).run state =
      (simulateQ (nativeImpl modes zeros setup codec route env) (PqxdhDeploymentSecrecy.send handle second)).run state := by
  rw [native_send_run, native_send_run, CborRawRecordFlat.refusal_length handle first second length]
  cases refused : sendRefusal (n := n) handle second state.1.1.2 with
  | some reply => rfl
  | none =>
    rw [← PqxdhRecordLiftFlat.nativeImpl_send_zeros modes setup codec route env handle first second length (project state) notKnown]
    apply map_congr
    intro result
    rw [nextSend_length handle first second length result.1 result.1]

/-- Each actual ledger byte and test-bit coin is forwarded unchanged and leaves the cursor untouched. -/
theorem nativeImpl_coin (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (coin : Nat) (state : NativeState n E) :
    (nativeImpl modes replace setup codec route env (.inl coin)).run state =
      (fun reply => (reply, (state.1, coinStep state.2))) <$> (unifSpec.query coin : ProbComp _) := by
  rw [CborRawRecordFlat.nativeImpl_run]
  simp only [native, coinLift, StateT.run, map_eq_bind_pure_comp]
  rfl

end BeaconcryptCore.Computational.CborRawRecordFlatSemantics

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlatSemantics.native_program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlatSemantics.native_program_run

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlatSemantics.native_send_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlatSemantics.native_send_run

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlatSemantics.nextSend_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlatSemantics.nextSend_length

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlatSemantics.nativeImpl_send_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlatSemantics.nativeImpl_send_zeros

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlatSemantics.nativeImpl_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlatSemantics.nativeImpl_coin
