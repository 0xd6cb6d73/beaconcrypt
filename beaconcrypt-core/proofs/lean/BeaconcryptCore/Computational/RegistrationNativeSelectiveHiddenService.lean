-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceDemand
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds

/-! Selective G3 hides only protected inputs carrying the selected uniform KEM word. Other protected G2 inputs keep their own persistent locally sampled uniform108-byte outputs and use known-kernel continuations. Off-protected inputs retain the actual deterministic source schedule. Thus unrelated repeated inputs are never changed into hidden-role refusals. The environment owns nonselected outputs but no selected hidden64-byte record seed. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeRelatedFamily (Message)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhServerAuthKeySchedule (Output)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeHiddenService (coins)
variable {n : Nat}

abbrev KnownOracle := Pqxdh.Bytes →ₒ Output
abbrev State (n : Nat) := RegistrationNativeHiddenService.State n × KnownOracle.QueryCache

def initial : State n := (RegistrationNativeHiddenService.initial, ∅)

def selected (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (bytes : Pqxdh.Bytes) : Bool :=
  inside bytes && decide (PqxdhJointGapDh.readDh 160 bytes = some candidate)

def onHidden {Value : Type} (work : StateT (RegistrationNativeHiddenService.State n) (OracleComp (EnvEffects n)) Value) :
    StateT (State n) (OracleComp (EnvEffects n)) Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

noncomputable def known (bytes : Pqxdh.Bytes) : StateT (State n) (OracleComp (EnvEffects n)) Output := fun before =>
  match before.2 bytes with
  | some output => pure (output, before)
  | none => (fun output => (output, (before.1, before.2.cacheQuery bytes output))) <$>
      simulateQ coins ($ᵗ Output)

def prepare (input : Message → Option Pqxdh.Bytes) (message : Message) :
    StateT (State n) (OracleComp (EnvEffects n)) (Option Message) :=
  onHidden (RegistrationNativeHiddenService.prepare input message)

noncomputable def demand (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message) :
    StateT (State n) (OracleComp (EnvEffects n)) (Option (Choice n)) := fun before =>
  if before.1.prepared message then
    match input message with
    | none => (onHidden (RegistrationNativeHiddenService.demand source input (selected inside candidate) message)).run before
    | some bytes =>
        if inside bytes && !(selected inside candidate bytes) then
          (fun result => (some (.known result.1), result.2)) <$>
            (known bytes).run ({ before.1 with demands := before.1.demands + 1 }, before.2)
        else (onHidden (RegistrationNativeHiddenService.demand source input (selected inside candidate) message)).run before
  else (onHidden (RegistrationNativeHiddenService.demand source input (selected inside candidate) message)).run before

/-- A selected address is genuinely protected and has the exact selected final32-byte KEM word. -/
theorem selected_iff (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (bytes : Pqxdh.Bytes) :
    selected inside candidate bytes = true ↔ inside bytes = true ∧ PqxdhJointGapDh.readDh 160 bytes = some candidate := by
  simp only [selected, Bool.and_eq_true, decide_eq_true_eq]

/-- A nonselected protected cache hit retains its full native108-byte output and all private service fields. -/
theorem known_hit (bytes : Pqxdh.Bytes) (before : State n) (output : Output) (cached : before.2 bytes = some output) :
    (known bytes).run before = pure (output, before) := by simp only [known, StateT.run, cached]

/-- A fresh nonselected protected input samples a locally owned complete108-byte output through the actual environment coins. -/
theorem known_miss (bytes : Pqxdh.Bytes) (before : State n) (missing : before.2 bytes = none) :
    (known bytes).run before =
      (fun output => (output, (before.1, before.2.cacheQuery bytes output))) <$> simulateQ coins ($ᵗ Output) := by
  simp only [known, StateT.run, missing]

/-- Selected inputs still invoke exactly the original hidden44 service, preserving its actual allocation, failures and source gates. -/
theorem demand_selected (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before : State n) (bytes : Pqxdh.Bytes) (prepared : before.1.prepared message = true)
    (realized : input message = some bytes) (hidden : selected inside candidate bytes = true) :
    (demand source input inside candidate message).run before =
      (onHidden (RegistrationNativeHiddenService.demand source input (selected inside candidate) message)).run before := by
  simp only [demand, StateT.run, prepared, ite_true, realized, hidden, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]

/-- Ordinary protected inputs retain an independent cached known108 reply instead of consuming a hidden slot or role. -/
theorem demand_other (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : Message)
    (before : State n) (bytes : Pqxdh.Bytes) (prepared : before.1.prepared message = true)
    (realized : input message = some bytes) (protectedInput : inside bytes = true)
    (other : selected inside candidate bytes = false) :
    (demand source input inside candidate message).run before =
      (fun result => (some (.known result.1), result.2)) <$>
        (known bytes).run ({ before.1 with demands := before.1.demands + 1 }, before.2) := by
  simp only [demand, StateT.run, prepared, ite_true, realized, protectedInput, other, Bool.not_false, Bool.and_self]

end BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.selected_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.selected_iff
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.known_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.known_hit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.known_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.known_miss
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.demand_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.demand_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.demand_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService.demand_other
