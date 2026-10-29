-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPoolCompiler
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser

/-! The raw anomaly predictor runs the actual native CBOR pool game with the original secrecy ledger. It reads the first successful finish preceding the selected raw accept from that original transcript. The KEM challenge ciphertext is used only by the final comparison, after the predictor's behavior. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyPool
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhKemIndCca (MlKem768Ciphertext)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

noncomputable def atPool (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ProbComp (Option MlKem768Ciphertext) :=
  (fun result => PqxdhDeploymentIdealGuess.guessCt (CborTaggedSimulation.boundaryWire wire parse)
    target result.1.2.transcript) <$>
      (simulateQ (CborRawPoolCompiler.native setup wire parse checks created.seed (parameters.pool target))
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
          setup.serverKeyId bounds (PqxdhDeploymentInterface.asModeO mode adversary))).run
        (PqxdhDeploymentNative.initial created)

noncomputable def fixed (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ProbComp (Option MlKem768Ciphertext) := do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit 0 setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure none
  | some created => atPool setup wire parse checks target parameters created bounds mode adversary

noncomputable def hit (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) : ProbComp Bool := do
  let parameters ← drawParams setup count
  let guessed ← fixed setup wire parse checks target parameters ensureInit runtime bounds mode adversary
  pure (decide (guessed = some parameters.challenge))

/-- The actual native pool predictor never reads the later challenge ciphertext. -/
theorem at_challenge (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (ciphertext : MlKem768Ciphertext)
    (created : PqxdhLiveServerConstruction.Created Unit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    atPool setup wire parse checks target {parameters with challenge := ciphertext} created bounds mode adversary =
      atPool setup wire parse checks target parameters created bounds mode adversary := rfl

/-- Server construction and the complete original raw ledger do not read the comparison ciphertext. -/
theorem fixed_challenge (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (ciphertext : MlKem768Ciphertext)
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    fixed setup wire parse checks target {parameters with challenge := ciphertext} ensureInit runtime bounds mode adversary =
      fixed setup wire parse checks target parameters ensureInit runtime bounds mode adversary := rfl

end BeaconcryptCore.Computational.CborRawAnomalyPool

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPool.at_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPool.at_challenge
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPool.fixed_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPool.fixed_challenge
