-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordEntropyAveraging
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFreshCoupling

/-! Byte-shift symmetry begins at any concrete initialized cursor, record control and shared CTX state. This permits a real public startup hash in the same cache before the original empty secrecy ledger begins; it neither resamples that cache nor moves private fresh-message draws into startup. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros)
open PqxdhRecordLiftFresh (hitAt shiftedHit extend shiftLedger_empty hitAt_shift)
open RegistrationNativePlatformGatedRecordFreshCoupling (FreshRelated FreshEscaped freshEscaped_keep step_couple)
variable {n : Nat} {ι KemSK Reader Response E X Failure : Type} {base : OracleSpec ι}

noncomputable def run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (created : PqxdhLiveServerConstruction.Created Unit)
    (state : CborRawRecordFlat.NativeState n E) : ProbComp (Client n E X × CtxPrivate n) :=
  (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
    (result.1, result.2.1), result.2.2.1.1.1), result.2.2.1.2), result.2.2.2)) <$>
    (simulateQ (RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKid bounds)
      (asModeO mode adversary)).run (PqxdhDeploymentSecrecy.Ledger.empty, state)

/-- The original fresh draw has byte-shift symmetry after an arbitrary shared-World startup state. -/
theorem world_couple (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (created : PqxdhLiveServerConstruction.Created Unit) (state : CborRawRecordFlat.NativeState n E)
    (index length : Nat) (offsets : Fin length → Fin 256) :
    Swap (fun first second => hitAt claim index length (ctxView first) =
      shiftedHit bounds claim index length offsets (ctxView second))
      (run modes zeros setup codec route env reserve serverKid bounds mode adversary created state)
      (run modes zeros setup codec route env reserve serverKid bounds mode adversary created state) := by
  unfold run
  refine (Swap.simulateQ_run (RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes zeros setup codec route env reserve serverKid bounds)
    (RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes zeros setup codec route env reserve serverKid bounds)
    (FreshRelated bounds index (extend offsets)) (FreshEscaped index) (FreshEscaped index)
    (freshEscaped_keep modes zeros setup codec route env reserve serverKid bounds index)
    (freshEscaped_keep modes zeros setup codec route env reserve serverKid bounds index)
    (step_couple modes setup codec route env reserve serverKid bounds index (extend offsets))
    (asModeO mode adversary) _ _
    ⟨rfl, (shiftLedger_empty index (extend offsets)).symm, fun _ member => absurd member List.not_mem_nil⟩).map ?_
  rintro ⟨first, ledger, native⟩ ⟨second, otherLedger, otherNative⟩ (⟨sameValue, sameNative, sameLedger, long⟩ | ⟨escapedFirst, escapedSecond⟩)
  · dsimp only at sameValue sameNative sameLedger long
    subst second otherNative otherLedger
    exact hitAt_shift bounds claim index length offsets first ledger native.1.1.1 _ _ _ long
  · exact (PqxdhRecordLiftFresh.hitAt_escaped claim index length first ledger (CborRawRecordFlat.project native) _ _ escapedFirst).trans
      (PqxdhRecordLiftFresh.shiftedHit_escaped bounds claim index length offsets second otherLedger
        (CborRawRecordFlat.project otherNative) _ _ escapedSecond).symm

/-- The byte-accurate bound holds pointwise in the actual initialized CTX cache and public native state. -/
theorem fresh_zeros_bytes (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (created : PqxdhLiveServerConstruction.Created Unit) (state : CborRawRecordFlat.NativeState n E) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$>
      run modes zeros setup codec route env reserve serverKid bounds mode adversary created state] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ :=
  CborRawRecordEntropyAveraging.fresh_bound bounds claim _
    (fun index length offsets => world_couple modes setup codec route env reserve serverKid bounds mode adversary claim created state index length offsets)

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial.world_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial.fresh_zeros_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial.fresh_zeros_bytes
