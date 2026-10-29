-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordEntropyWorld

/-! Fresh-message entropy after an arbitrary concrete public startup, including shared-CTX hashing. The original fresh ledger begins empty after that startup; every successful branch retains its exact reached cursor, native state and CTX cache. Averaging introduces no session or startup-query multiplier. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordEntropyPreamble
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (FreshBounds ModeSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftFlat (zeros zeros_length)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {base : OracleSpec ι}

/-- Hiding-invariant observations commute with actual random-record plaintext replacement at the reached initialized World state. -/
theorem law_zeros (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (created : PqxdhLiveServerConstruction.Created Unit)
    (state : CborRawRecordFlat.NativeState n E) (observe : View n E X → Bool)
    (invariant : ∀ first second, hidingView first = hidingView second → observe first = observe second) :
    (fun result => observe (ctxView result)) <$>
      CborRawRecordEntropyInitial.run (fun _ => .random) id setup codec route env serverKid bounds .P adversary created state =
      (fun result => observe (ctxView result)) <$>
        CborRawRecordEntropyInitial.run (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary created state := by
  let factor : HidingView n E X → Bool := fun projection =>
    @dite _ (∃ view, hidingView view = projection) (Classical.propDecidable _) (fun witness => observe witness.choose)
      (fun _ => false)
  have factored : ∀ view, observe view = factor (hidingView view) := fun view => by
    have existsView : ∃ other, hidingView other = hidingView view := ⟨view, rfl⟩
    simp only [factor, existsView]
    exact invariant _ _ (Eq.symm (Exists.choose_spec (p := fun other => hidingView other = hidingView view) _))
  have replaced := CborRawRecordEntropyWorld.hiding_replace setup codec route env serverKid bounds
    adversary created state id zeros (fun message => (zeros_length message).symm)
  calc _ = factor <$> ((fun result => hidingView (ctxView result)) <$>
        CborRawRecordEntropyInitial.run (fun _ => .random) id setup codec route env serverKid bounds .P adversary created state) := by
        rw [Functor.map_map]
        exact congrArg (fun function => function <$>
          CborRawRecordEntropyInitial.run (fun _ => .random) id setup codec route env serverKid bounds .P adversary created state)
          (funext fun result => factored (ctxView result))
    _ = factor <$> ((fun result => hidingView (ctxView result)) <$>
        CborRawRecordEntropyInitial.run (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary created state) := by rw [replaced]
    _ = _ := by
        rw [Functor.map_map]
        exact congrArg (fun function => function <$>
          CborRawRecordEntropyInitial.run (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary created state)
          (funext fun result => (factored (ctxView result)).symm)

/-- Fresh guessing retains the byte-accurate bound after the actual public startup cache has been populated. -/
theorem fresh_bytes (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (created : PqxdhLiveServerConstruction.Created Unit) (state : CborRawRecordFlat.NativeState n E) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$>
      CborRawRecordEntropyInitial.run (fun _ => .random) id setup codec route env serverKid bounds .P adversary created state] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [law_zeros setup codec route env serverKid bounds adversary created state _ (PqxdhRecordLiftFresh.freshEvent_hiding claim)]
  exact CborRawRecordEntropyInitial.fresh_zeros_bytes (fun _ => .random) setup codec route env serverKid bounds .P adversary claim created state

noncomputable def run (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit) × CborRawRecordFlat.NativeState n E))
    (adversary : PqxdhLiveServerConstruction.Created Unit → E → OracleComp (ModeSpec .P) X) :
    ProbComp (Client n E X × CtxPrivate n) := do
  let started ← startup
  match started.1 with
  | none => pure ((none, started.2.1.2), started.2.2)
  | some created =>
      CborRawRecordEntropyInitial.run (fun _ => .random) id setup codec route env serverKid bounds .P
        (adversary created started.2.1.1.1) created started.2

/-- Averaging the actual public startup and all its cache effects preserves the same fresh-message entropy bound. -/
theorem startup_fresh_bytes (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit) × CborRawRecordFlat.NativeState n E))
    (adversary : PqxdhLiveServerConstruction.Created Unit → E → OracleComp (ModeSpec .P) X)
    (claim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$> run setup codec route env serverKid bounds startup adversary] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  unfold run
  rw [map_bind, ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_le_of_forall_le_of_support
  intro started _supported
  cases initialized : started.1 with
  | none => simp [freshEvent, FreshHit, ctxView, viewOf]
  | some created =>
      dsimp only
      rw [prEvent_eq_evalDist_singleton]
      exact fresh_bytes setup codec route env serverKid bounds (adversary created started.2.1.1.1) claim created started.2

end BeaconcryptCore.Computational.CborRawRecordEntropyPreamble
/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyPreamble.law_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyPreamble.law_zeros
/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyPreamble.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyPreamble.fresh_bytes
/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyPreamble.startup_fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyPreamble.startup_fresh_bytes
