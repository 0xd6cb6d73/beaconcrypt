-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordHiding
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-! Hiding-invariant observations transfer to zeroed hidden plaintexts in the actual cursor-filtered random-record world. The complete original World program, including private secrecy-ledger draws, lies inside the cursor client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordHidingLaw
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros zeros_length)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

noncomputable def ctxRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :=
  PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
    (CborRecordWorldClient.client (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary))

theorem law_zeros (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (observe : View n E X → Bool)
    (invariant : ∀ first second, hidingView first = hidingView second → observe first = observe second) :
    (fun result => observe (ctxView result)) <$> ctxRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary =
      (fun result => observe (ctxView result)) <$>
        ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary := by
  let factor : HidingView n E X → Bool := fun projection =>
    @dite _ (∃ view, hidingView view = projection) (Classical.propDecidable _) (fun h => observe h.choose)
      (fun _ => false)
  have factored : ∀ view, observe view = factor (hidingView view) := fun view => by
    have h : ∃ other, hidingView other = hidingView view := ⟨view, rfl⟩
    simp only [factor, h]
    exact invariant _ _ (Eq.symm (Exists.choose_spec (p := fun other => hidingView other = hidingView view) _))
  have replaced := CborRawRecordHiding.hiding_replace setup codec route env serverKid bounds adversary id zeros
    fun message => (zeros_length message).symm
  change (fun result => hidingView (ctxView result)) <$>
      ctxRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary =
    (fun result => hidingView (ctxView result)) <$>
      ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary at replaced
  calc (fun result => observe (ctxView result)) <$> ctxRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary
      = factor <$> ((fun result => hidingView (ctxView result)) <$>
          ctxRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary) := by
        rw [Functor.map_map]
        exact congrArg (fun f => f <$> ctxRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary)
          (funext fun result => factored (ctxView result))
    _ = factor <$> ((fun result => hidingView (ctxView result)) <$>
          ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P adversary) := by
        rw [replaced]
    _ = _ := by
        rw [Functor.map_map]
        exact congrArg (fun f => f <$> ctxRun (fun _ => .random) zeros setup codec route env serverKid bounds .P
          adversary) (funext fun result => (factored (ctxView result)).symm)


end BeaconcryptCore.Computational.CborRawRecordHidingLaw

/-- info: 'BeaconcryptCore.Computational.CborRawRecordHidingLaw.law_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordHidingLaw.law_zeros
