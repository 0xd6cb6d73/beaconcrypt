-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger

/-! Exact frozen record binding target from the complete initialized adaptive source execution. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Every supported actual cross-handle acceptance supplies a retained commitment conflict, with no ledger premise. -/
theorem ctxRun_cross_conflict (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (crossed : CrossAccept codec route (ctxView result)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2 := by
  exact PqxdhRecordFactsBindingEvent.cross_accept_conflict codec route (ctxView result) result.1.2 result.2 rfl
    (PqxdhRecordFactsBindingKnownLedger.ctxView_ledgerEvidence modes ideal replace setup codec route readback
      env serverKid bounds mode adversary result supported) crossed

/-- Exact cross-accept probability in the original complete adaptive run is bounded by the source-derived two-class collision term. -/
theorem ctxRun_cross_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    𝒟[(fun result => crossEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤
      ((budget.sends * (budget.sends + sharedHashTotal ⟨budget, startup, allowance, bounds, n, 0⟩) : Nat) : ENNReal) /
        (2 : ENNReal)^512 := by
  refine le_trans ?_ (PqxdhRecordFactsBindingProbability.run_conflict_bound modes ideal replace setup codec route env
    startup allowance framed serverKid bounds mode budget adversary respects 0)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  exact fun result supported crossed => @decide_eq_true _ (Classical.propDecidable _)
    (ctxRun_cross_conflict modes ideal replace setup codec route readback env serverKid bounds mode adversary
      result supported (@of_decide_eq_true _ (Classical.propDecidable _) crossed))

/-- The complete actual run satisfies the unchanged frozen binding loss, without a selected-honest-handle premise. -/
theorem ctxRun_binding_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    𝒟[(fun result => crossEvent codec route (ctxView result)) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤
      bindingTerm ⟨budget, startup, allowance, bounds, n, 0⟩ :=
  le_trans (ctxRun_cross_bound modes ideal replace setup codec route readback env startup allowance framed
    serverKid bounds mode budget adversary respects)
    (PqxdhRecordFactsBindingProbability.collision_le_binding ⟨budget, startup, allowance, bounds, n, 0⟩)

/-- The integrity replay world satisfies the frozen cross-handle binding term in either observation mode. -/
theorem idealAuth_binding (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    𝒟[(fun result => crossEvent codec route (ctxView result)) <$>
      idealAuth setup codec route env serverKid bounds mode adversary] {true} ≤
      bindingTerm ⟨budget, startup, allowance, bounds, n, 0⟩ :=
  ctxRun_binding_bound (fun _ => .replay) (by intro label; decide) id setup codec route readback env
    startup allowance framed serverKid bounds mode budget adversary respects

/-- The mode-selected ideal record world satisfies the same frozen term, including random ciphertexts in mode P. -/
theorem idealRecords_binding (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    𝒟[(fun result => crossEvent codec route (ctxView result)) <$>
      idealRecords setup codec route env serverKid bounds mode adversary] {true} ≤
      bindingTerm ⟨budget, startup, allowance, bounds, n, 0⟩ :=
  ctxRun_binding_bound (fun _ => recordMode mode) (by intro label; cases mode <;> decide) id setup codec route
    readback env startup allowance framed serverKid bounds mode budget adversary respects

/-- The exact frozen binding statement, with its original contract and both complete ideal worlds. -/
theorem bindingStatement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) :
    BindingStatement setup codec route serverKid bounds n bindingTerm :=
  fun readback {_ _} env startup allowance framed mode adversary budget respects =>
    ⟨idealAuth_binding setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects,
     idealRecords_binding setup codec route readback env startup allowance framed serverKid bounds mode budget adversary respects⟩

/-- The unchanged global ideal-record binding target is discharged. -/
theorem bindingTarget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) :
    BindingTarget setup codec route serverKid bounds n :=
  bindingStatement setup codec route serverKid bounds

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.ctxRun_cross_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.ctxRun_cross_conflict

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.ctxRun_cross_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.ctxRun_cross_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.ctxRun_binding_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.ctxRun_binding_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.idealAuth_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.idealAuth_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.idealRecords_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.idealRecords_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.bindingStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.bindingStatement

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.bindingTarget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingGlobal.bindingTarget
