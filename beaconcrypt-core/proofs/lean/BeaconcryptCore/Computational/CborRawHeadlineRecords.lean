-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawHeadlineSlots

/-! The concrete raw record reductions transfer Boolean permitted-view events to the actual replay or random-ciphertext worlds. Every loss names the real cursor client, counted service bills and explicit cryptographic reduction. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineRecords
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment EffectKind Frame)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhRecordLiftIdeal (View chainView ctxView)
open CborRawRecordLiftBounds (client)
open CborRawRecordLiftCrypto (chainLoss authLoss privacyLoss)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

noncomputable def randomLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (event : View n E X → Bool) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) : ℝ≥0∞ :=
  chainLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget
    (fun view => pure (event view)) setup.hmac +
  authLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget
    (fun view => pure (event view)) fallback
    (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, 0⟩)
    (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, 0⟩) +
  privacyLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget
    (fun view => pure (event view))

/-- A view event on the actual all-real raw world is bounded by its actual random-record probability and explicit three-part reduction loss. -/
theorem random_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (event : View n E X → Bool)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[event <$> (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))] {true} ≤
    𝒟[event <$> (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))] {true} +
    randomLoss setup codec route env serverKid bounds mode budget adversary event startup allowance fallback := by
  have close := CborRawRecordLiftCrypto.record_random_bound setup codec route env startup allowance framed serverKid
    bounds mode budget adversary respects (fun view => pure (event view)) 0
    (fun _ => by trivial) setup.hmac correct fallback
  apply (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance _ _).trans
  apply add_le_add le_rfl
  simpa only [randomLoss, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using close

noncomputable def integrityLoss (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (event : View n E X → Bool) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) : ℝ≥0∞ :=
  chainLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget
    (fun view => pure (event view)) setup.hmac +
  authLoss setup codec route (client env setup.source.crypto codec serverKid bounds mode adversary) budget
    (fun view => pure (event view)) fallback
    (PqxdhRecordLiftCtxBills.programBill .hash ⟨budget, startup, allowance, bounds, n, 0⟩)
    (PqxdhRecordLiftCtxBills.programBill .raw ⟨budget, startup, allowance, bounds, n, 0⟩)

/-- The actual all-real raw record event transfers to replay acceptance with explicit chain and integrity losses. -/
theorem integrity_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (event : View n E X → Bool)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    𝒟[event <$> (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))] {true} ≤
    𝒟[event <$> (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .replay) id setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))] {true} +
    integrityLoss setup codec route env serverKid bounds mode budget adversary event startup allowance fallback := by
  have close := CborRawRecordLiftCrypto.record_auth_bound setup codec route env startup allowance framed serverKid
    bounds mode budget adversary respects (fun view => pure (event view)) 0
    (fun _ => by trivial) setup.hmac correct fallback
  apply (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance _ _).trans
  apply add_le_add le_rfl
  simpa only [integrityLoss, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using close

/-- Actual raw real and random-record permitted-view probabilities differ by the explicit three-part primitive loss. -/
theorem random_close (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (event : View n E X → Bool)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    ENNReal.ofReal |(𝒟[event <$> (chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))] {true}).toReal -
      (𝒟[event <$> (ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec route
      (client env setup.source.crypto codec serverKid bounds mode adversary))] {true}).toReal| ≤
    randomLoss setup codec route env serverKid bounds mode budget adversary event startup allowance fallback := by
  have close := CborRawRecordLiftCrypto.record_random_bound setup codec route env startup allowance framed serverKid
    bounds mode budget adversary respects (fun view => pure (event view)) 0
    (fun _ => by trivial) setup.hmac correct fallback
  simpa only [randomLoss, ProbComp.boolDistance, Functor.map_map, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind] using close

end BeaconcryptCore.Computational.CborRawHeadlineRecords

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineRecords.random_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineRecords.random_le

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineRecords.integrity_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineRecords.integrity_le

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineRecords.random_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineRecords.random_close
