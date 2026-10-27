-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsLaterFlat
import BeaconcryptCore.Computational.PqxdhRecordFactsLaterTargets
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterHiding
import BeaconcryptCore.Computational.PqxdhRecordLiftLor

/-! The later left-or-right fact, with the run bit-swap followed by the complete E-only post execution. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat PqxdhRecordLiftSwap
open PqxdhRecordLiftLor PqxdhRecordLiftLaterWorlds PqxdhRecordFactsLaterFlat PqxdhRecordFactsLaterTargets
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhDeploymentLater (PostSpec)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Out R : Type}

/-- An admitted test on a caller-known handle remains excluded after the post phase: the run ledger is fixed and caller-known kernels persist. -/
theorem post_escaped (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (adversary : OracleComp PostSpec Out)
    (ledger : Ledger) (state : NativeState n E) (escaped : Escaped setup.source.crypto codec serverKid (ledger, state))
    (result : Out × NativeState n E) (reached : result ∈ support (postRun modes replace setup codec route env adversary state)) :
    Escaped setup.source.crypto codec serverKid (ledger, result.2) := by
  obtain ⟨before, entry, after, handle, left, right, transcript, query, admitted, known⟩ := escaped
  exact ⟨before, entry, after, handle, left, right, transcript, query, admitted,
    postRun_known modes replace setup codec route env adversary state handle known result reached⟩

/-- Append the E-only post phase to related or escaped run results. The public output and complete native state agree on the related branch; the two escaped branches still cannot satisfy hidden-test eligibility. -/
theorem post_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Std.U64) (reveal : E → R) (second : X → R → OracleComp PostSpec Out)
    (decision eligible : PublicHiding n E Out → Bool)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (firstResult secondResult : X × Ledger × NativeState n E)
    (related : SimRel Related (Escaped setup.source.crypto codec serverKid)
      (Escaped setup.source.crypto codec serverKid) firstResult secondResult) :
    Swap (fun r₁ r₂ => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView r₁) =
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView r₂))
      ((fun later => ((some (created, (later.1, firstResult.2.1), later.2.1.1), later.2.1.2), later.2.2)) <$>
        postRun modes zeros setup codec route env
          (second firstResult.1 (reveal firstResult.2.2.1.1)) firstResult.2.2)
      ((fun later => ((some (created, (later.1, secondResult.2.1), later.2.1.1), later.2.1.2), later.2.2)) <$>
        postRun modes zeros setup codec route env
          (second secondResult.1 (reveal secondResult.2.2.1.1)) secondResult.2.2) := by
  rcases firstResult with ⟨x₁, ledger₁, state₁⟩
  rcases secondResult with ⟨x₂, ledger₂, state₂⟩
  rcases related with ⟨hx, hstate, hledger, inv⟩ | ⟨escaped₁, escaped₂⟩
  · dsimp only at hx hstate hledger
    subst x₂ state₂ ledger₂
    refine (Swap.refl (postRun modes zeros setup codec route env (second x₁ (reveal state₁.1.1)) state₁)
      (R := Eq) fun _ => rfl).map ?_
    rintro later _ rfl
    exact (lorGuess_flip setup.source.crypto codec serverKid decision eligible later.1 ledger₁ later.2.1.1 _ _ _).symm
  · refine Swap.escape _ _ fun a ha b hb => ?_
    rw [support_map] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact (lorGuess_escaped setup.source.crypto codec serverKid decision eligible a.1 ledger₁ a.2 _ _
      (post_escaped modes zeros setup codec route env serverKid _ ledger₁ state₁ escaped₁ a ha)).trans
      (lorGuess_escaped setup.source.crypto codec serverKid _ eligible b.1 ledger₂ b.2 _ _
        (post_escaped modes zeros setup codec route env serverKid _ ledger₂ state₂ escaped₂ b hb)).symm

/-- The run-phase bit-swap coupling survives the complete E-only post phase. The post output, environment and shared-cache evolution remain in the coupled execution. -/
theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (reveal : E → R) (first : OracleComp (ModeSpec .P) X) (second : X → R → OracleComp PostSpec Out)
    (decision eligible : PublicHiding n E Out → Bool) :
    Swap (fun r₁ r₂ => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView r₁) =
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView r₂))
      (laterCtxRun setup codec route env serverKid bounds .P reveal first second modes zeros)
      (laterCtxRun setup codec route env serverKid bounds .P reveal first second modes zeros) := by
  rw [laterCtxRun_flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨_ | ⟨created, initial⟩, control⟩, secret⟩
  · exact .pure _ _ (by simp [ctxView, viewOf, lorGuess, TestsHidden])
  · refine (Swap.refl (install modes zeros setup codec route created control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env serverKid bounds)
      (fullImpl modes zeros setup codec route env serverKid bounds) Related
      (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid)
      (escaped_keep modes zeros setup codec route env serverKid bounds)
      (escaped_keep modes zeros setup codec route env serverKid bounds)
      (step_couple modes setup codec route env serverKid bounds) (asModeO .P first) _ _
      ⟨rfl, rfl, ledgerInv_empty⟩).bind ?_
    exact post_couple modes setup codec route env serverKid reveal second decision eligible
      (PqxdhRegistrationJointServerBirth.encode created)

/-- In the zeroed later world every public decision guesses the test bit with exactly half the probability of hidden-test eligibility. -/
theorem lor_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (reveal : E → R) (first : OracleComp (ModeSpec .P) X) (second : X → R → OracleComp PostSpec Out)
    (decision eligible : PublicHiding n E Out → Bool) :
    𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds .P reveal first second modes zeros] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds .P reveal first second modes zeros] {true} := by
  have same := (world_couple modes setup codec route env serverKid bounds reveal first second decision eligible).evalDist_map
    (fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result))
    (fun result => lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible
      (ctxView result)) fun _ _ related => related
  have split : (fun result : Client n E Out × CtxPrivate n =>
      lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) =
      fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result) ||
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView result) :=
    funext fun result => (lorEligible_split setup.source.crypto codec serverKid decision eligible (ctxView result)).1
  rw [split, evalDist_or _ _ _ fun result =>
    (lorEligible_split setup.source.crypto codec serverKid decision eligible (ctxView result)).2, ← same, ← two_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- Observations that factor through the hiding projection have exactly the same computation law after zeroing the hidden plaintexts, including the whole post phase. -/
theorem law_zeros (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (reveal : E → R) (first : OracleComp (ModeSpec .P) X) (second : X → R → OracleComp PostSpec Out)
    (observe : View n E Out → Bool)
    (invariant : ∀ a b, hidingView a = hidingView b → observe a = observe b) :
    (fun result => observe (ctxView result)) <$>
        laterIdealRecords setup codec route env serverKid bounds .P reveal first second =
      (fun result => observe (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) zeros := by
  let factor : HidingView n E Out → Bool := fun projection =>
    @dite _ (∃ view, hidingView view = projection) (Classical.propDecidable _) (fun h => observe h.choose)
      (fun _ => false)
  have factored : ∀ view, observe view = factor (hidingView view) := fun view => by
    have h : ∃ other, hidingView other = hidingView view := ⟨view, rfl⟩
    simp only [factor, h]
    exact invariant _ _ (Eq.symm (Exists.choose_spec (p := fun other => hidingView other = hidingView view) _))
  have replaced := PqxdhRecordLiftLaterHiding.later_hiding_replace setup codec route serverKid bounds env
    reveal first second id zeros fun message => (zeros_length message).symm
  simpa only [Functor.map_map, ← factored, laterIdealRecords, recordMode] using congrArg (fun work => factor <$> work) replaced

/-- The frozen later left-or-right target, for every E-only reveal and unrestricted post adversary. No cryptographic, `Frame` or budget premise. -/
theorem later_idealRecords_lor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (n : Nat) :
    LaterLorStatement setup codec route serverKid bounds n := by
  intro E X Out R env reveal first second decision eligible
  rw [law_zeros setup codec route env serverKid bounds reveal first second _
      (lorGuess_hiding setup.source.crypto codec serverKid decision eligible),
    law_zeros setup codec route env serverKid bounds reveal first second _
      (lorEligible_hiding setup.source.crypto codec serverKid eligible)]
  exact lor_zeros (fun _ => .random) setup codec route env serverKid bounds reveal first second decision eligible

end BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.post_escaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.post_escaped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.post_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.post_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.world_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.lor_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.lor_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.law_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.law_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.later_idealRecords_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor.later_idealRecords_lor
