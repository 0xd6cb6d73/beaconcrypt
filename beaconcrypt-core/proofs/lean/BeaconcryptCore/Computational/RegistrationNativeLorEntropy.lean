-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLorTransport
import BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized
import BeaconcryptCore.Computational.RegistrationNativeRecordPackage

/-! Native canonical LR eligibility and the original test-bit win have exact all-random fairness after arbitrary reached startup effects. The bridge restores native mode-P observations and every admitted test from the same transport ledger, retaining the original test bit and physical slot map. The analysis projection is used only through these proved public factors. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLorEntropy
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRecordPackage (View nativeView)
variable {n : Nat} {ι KemSK E Value : Type} {base : OracleSpec ι}

noncomputable def analysisEligible (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value)
    (target : Fin budget.accept × Fin budget.capacity)
    (projection : PqxdhRecordLiftIdeal.PublicHiding n (RegistrationNativeEntropyPort.State E) Value) : Bool :=
  projection.1.elim false fun finished => RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target
    (finished.1, RegistrationNativeLorTransport.representative (RegistrationNativePublicObservation.restoreFrom [] finished.2.1).2)

def analysisDecision (guess : Value → Bool)
    (projection : PqxdhRecordLiftIdeal.PublicHiding n (RegistrationNativeEntropyPort.State E) Value) : Bool :=
  projection.1.elim false fun finished => guess finished.1

def HiddenTests (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (finished : PqxdhRegistrationJointServerBirth.ClientCreated Unit × (Value × RegistrationNativeLedger.State) × E)
    (slots : PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n)) : Prop :=
  finished.2.1.2.ledger.test.isSome ∧ RegistrationNativeLorCanonical.OnTests crypto wire serverKeyId
    finished.2.1.2.ledger.transcript (fun handle => (slots handle).isSome)

noncomputable def eligibleView (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value)
    (target : Fin budget.accept × Fin budget.capacity) (view : View n E Value) : Bool :=
  view.result.elim false fun finished => RegistrationNativeLorCanonical.j crypto wire serverKeyId budget filter target finished.2.1 &&
    @decide (HiddenTests crypto wire serverKeyId finished view.slots) (Classical.propDecidable _)

noncomputable def winningView (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (view : View n E Value) : Bool :=
  view.result.elim false fun finished => RegistrationNativeLorCanonical.w crypto wire serverKeyId budget filter guess target finished.2.1 &&
    @decide (HiddenTests crypto wire serverKeyId finished view.slots) (Classical.propDecidable _)

noncomputable def eligible (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value)
    (target : Fin budget.accept × Fin budget.capacity) (result : RegistrationNativeEntropyRun.Result n E Value) : Bool :=
  eligibleView crypto wire serverKeyId budget filter target (nativeView result.1 result.2.base.produced)

noncomputable def winning (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (result : RegistrationNativeEntropyRun.Result n E Value) : Bool :=
  winningView crypto wire serverKeyId budget filter guess target (nativeView result.1 result.2.base.produced)

/-- Native hidden-test eligibility is the literal old fair-game event after exact restoration. -/
theorem project_eligible (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (old : PqxdhRecordLiftIdeal.Client n (RegistrationNativeEntropyPort.State E) Value × PqxdhRecordLiftIdeal.CtxPrivate n) :
    eligible crypto wire serverKeyId budget filter target (RegistrationNativeEntropyRun.project old) =
      PqxdhRecordLiftIdeal.lorEligible crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId
        (analysisEligible crypto wire serverKeyId budget filter target) (PqxdhRecordLiftIdeal.ctxView old) := by
  rcases old with ⟨⟨born, control⟩, secret⟩
  cases born with
  | none => rfl
  | some born =>
      rcases born with ⟨created, ⟨value, ledger⟩, native⟩
      apply Bool.eq_iff_iff.mpr
      simp only [eligible, eligibleView, HiddenTests, RegistrationNativeRecordPackage.nativeView, RegistrationNativeEntropyRun.project,
        RegistrationNativeEntropyProgram.outcome, RegistrationNativeEntropyExecution.result, Option.map_some, Prod.map_def, id_eq,
        Option.elim_some, Bool.and_eq_true, decide_eq_true_iff, RegistrationNativeLorTransport.j_restored,
        PqxdhRecordLiftIdeal.lorEligible, PqxdhRecordLiftIdeal.ctxView, PqxdhRecordLiftIdeal.viewOf,
        PqxdhRecordLiftIdeal.publicHiding, analysisEligible, PqxdhRecordLiftIdeal.TestsHidden, Option.mem_some_iff,
        RegistrationNativeEntropyRestore.ledger_transcript, RegistrationNativeLorTransport.onTests_strip]
      simp only [(RegistrationNativeEntropyRestore.ledger_secrets ledger).1, RegistrationNativeLorCanonical.OnTests]
      constructor
      · rintro ⟨allowed, tested, hidden⟩
        exact ⟨allowed, (value, ledger, native), rfl, tested, hidden⟩
      · rintro ⟨allowed, other, rfl, tested, hidden⟩
        exact ⟨allowed, tested, hidden⟩

/-- The native winning event retains the original bit while public eligibility and physical tests are restored. -/
theorem project_winning (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity)
    (old : PqxdhRecordLiftIdeal.Client n (RegistrationNativeEntropyPort.State E) Value × PqxdhRecordLiftIdeal.CtxPrivate n) :
    winning crypto wire serverKeyId budget filter guess target (RegistrationNativeEntropyRun.project old) =
      PqxdhRecordLiftIdeal.lorGuess crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId
        (analysisDecision guess) (analysisEligible crypto wire serverKeyId budget filter target) (PqxdhRecordLiftIdeal.ctxView old) := by
  rcases old with ⟨⟨born, control⟩, secret⟩
  cases born with
  | none => rfl
  | some born =>
      rcases born with ⟨created, ⟨value, ledger⟩, native⟩
      apply Bool.eq_iff_iff.mpr
      simp only [winning, winningView, HiddenTests, RegistrationNativeRecordPackage.nativeView, RegistrationNativeEntropyRun.project,
        RegistrationNativeEntropyProgram.outcome, RegistrationNativeEntropyExecution.result, Option.map_some, Prod.map_def, id_eq,
        Option.elim_some, Bool.and_eq_true, decide_eq_true_iff, RegistrationNativeLorCanonical.w, RegistrationNativeLorTransport.j_restored,
        PqxdhRecordLiftIdeal.lorGuess, PqxdhRecordLiftIdeal.ctxView, PqxdhRecordLiftIdeal.viewOf,
        PqxdhRecordLiftIdeal.publicHiding, analysisEligible, analysisDecision, PqxdhRecordLiftIdeal.TestsHidden, Option.mem_some_iff,
        PqxdhRecordLiftIdeal.testBit, Option.bind_some,
        RegistrationNativeEntropyRestore.ledger_transcript, RegistrationNativeLorTransport.onTests_strip]
      simp only [(RegistrationNativeEntropyRestore.ledger_secrets ledger).1, RegistrationNativeLorCanonical.OnTests]
      constructor
      · rintro ⟨⟨allowed, bit⟩, tested, hidden⟩
        exact ⟨allowed, ⟨(value, ledger, native), rfl, tested, hidden⟩, bit⟩
      · rintro ⟨allowed, ⟨other, rfl, tested, hidden⟩, bit⟩
        exact ⟨⟨allowed, bit⟩, tested, hidden⟩


/-- Fairness holds at the actual reached cursor and shared CTX cache, without reinitializing either. -/
theorem initialized_lor (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (env : RegistrationNativeEntropyInterface.Environment n E)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (created : PqxdhLiveServerConstruction.Created Unit) (initial : E)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : PqxdhRecordLiftIdeal.CtxPrivate n) :
    𝒟[winning setup.source.crypto wire serverKeyId budget filter guess target <$>
      RegistrationNativeEntropyInitialized.run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire)
        route env serverKeyId bounds .P work created initial shell control secret] {true} =
      2⁻¹ * 𝒟[eligible setup.source.crypto wire serverKeyId budget filter target <$>
        RegistrationNativeEntropyInitialized.run (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire)
          route env serverKeyId bounds .P work created initial shell control secret] {true} := by
  rw [← RegistrationNativeEntropyInitialized.run_transport]
  simp only [Functor.map_map, project_winning, project_eligible]
  exact CborRawRecordLorInitial.lor setup (RegistrationNativeWire.ledgerCodec wire) route (RegistrationNativeEntropyPort.environment env)
    serverKeyId bounds (RegistrationNativeEntropyCompile.compile .P work) (analysisDecision guess)
    (analysisEligible setup.source.crypto wire serverKeyId budget filter target) created (((([], initial), shell), control), secret)

end BeaconcryptCore.Computational.RegistrationNativeLorEntropy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEntropy.project_eligible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEntropy.project_eligible

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEntropy.project_winning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEntropy.project_winning

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEntropy.initialized_lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEntropy.initialized_lor
