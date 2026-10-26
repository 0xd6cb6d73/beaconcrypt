import BeaconcryptCore.Computational.PqxdhServerAuthPublicationGuess
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationReferenceBytes

/-! The complete sampled publication reference supplies the concrete before-raw tag observer and the existing ordinary random privacy endpoint. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom
open CtxRomAuth AdaptiveCtxReceive PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhServerAuthPublicationGuess PqxdhServerAuthPublicationPrivateView
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

/-- The complete reference is lowered through the maintained adaptive known-key compiler, with its literal empty known-key state. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :=
  AdaptiveCtxDynamicKnownKeys.wrapped setup.source.crypto
    (PqxdhServerAuthPublicationReference.client setup codec checks adversary Q j)
    AdaptiveCtxDynamicKnownKeys.initialReduction

/-- The literal source/reference compiler makes at most one selected seal, including rejected and unreturned outputs. -/
theorem source_seal (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (source setup codec checks adversary Q j).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 :=
  AdaptiveCtxDynamicKnownBounds.target_bound setup.source.crypto _
    AdaptiveCtxSharedTarget.forward_seal_class _ 1
    (PqxdhServerAuthPublicationReferenceResources.client_record_bills setup codec checks adversary Q j).1 _

/-- The actual decoded tag is read only from the first selected raw request, before any opening operation is issued. -/
def decodedTag (decode : RawDecoder) (bytes : Pqxdh.Bytes) : Option (FixedBytes 16) :=
  (decode bytes).map fun target => ⟨target.record.tag, target.record.tagLength⟩

/-- The unconditional concrete reference capture has one 128-bit tag-guess charge. Its complete context, residual and adaptive source work are sampled as originally specified. -/
theorem reference_capture (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (replacement : CtxRomRecord) :
    Pr{let x ← (Prod.fst <$>
      (simulateQ (impl decode) (capture (source setup codec checks adversary Q j) none)).run
        ((initialState, []), CtxNonceAeadIntCtxt.emptyModifiedNonceAeadHandlerState))}[(Hit (decodedTag decode)) x] ≤
      ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  exact blind_capture_bound decode replacement _
    (source_seal setup codec checks adversary Q j)
    (PqxdhServerAuthPublicationBlindKnown.reference replacement setup codec checks adversary Q j _)
    _ initial_unused _

/-- The existing ordinary random privacy view is exactly the complete direct source interpreted at its literal empty state, with only its Boolean decision exposed. -/
theorem random_source (decode : RawDecoder) (work : OracleComp ReceiveSpec Bool) :
    AdaptiveCtxPrivacyGuard.randomView decode work = Prod.fst <$>
      (simulateQ (impl decode) work).run
        ((initialState, []), CtxNonceAeadIntCtxt.emptyModifiedNonceAeadHandlerState) := by
  rw [AdaptiveCtxDirectReplay.randomView_direct, program_source]
  simp only [AdaptiveCtxDirectReplay.directRandomView, AdaptiveCtxDirectReplay.directRandomGame,
    AdaptiveCtxDirectReplay.directClient, Functor.map_map]

/-- The concrete ordinary decision privately captures the actual record and tests its tag against the first raw request; it never issues that opening. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) : OracleComp ReceiveSpec Bool := by
  classical
  exact (fun candidate => decide (Hit (decodedTag decode) candidate)) <$>
    capture (source setup codec checks adversary Q j) none

/-- The existing ordinary random privacy endpoint of the actual fully sampled reference observer has probability at most one 128-bit tag guess. -/
theorem random_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) :
    Pr{let answer ← (AdaptiveCtxPrivacyGuard.randomView decode
      (decision setup codec checks adversary Q j decode))}[answer = true] ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [random_source]
  simp only [decision, simulateQ_map, StateT.run_map, Functor.map_map, prEvent_map, decide_eq_true_eq]
  simpa only [prEvent_map, Function.comp_def] using
    reference_capture setup codec checks adversary Q j decode
      ⟨[], List.replicate 16 0, by simp, List.Vector.replicate 64 0⟩

/-- The actual tag decision preserves every all-reply ordinary source budget, including selected plaintext bytes. -/
theorem decision_budget {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (canQuery : ReceiveSpec.Domain → Budget → Prop)
    (cost : ReceiveSpec.Domain → Budget → Budget) (budget : Budget)
    (bounded : (source setup codec checks adversary Q j).IsQueryBound budget canQuery cost) :
    (decision setup codec checks adversary Q j decode).IsQueryBound budget canQuery cost := by
  rw [decision, isQueryBound_map_iff]
  exact capture_budget _ canQuery cost budget bounded none

/-- The concrete ordinary decision issues no selected opening even when its first candidate is malformed. -/
theorem decision_no_raw (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (decode : RawDecoder) :
    (decision setup codec checks adversary Q j decode).IsQueryBoundP IsRawQuery 0 := by
  rw [decision, isQueryBoundP_map_iff]
  exact capture_no_raw _ none

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh

/-- Concrete source budgets lower through every known-key operation and the actual cutoff. The decision has one selected seal and no selected raw request, without bounding only successful callbacks. -/
theorem decision_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : RawDecoder) :
    let client := decision setup codec checks adversary Q j decode
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform H ∧
      client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash H ∧
      client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 ∧
      client.IsQueryBoundP IsRawQuery 0 := by
  have bills := PqxdhServerAuthPublicationReferenceResources.client_bills setup codec checks
    caps bounded adversary qCoin Q qHash qH coins accepts hashes rom j
  refine ⟨?_, ?_, ?_, decision_no_raw setup codec checks adversary Q j decode⟩
  · apply decision_budget
    exact AdaptiveCtxDynamicKnownBounds.uniform_bound setup.source.crypto _ _ bills.1 _
  · apply decision_budget
    exact AdaptiveCtxDynamicKnownBounds.hash_bound setup.source.crypto _ _ bills.2.1 _
  · apply decision_budget
    exact source_seal setup codec checks adversary Q j

/-- The actual observer retains the source checked plaintext limit across all adaptive branches; stopping and testing add no plaintext bytes. -/
theorem decision_plaintext (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (decode : RawDecoder) :
    AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound
      (decision setup codec checks adversary Q j decode) Aeneas.Std.Usize.max := by
  apply decision_budget
  exact AdaptiveCtxDynamicKnownBounds.plaintext_bound setup.source.crypto _ _
    (PqxdhServerAuthPublicationReferenceBytes.client_plaintext setup codec checks adversary Q j) _

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.source_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.source_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.reference_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.reference_capture
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.random_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.random_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.random_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_no_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_no_raw
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom.decision_plaintext
