import BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition

/-! The accepted-observation bound applies to the complete native experiment in production constructor order. -/
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthObservedGame
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Complete original native execution with the client returning its public journal. The observation is a final mathematical projection; it changes no operation or public reply. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observation : Observation) (context : Context KemSK) : ProbComp Bool :=
  (fun result => observation context.seed context.scalar result.2.2.ghost result.1.2) <$>
    (simulateQ (PqxdhServerAuthNative.nativeHandler setup codec checks context.seed context.scalar context.beaconSeed)
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        (PqxdhJointDhExtractFamily.empty, contextState setup context)

/-- Native execution under the original context sampler, retaining the whole observation. -/
noncomputable def nativeGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observation : Observation) : ProbComp Bool := do
  let context ← contextSample setup codec
  native setup codec checks adversary revealSeed observation context

/-- The existing complete native interpreter relation applies to arbitrary final source observations and the entire chronological client journal. -/
theorem native_flat (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observation : Observation) :
    𝒟[nativeGame setup codec checks adversary revealSeed observation] =
      𝒟[flatObserved setup codec checks revealSeed adversary observation] := by
  apply evalDist_eq_of_evalSPMF_eq
  apply evalSPMF_eq_of_relTriple_eqRel
  unfold nativeGame flatObserved
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support (contextSample setup codec))
    (relTriple_refl_of_mem_support (contextSample setup codec) fun value member => ⟨rfl, member⟩) ?_
  rintro context _ ⟨rfl, supported⟩
  unfold native
  rw [← PqxdhServerAuthNative.program_native setup codec checks context.seed context.scalar context.beaconSeed
    _ (PqxdhJointDhExtractFamily.empty, contextState setup context) (contextSample_invariant setup codec context supported).1]
  simp only [PqxdhServerAuthNative.evaluate, run_interp, interp_simulateQ, Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono (flatReal_couple setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar _ (contextState setup context, PqxdhJointDhExtractFamily.empty))
  rintro left right (⟨same, related⟩ | ⟨bad, _⟩)
  · simp only [related, project, same]
    rfl
  · exact bad.elim

/-- Source constructor order with the complete native continuation: Server seed, Beacon seed, Beacon prekey, KEM generation and Phase-1 one-time scalar. -/
noncomputable def orderedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observation : Observation) : ProbComp Bool := do
  let seed ← sampleSeed
  let beaconSeed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let published ← phase1Run setup codec beaconSeed
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) oneTime keys.1 keys.2
  native setup codec checks adversary revealSeed observation ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩

/-- Constructor interchange is applied to the entire evaluated Phase-1/native/journal continuation, not to marginal distributions of keys. -/
theorem native_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observation : Observation) :
    𝒟[nativeGame setup codec checks adversary revealSeed observation] =
      𝒟[orderedGame setup codec checks adversary revealSeed observation] := by
  simpa only [nativeGame, orderedGame, contextSample, bind_assoc, pure_bind] using
    PqxdhServerAuthNative.constructor_order setup (fun seed scalar beaconSeed oneTime keys => do
      let published ← phase1Run setup codec beaconSeed
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) oneTime keys.1 keys.2
      native setup codec checks adversary revealSeed observation ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩)

/-- The full production-order native observation is exactly the original journaled source observation, including the actual source family interpreter. -/
theorem ordered_observed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observation : Observation) :
    𝒟[orderedGame setup codec checks adversary revealSeed observation] =
      𝒟[observed setup codec checks revealSeed adversary observation] := by
  exact (native_order setup codec checks adversary revealSeed observation).symm.trans
    ((native_flat setup codec checks adversary revealSeed observation).trans
      (evalDist_eq_of_evalSPMF_eq _ _ (observed_flat setup codec checks revealSeed adversary observation)).symm)

open PqxdhServerAuthObservedEntry PqxdhServerAuthObservedPartition

/-- Accepted observations read the actual acceptance annotation and only the root-erased trace plus public API journal. The secret seed/scalar indexing is ignored. -/
noncomputable def acceptedObservation (observer : Observer) : Observation := fun _ _ ghost journal =>
  @decide ((∃ snap, ghost.acceptance = some snap) ∧ observer (eraseGhost ghost) journal = true)
    (Classical.propDecidable _)

/-- The unrestricted accepted event in the native production-order execution is exactly the event partitioned in the original source experiment. No owner, disclosure, collision or successful-publication premise is added. -/
theorem ordered_accepted_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (observer : Observer) :
    𝒟[orderedGame setup codec checks adversary revealSeed (acceptedObservation observer)] =
      𝒟[acceptedGame setup codec checks revealSeed adversary observer] := by
  convert ordered_observed setup codec checks adversary revealSeed (acceptedObservation observer) using 1
  rfl

open PqxdhServerAuthAssumptions PqxdhServerAuthGapDh PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts

/-- The original native production-order accepted observation is bounded by the same single disclosure extractor, explicit scalar-collision term and Q+1 new schedule reductions, with the exact source-instantiated primitive-query ledger. Uniform observed endpoint security is still a separate obligation. -/
theorem ordered_bound_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary) (observer : Observer)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[orderedGame setup codec checks adversary false (acceptedObservation observer)] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), ((𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j observer] {true}).toReal +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j observer) ∧
    ObservedBills setup codec checks adversary observer caps qCoin Q qH qHash := by
  simpa only [ordered_accepted_source] using
    And.intro (accepted_bound setup codec checks adversary Q qH qHash budget observer law spread correct)
      (observed_bills setup codec checks caps bounded adversary observer qCoin Q qH qHash budget coins)

end BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.native_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.native_flat

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.native_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.native_order

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.ordered_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.ordered_observed

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.ordered_accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.ordered_accepted_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.ordered_bound_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution.ordered_bound_with_resources
