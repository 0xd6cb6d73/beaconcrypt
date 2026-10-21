import BeaconcryptCore.Computational.PqxdhServerAuthObservedSchedule
import BeaconcryptCore.Computational.PqxdhServerAuthNative

/-! The public journal follows the original native protocol handlers and the complete production-order continuation. -/
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthObservedNative
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthObservedEntry
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual native source API retains its complete state while the external client returns its chronological journal. The final decision reads only the designated root-erased observation. -/
noncomputable def native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) : ProbComp Bool :=
  (fun result => decision setup context Q j observer result.2.2.ghost result.1.2) <$>
    (simulateQ (PqxdhServerAuthNative.nativeHandler setup codec checks context.seed context.scalar context.beaconSeed)
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        (PqxdhJointDhExtractFamily.empty, contextState setup context)

/-- The original native interpreter and real table skeleton have the same complete observed outcome for every context supplied by the actual sampler. -/
theorem native_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK)
    (supported : context ∈ support (contextSample setup codec)) :
    RelTriple (native setup codec checks adversary revealSeed Q j observer context)
      (source setup codec checks adversary revealSeed Q j observer context) Eq := by
  unfold native source
  rw [← PqxdhServerAuthNative.program_native setup codec checks context.seed context.scalar context.beaconSeed
    _ (PqxdhJointDhExtractFamily.empty, contextState setup context) (contextSample_invariant setup codec context supported).1]
  simp only [PqxdhServerAuthNative.evaluate, run_interp, interp_simulateQ, Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono (flatReal_couple setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar _ (contextState setup context, PqxdhJointDhExtractFamily.empty))
  rintro left right (⟨same, related⟩ | ⟨bad, _⟩)
  · simp only [related, project, same]
  · exact bad.elim

/-- Native observed experiment in the existing R1 context order. -/
noncomputable def nativeGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : ProbComp Bool := do
  let context ← contextSample setup codec
  native setup codec checks adversary revealSeed Q j observer context

/-- Native and flattened experiments agree on the complete final observation under the same source sampler. -/
theorem native_game_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) :
    𝒟[nativeGame setup codec checks adversary revealSeed Q j observer] =
      𝒟[PqxdhServerAuthObservedSchedule.actualGame setup codec checks adversary revealSeed Q j observer] := by
  refine EvalDistEq.evalDist_eq ((VCVioLegacy.evalSPMF_eq_iff_evalDistEq _ _).1 ?_)
  apply evalSPMF_eq_of_relTriple_eqRel
  unfold nativeGame PqxdhServerAuthObservedSchedule.actualGame
  refine relTriple_bind (R := fun a b => a = b ∧ a ∈ support (contextSample setup codec))
    (relTriple_refl_of_mem_support (contextSample setup codec) fun value member => ⟨rfl, member⟩) ?_
  rintro context _ ⟨rfl, supported⟩
  exact native_source setup codec checks adversary revealSeed Q j observer context supported

/-- Production constructor order: Server seed, Beacon seed, Beacon prekey, complete KEM generation and then the Phase-1 one-time scalar. Phase 1 and the entire native journal-producing continuation are unchanged. -/
noncomputable def orderedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let beaconSeed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let published ← phase1Run setup codec beaconSeed
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) oneTime keys.1 keys.2
  native setup codec checks adversary revealSeed Q j observer ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩

/-- Both source-order interchanges quantify over the full evaluated observed continuation, including every public request/reply, cache, state and adaptive decision. -/
theorem native_source_order (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) :
    𝒟[nativeGame setup codec checks adversary revealSeed Q j observer] =
      𝒟[orderedGame setup codec checks adversary revealSeed Q j observer] := by
  simpa only [nativeGame, orderedGame, contextSample, bind_assoc, pure_bind] using
    PqxdhServerAuthNative.constructor_order setup (fun seed scalar beaconSeed oneTime keys => do
      let published ← phase1Run setup codec beaconSeed
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) oneTime keys.1 keys.2
      native setup codec checks adversary revealSeed Q j observer ⟨seed, scalar, beaconSeed, oneTime, keys, published⟩)

/-- Production-order accepted observation transport to the correlated uniform-output game with its five concrete advantages. This is a per-owner bridge; a concrete publication predicate and its uniform-endpoint probability are separate obligations. -/
theorem ordered_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[orderedGame setup codec checks adversary revealSeed Q j observer] {true}).toReal ≤
      (𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary revealSeed Q j observer] {true}).toReal +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary revealSeed Q j observer := by
  rw [← native_source_order, native_game_source]
  exact PqxdhServerAuthObservedSchedule.source_uniform setup codec checks adversary revealSeed Q j observer correct

end BeaconcryptCore.Computational.PqxdhServerAuthObservedNative

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.native_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.native_game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.native_game_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.native_source_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.native_source_order

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.ordered_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedNative.ordered_uniform
