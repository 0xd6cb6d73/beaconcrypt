import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Binding

/-! The private target-generation occurrence of the actual R1 context sampler. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity PqxdhJointGapDh
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- R1 has one designated target generation. This private coordinate identifies that source occurrence, not a key value and not a uniqueness statement about a replicated scheduler. -/
inductive Position where
  | targetPhase1

/-- The literal context sampler, with its single source-generation coordinate retained as private annotation. -/
noncomputable def sample (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    ProbComp (Context KemSK × Position) :=
  (fun context => (context, Position.targetPhase1)) <$> contextSample setup codec

/-- Erasing the private coordinate recovers the complete original sampler, with all actual key generation and publication effects. -/
theorem sample_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    Prod.fst <$> sample setup codec = contextSample setup codec := by
  simp only [sample, Functor.map_map, id_map']

/-- These are the original sampled values and the exact same invocation of Phase1 publication. No origin is recovered by comparing public keys or root outputs. -/
def Generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (context : Context KemSK) : Prop :=
  context.seed ∈ support sampleSeed ∧
  context.scalar ∈ support PqxdhJointGapDh.sampleScalar ∧
  context.beaconSeed ∈ support sampleSeed ∧
  context.oneTime ∈ support PqxdhJointGapDh.sampleScalar ∧
  context.keys ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) ∧
  context.published ∈ support (phase1Run setup codec context.beaconSeed (context.publicValue setup)
    context.oneTime context.keys.1 context.keys.2)

/-- Every actual context sample supplies all same-run generation and Phase1 publication receipts. -/
theorem context_generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (supported : context ∈ support (contextSample setup codec)) :
    Generated setup codec context := by
  simp only [contextSample, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, seedRun, scalar, scalarRun, beaconSeed, beaconRun, oneTime, oneTimeRun,
    keys, keysRun, published, publishedRun, rfl⟩ := supported
  exact ⟨seedRun, scalarRun, beaconRun, oneTimeRun, keysRun, publishedRun⟩

/-- The private generation position and all generated fields come from one literal sampler output. -/
theorem sample_generated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (position : Position)
    (supported : (context, position) ∈ support (sample setup codec)) :
    position = .targetPhase1 ∧ Generated setup codec context := by
  simp only [sample, support_map] at supported
  obtain ⟨actual, reached, same⟩ := supported
  have contextEq : actual = context := congrArg Prod.fst same
  have positionEq : Position.targetPhase1 = position := congrArg Prod.snd same
  exact ⟨positionEq.symm, context_generated setup codec context (contextEq ▸ reached)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation.sample_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation.sample_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation.context_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation.context_generated

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation.sample_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation.sample_generated
