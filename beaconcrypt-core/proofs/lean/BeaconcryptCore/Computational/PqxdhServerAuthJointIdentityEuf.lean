import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityLog
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-! A concrete source client and a deterministic all-attempt extractor for the ordinary joint-use weak-EUF endpoint. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf
open PqxdhJointIdentity PqxdhEd25519EufCma PqxdhJointPhase1Reports
open PqxdhServerAuthExperiment PqxdhServerAuthJointIdentityCompiler PqxdhServerAuthJointIdentityLog
open PqxdhJointGapDh (ScalarBytes)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Re-read only the original raw message using the original abstract decoder and getters. No secret or recovered plaintext is an input. -/
def rawCandidate (codec : Codec Reader Response) (raw : Pqxdh.Bytes) : Option Phase1Candidate := do
  let reader ← codec.read1 raw
  let identity ← codec.identity reader
  let prekey ← codec.preField reader
  let oneTime ← codec.oneField reader
  let pq ← codec.pqField reader
  pure ⟨identity, prekey, oneTime, pq⟩

/-- Inspect all original accept inputs, including unsuccessful calls; this can only enlarge the extracted bad event. -/
def candidates (codec : Codec Reader Response) (journal : QueryLog ServerAuthSpec) : List Phase1Candidate :=
  journal.filterMap fun event => match event with
    | ⟨.inr (.accept raw), _⟩ => rawCandidate codec raw
    | _ => none

/-- Actual locally generated unsigned Phase1 fields. -/
def material (setup : Setup baseSpec KemSK) (scalar oneTime : ScalarBytes)
    (key : PqxdhKemIndCca.MlKem768PublicKey) : Phase1Material Unit :=
  ⟨setup.dh.publicKey scalar, setup.dh.publicKey oneTime, key, ()⟩

/-- All-candidate same-identity field substitution; attacker-owned identities and unchanged honest candidates are included in the run and do not satisfy this event. -/
def changed (primitives : Primitives) (target : PublicIdentity) (honest : Phase1Material Unit)
    (attempts : List Phase1Candidate) : Bool :=
  attempts.any (phase1FieldSubstitutionBit primitives.verify target.ed25519 honest)

/-- An executable public scan returns the first valid, never-issued detached signature. It performs no oracle request and makes no field or attempt guess. -/
def extract (primitives : Primitives) (target : PublicIdentity) (honest : Phase1Material Unit)
    (attempts : List Phase1Candidate) (fallback : Forgery) : Forgery :=
  ((attempts.flatMap candidateFields).find? fun forgery =>
    primitives.verify target.ed25519 forgery.message forgery.signature &&
      !decide (forgery.message ∈ honestPhase1Messages honest)).getD fallback

/-- With the actual three-message history, any changed accepted tuple supplies a valid fresh field to the all-attempt scan. No signature uniqueness or honest-candidate premise is required. -/
theorem extract_wins (primitives : Primitives) (target : PublicIdentity) (honest : Phase1Material Unit)
    (attempts : List Phase1Candidate) (fallback : Forgery) (history : History)
    (logged : signedMessages history = honestPhase1Messages honest)
    (bad : changed primitives target honest attempts = true) :
    wins primitives target (extract primitives target honest attempts fallback) history = true := by
  obtain ⟨candidate, member, substituted⟩ := List.any_eq_true.mp bad
  obtain ⟨decoded, accepted, _⟩ :=
    (phase1FieldSubstitutionBit_eq_true_iff _ _ _ _).mp substituted
  obtain ⟨forgery, field, fresh⟩ := singleBundle_unissued primitives target.ed25519 honest candidate substituted
  have valid := acceptedFields_valid primitives candidate target.ed25519 decoded accepted forgery field
  cases selected : (attempts.flatMap candidateFields).find? (fun forgery =>
      primitives.verify target.ed25519 forgery.message forgery.signature &&
        !decide (forgery.message ∈ honestPhase1Messages honest)) with
  | none =>
    have missing := (List.find?_eq_none.mp selected) forgery (List.mem_flatMap.mpr ⟨candidate, member, field⟩)
    simp [valid, fresh] at missing
  | some found =>
    simpa only [wins, extract, selected, Option.getD_some, logged] using List.find?_some selected

/-- The reduction's local unsigned fields and original public query/reply journal. No separate target-seed or complete native-state field is returned; the original public replies, including kernel reveals, remain unchanged. -/
structure Captured where
  honest : Phase1Material Unit
  journal : QueryLog ServerAuthSpec

/-- Full source-shaped execution in the joint game. All local samplers and the complete original private-state continuation run before the public extraction. -/
noncomputable def capture (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (target : PublicIdentity) : OracleComp AdversarySpec Captured := do
  let serverSeed ← coins sampleSeed
  let scalar ← coins PqxdhJointGapDh.sampleScalar
  let keys ← coins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let oneTime ← coins PqxdhJointGapDh.sampleScalar
  let result ← execution setup codec checks serverSeed scalar oneTime keys
    (fun input => PqxdhServerAuthApiJournal.record (adversary input)) target
  pure ⟨material setup scalar oneTime keys.1, result.2.1.2⟩

/-- Even after all source sampling and the adaptive API, the actual challenger log is exactly the three messages corresponding to the reduction's locally generated fields. -/
theorem capture_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (seed : IdentitySeed) (result : Captured × History)
    (supported : result ∈ support (PqxdhJointIdentity.run setup.joint seed (capture setup codec checks adversary))) :
    signedMessages result.2 = honestPhase1Messages result.1.honest := by
  simp only [PqxdhJointIdentity.run, capture, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, coins_history, bind_map_left,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨serverSeed, _, scalar, _, keys, _, oneTime, _, outcome, reached, rfl⟩ := supported
  simpa only [signedMessages, List.filterMap_nil, List.nil_append, honestPhase1Messages, material] using
    execution_history setup codec checks serverSeed seed scalar oneTime keys _ [] outcome reached

/-- The constructed primitive adversary uses only joint public keys, its own local generation, and the literal public journal. -/
noncomputable def reduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (fallback : Forgery) (target : PublicIdentity) : OracleComp AdversarySpec Forgery :=
  (fun result => extract setup.joint target result.honest (candidates codec result.journal) fallback) <$>
    capture setup codec checks adversary target

/-- A private common experiment for the event inclusion. Its seed and complete joint history are challenger state, never inputs to the reduction. -/
noncomputable def sampled (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) : ProbComp (IdentitySeed × (Captured × History)) := do
  let seed ← sampleSeed
  let result ← PqxdhJointIdentity.run setup.joint seed (capture setup codec checks adversary)
  pure (seed, result)

/-- The same full execution observed only for any publicly verifiable same-target field substitution. -/
noncomputable def routedBad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) : ProbComp Bool :=
  (fun result => changed setup.joint (setup.joint.publicKeys result.1) result.2.1.honest
    (candidates codec result.2.1.journal)) <$> sampled setup codec checks adversary

/-- The ordinary joint weak-EUF experiment uses this exact run and exact final signing history; extraction is a final public computation. -/
theorem reduction_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (fallback : Forgery) :
    PqxdhJointIdentity.game setup.joint (reduction setup codec checks adversary fallback) =
      (fun result => wins setup.joint (setup.joint.publicKeys result.1)
        (extract setup.joint (setup.joint.publicKeys result.1) result.2.1.honest
          (candidates codec result.2.1.journal) fallback) result.2.2) <$>
        sampled setup codec checks adversary := by
  simp only [PqxdhJointIdentity.game, PqxdhJointIdentity.run, reduction, simulateQ_map,
    StateT.run_map, bind_map_left, sampled, map_bind, map_pure]

set_option linter.deprecated false in
/-- Coefficient-one ordinary joint-use weak-EUF reduction for all original accept attempts in one complete source-shaped execution. No attempt, signature-field or candidate-key selection factor is charged. -/
theorem routed_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (fallback : Forgery) :
    Pr[= true | routedBad setup codec checks adversary] ≤
      PqxdhJointIdentity.advantage setup.joint (reduction setup codec checks adversary fallback) := by
  simp only [PqxdhJointIdentity.advantage, ← VCVioLegacy.probOutput_eq_prEvent, reduction_game, routedBad,
    ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def]
  apply probEvent_mono
  rintro ⟨seed, result⟩ supported bad
  simp only [sampled, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at supported
  obtain ⟨_, _, _, reached, rfl, rfl⟩ := supported
  exact extract_wins setup.joint _ _ _ fallback _
    (capture_history setup codec checks adversary _ _ reached) bad

/-- The original native API execution, with its original literal context and all private state, projected only after the run to local unsigned material and the public journal. -/
noncomputable def nativeCapture (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (context : PqxdhServerAuthEntryFactor.Context KemSK) : ProbComp Captured :=
  (fun result => (⟨material setup context.scalar context.oneTime context.keys.1, result.1.2⟩ : Captured)) <$>
    (simulateQ (PqxdhServerAuthNative.nativeHandler setup codec checks context.seed context.scalar context.beaconSeed)
      (PqxdhServerAuthApiJournal.record (adversary (PqxdhServerAuthEntryFactor.contextInput setup false context)))).run
        (PqxdhJointDhExtractFamily.empty, PqxdhServerAuthEntryFactor.contextState setup context)

set_option backward.isDefEq.respectTransparency false in
/-- The seed-free reduction reproduces the literal source generation and complete native execution, with every writer/rejection branch retained. -/
theorem capture_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (beaconSeed : IdentitySeed) :
    simulateQ (plain setup.joint beaconSeed) (capture setup codec checks adversary (setup.joint.publicKeys beaconSeed)) = (do
      let serverSeed ← sampleSeed
      let scalar ← PqxdhJointGapDh.sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      let oneTime ← PqxdhJointGapDh.sampleScalar
      let published ← phase1Run setup codec beaconSeed
        (PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed scalar) oneTime keys.1 keys.2
      nativeCapture setup codec checks adversary ⟨serverSeed, scalar, beaconSeed, oneTime, keys, published⟩) := by
  simp only [capture, simulateQ_bind, coins_plain, execution_plain, simulateQ_pure, bind_assoc, pure_bind]
  simp only [nativeCapture, PqxdhServerAuthEntryFactor.contextInput,
    PqxdhServerAuthEntryFactor.contextState, PqxdhServerAuthEntryFactor.Context.publicValue,
    Bool.false_eq_true, ite_false, bind_pure_comp]

/-- Removing the challenger's private log changes no source observation. -/
theorem capture_observation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (seed : IdentitySeed) :
    (fun result => changed setup.joint (setup.joint.publicKeys seed) result.1.honest
      (candidates codec result.1.journal)) <$>
        PqxdhJointIdentity.run setup.joint seed (capture setup codec checks adversary) =
      (fun result => changed setup.joint (setup.joint.publicKeys seed) result.honest
        (candidates codec result.journal)) <$>
          simulateQ (plain setup.joint seed) (capture setup codec checks adversary (setup.joint.publicKeys seed)) := by
  simpa only [PqxdhJointIdentity.run, Functor.map_map, Function.comp_def] using congrArg
    (fun work => (fun result => changed setup.joint (setup.joint.publicKeys seed) result.honest
      (candidates codec result.journal)) <$> work)
    (plain_run setup.joint seed (capture setup codec checks adversary (setup.joint.publicKeys seed)) [])

/-- Production constructor order and the original native API. Only the final mathematical event scans all public accept inputs for same-identity changed signed fields. -/
noncomputable def sourceBad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) : ProbComp Bool := do
  let serverSeed ← sampleSeed
  let beaconSeed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let published ← phase1Run setup codec beaconSeed
    (PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed scalar) oneTime keys.1 keys.2
  let result ← nativeCapture setup codec checks adversary ⟨serverSeed, scalar, beaconSeed, oneTime, keys, published⟩
  pure (changed setup.joint (setup.joint.publicKeys beaconSeed) result.honest (candidates codec result.journal))

set_option backward.isDefEq.respectTransparency false in
/-- The joint reduction and original source event have identical evaluated distributions. The seed-order law quantifies over the complete native continuation and its original state, caches and public replies. -/
theorem source_routed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) :
    𝒟[routedBad setup codec checks adversary] = 𝒟[sourceBad setup codec checks adversary] := by
  simp only [routedBad, sampled, map_bind, map_pure]
  simp_rw [bind_pure_comp, capture_observation, capture_plain]
  simp only [map_bind, sourceBad, bind_pure_comp]
  exact seed_order _

set_option linter.deprecated false in
/-- Actual production-order field-substitution probability is bounded by the constructed joint Ed25519/converted-X25519 weak-EUF adversary with coefficient one. The target seed is generated only by the primitive challenger. -/
theorem source_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (fallback : Forgery) :
    𝒟[sourceBad setup codec checks adversary] {true} ≤
      PqxdhJointIdentity.advantage setup.joint (reduction setup codec checks adversary fallback) := by
  rw [← source_routed, evalDist_apply_singleton]
  exact routed_bound setup codec checks adversary fallback

/-- The reached original decoder and getter receipts reconstruct the exact original candidate, with no injectivity or serialization assumption. -/
theorem rawCandidate_receipt (codec : Codec Reader Response) (raw : Pqxdh.Bytes)
    (reader : Reader) (candidate : Phase1Candidate)
    (read : codec.read1 raw = some reader)
    (identity : codec.identity reader = some candidate.identityKey)
    (pre : codec.preField reader = some candidate.preKey)
    (one : codec.oneField reader = some candidate.oneTimeKey)
    (pq : codec.pqField reader = some candidate.pqKey) :
    rawCandidate codec raw = some candidate := by
  simp only [rawCandidate, read, identity, pre, one, pq, Option.bind_eq_bind, Option.bind_some, pure]

/-- Every actual accept request and its original decoded candidate occur in the public all-attempt scan, regardless of its optional response. -/
theorem candidates_member (codec : Codec Reader Response) (journal : QueryLog ServerAuthSpec)
    (raw : Pqxdh.Bytes) (reply : Option Nat) (candidate : Phase1Candidate)
    (member : (⟨.inr (.accept raw), reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal)
    (decoded : rawCandidate codec raw = some candidate) : candidate ∈ candidates codec journal := by
  exact List.mem_filterMap.mpr ⟨_, member, decoded⟩

/-- An actual receipt's changed candidate is included once in the all-attempt bad event, without choosing a record, field or successful accept index. -/
theorem changed_member (codec : Codec Reader Response) (primitives : Primitives) (target : PublicIdentity)
    (honest : Phase1Material Unit) (journal : QueryLog ServerAuthSpec)
    (raw : Pqxdh.Bytes) (reply : Option Nat) (candidate : Phase1Candidate)
    (member : (⟨.inr (.accept raw), reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ journal)
    (decoded : rawCandidate codec raw = some candidate)
    (bad : phase1FieldSubstitutionBit primitives.verify target.ed25519 honest candidate = true) :
    changed primitives target honest (candidates codec journal) = true :=
  List.any_eq_true.mpr ⟨candidate, candidates_member codec journal raw reply candidate member decoded, bad⟩

end BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.extract_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.extract_wins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.capture_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.capture_history
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.reduction_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.reduction_game
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.routed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.routed_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.capture_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.capture_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.capture_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.capture_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.source_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.source_routed
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.source_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.rawCandidate_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.rawCandidate_receipt
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.candidates_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.candidates_member
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.changed_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf.changed_member
