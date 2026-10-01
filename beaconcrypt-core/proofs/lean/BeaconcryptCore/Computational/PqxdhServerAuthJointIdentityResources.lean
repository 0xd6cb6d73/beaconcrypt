import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityEuf

/-! Resource accounting for the concrete joint-use reduction. All source and primitive ambient work remains explicit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhServerAuthJointIdentityCompiler PqxdhServerAuthJointIdentityLog
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

set_option backward.isDefEq.respectTransparency false in
/-- The literal live Phase1 program invokes at most three joint signature requests under every possible returned signature and writer outcome. -/
theorem phase1_signing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (target : PublicIdentity) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    (phase1 setup codec target publicValue oneTime kemPk kemSk).IsQueryBoundP IsSign 3 := by
  unfold phase1
  have source := PqxdhLivePhase1Bundle.bundle_bound
    (publicProjection setup publicValue target kemPk) (freshBeacon setup publicValue kemSk) .signing
  simp only [reduceCtorEq, ite_false, ite_true, Nat.add_zero, Nat.zero_add] at source
  apply source.simulateQ_of_step
  · intro query counted
    rcases query with gen | ((coin | request) | bundle)
    all_goals try simp only [signingImpl, isQueryBoundP_pure, isQueryBoundP_query_iff, IsSign, false_implies]
    cases request <;> try trivial
    rename_i index service
    cases service <;> simp [IsSign]
  · intro query notCounted
    rcases query with gen | (request | bundle)
    all_goals simp_all only [PqxdhLivePhase1Bundle.IsKind, signingImpl, isQueryBoundP_pure,
      not_true_eq_false]

/-- The full adaptive source execution spends at most three signing requests, including arbitrary successful and failed native finishes. -/
theorem execution_signing {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (target : PublicIdentity) :
    (execution setup codec checks serverSeed scalar oneTime keys work target).IsQueryBoundP IsSign 3 := by
  unfold execution
  refine isQueryBoundP_bind (n := 3) (m := 0) (phase1_signing setup codec target _ oneTime keys.1 keys.2) ?_
  intro published _
  exact isQueryBoundP_bind (n := 0) (m := 0) (program_quiet setup codec checks serverSeed scalar _ _) (fun _ _ => trivial)

/-- The locally generated Server identity, prekey, KEM keypair and one-time scalar add no target signing request. -/
theorem capture_signing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (target : PublicIdentity) :
    (PqxdhServerAuthJointIdentityEuf.capture setup codec checks adversary target).IsQueryBoundP IsSign 3 := by
  unfold PqxdhServerAuthJointIdentityEuf.capture
  refine isQueryBoundP_bind (n := 0) (m := 3) (coins_quiet _) (fun serverSeed _ => ?_)
  refine isQueryBoundP_bind (n := 0) (m := 3) (coins_quiet _) (fun scalar _ => ?_)
  refine isQueryBoundP_bind (n := 0) (m := 3) (coins_quiet _) (fun keys _ => ?_)
  refine isQueryBoundP_bind (n := 0) (m := 3) (coins_quiet _) (fun oneTime _ => ?_)
  exact isQueryBoundP_bind (n := 3) (m := 0)
    (execution_signing setup codec checks serverSeed scalar oneTime keys _ target) (fun _ _ => trivial)

/-- All postprocessing is public and query-free: every uniform, signature, and optional static-DH cap is exactly the cap of the complete captured source execution. -/
theorem reduction_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (fallback : Forgery) (target : PublicIdentity)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate] (cap : Nat) :
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP predicate cap ↔
      (PqxdhServerAuthJointIdentityEuf.capture setup codec checks adversary target).IsQueryBoundP predicate cap :=
  isQueryBoundP_map_iff _ _ _

/-- The actual ordinary weak-EUF reduction has signing cap three, with no dependence on the number of adaptive accept attempts. -/
theorem reduction_signing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (fallback : Forgery) (target : PublicIdentity) :
    (PqxdhServerAuthJointIdentityEuf.reduction setup codec checks adversary fallback target).IsQueryBoundP IsSign 3 :=
  (reduction_queries setup codec checks adversary fallback target IsSign 3).mpr
    (capture_signing setup codec checks adversary target)

/-- At most three detached fields are inspected for each decoded input, in the actual source verification order. -/
theorem fields_length (attempts : List PqxdhEd25519EufCma.Phase1Candidate) :
    (attempts.flatMap PqxdhJointPhase1Reports.candidateFields).length ≤ 3 * attempts.length := by
  induction attempts with
  | nil => simp
  | cons candidate rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have fieldBound := PqxdhJointPhase1Reports.candidateFields_length candidate
    omega

/-- The extractor's detached-verification scan has at most three fields per original public API call, including rejected attempts. This is a bound on local scan inputs, not an omission of source oracle costs. -/
theorem journal_fields_length (codec : Codec Reader Response) (journal : QueryLog ServerAuthSpec) :
    ((PqxdhServerAuthJointIdentityEuf.candidates codec journal).flatMap
      PqxdhJointPhase1Reports.candidateFields).length ≤ 3 * journal.length := by
  exact (fields_length _).trans (Nat.mul_le_mul_left 3 (List.length_filterMap_le _ _))

end BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.phase1_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.phase1_signing
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.execution_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.execution_signing
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.capture_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.capture_signing
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.reduction_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.reduction_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.reduction_signing
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.fields_length' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.fields_length
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.journal_fields_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityResources.journal_fields_length
