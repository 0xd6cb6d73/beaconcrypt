import BeaconcryptCore.Computational.PqxdhAuthenticatedRootExperiment

/-!
The source theorem keeps arbitrary candidates and the complete generated private prefix. The total KEM presentation is used only after support is derived from that same source generation. The exact source-order distribution then reaches a key-first private continuation through one charged authentication event. No selected-key honesty, zero-error correctness or ideal public HKDF premise occurs in this source bridge.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState
open PqxdhPrivateRootSource PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhSourceAuthenticatedRoot PqxdhHiddenRoot PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhChallengeSecretRouting
open PqxdhPrivatePhase1Prefix PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhGeneratedNativeContinuation PqxdhAuthenticatedRootExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- Whole-continuation native/total compatibility is used only for an actually generated target key. -/
theorem nativeNext_eq_total
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (secret : KemSK) (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (supported : (prepared.1.context.generated.target, secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen)) :
    𝒟[PqxdhAuthenticatedRootExperiment.nativeNext env baseImpl kem attachedVerify primitives program post secret prepared] =
      𝒟[PqxdhAuthenticatedRootExperiment.totalNext env baseImpl kem attachedVerify primitives program post secret prepared] := by
  refine EvalDistEq.evalDist_eq ?_
  simp only [PqxdhAuthenticatedRootExperiment.nativeNext, PqxdhAuthenticatedRootExperiment.totalNext]
  split
  · refine EvalDistEq.bind_right _ fun ephemeral => ?_
    refine ((compatible _ supported).bind_left _).trans ?_
    rw [bind_map_left]
  · rfl

/-- Total encapsulation is justified inside the same source prefix, with no honest selected-candidate premise. -/
theorem actual_eq_total
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native) :
    𝒟[actual env baseImpl kem attachedVerify primitives program post] =
      𝒟[nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
        (PqxdhAuthenticatedRootExperiment.totalNext env baseImpl kem attachedVerify primitives program post) false] := by
  refine EvalDistEq.evalDist_eq ?_
  rw [actual]
  refine (nativeContinued_keyfirst _ _ _ _ _ _ _ _).trans ?_
  refine EvalDistEq.trans ?_ (nativeContinued_keyfirst _ _ _ _ _ _ _ _).symm
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun pair generated => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun prepared reached => ?_
  refine EvalDistEq.of_evalDist_eq ?_
  apply nativeNext_eq_total env baseImpl kem attachedVerify primitives program post compatible pair.2 prepared
  rw [PqxdhGeneratedRootSource.borrowedPrefix_target attachedVerify primitives baseImpl kem pair.2 setup
    (driver env.toDriverEnvironment program) pair.1 prepared reached]
  exact generated

/-- The private mathematical completion retains the initial encapsulated secret and all later native calls. Completed modes ignore the additional ordinary challenger encapsulation. -/
noncomputable def nativeComplete (key : TargetKemPublicKey) (secret : KemSK)
    (mode : Mode setup (driver env.toDriverEnvironment program).State) : ProbComp Bool := do
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)
  nativeAfter env baseImpl kem attachedVerify primitives program post key secret mode pair.1 pair.2

/-- This key-first presentation is the exact private actual continuation expected by the ordinary endpoint. -/
noncomputable def nativeMain : ProbComp Bool := do
  let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let mode ← evalKem baseImpl kem pair.2 ((protocol env kem attachedVerify primitives program post).prepare pair.1)
  nativeComplete env baseImpl kem attachedVerify primitives program post pair.1 pair.2 mode

/-- Dispatch preserves every source branch and the complete native continuation, erasing only an unused independent challenger draw on completed branches. -/
theorem dispatch_complete_eq_source
    (prepared : Prepared setup (driver env.toDriverEnvironment program).State)
    (key : TargetKemPublicKey) (secret : KemSK) (target_eq : prepared.1.context.generated.target = key) :
    𝒟[do
      let mode ← evalKem baseImpl kem secret
        (PqxdhPrivateAcceptedRoot.dispatch kem env.parameters attachedVerify primitives setup (commonObserver env program post) prepared)
      nativeComplete env baseImpl kem attachedVerify primitives program post key secret mode] =
      𝒟[PqxdhAuthenticatedRootExperiment.filteredNext env baseImpl kem attachedVerify primitives program post secret prepared] := by
  refine EvalDistEq.evalDist_eq ?_
  by_cases bad : changedBit (some prepared.1, prepared.2) = true
  · simp [PqxdhPrivateAcceptedRoot.dispatch, PqxdhAuthenticatedRootExperiment.filteredNext, bad, evalKem, nativeComplete, nativeAfter,
      -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
    exact OracleComp.EvalDistEq.map_const _ _
  · by_cases eligible : targetEligible env.parameters prepared = true
    · simp only [PqxdhPrivateAcceptedRoot.dispatch, PqxdhAuthenticatedRootExperiment.filteredNext, bad, Bool.false_eq_true, ite_false,
        eligible, ite_true, PqxdhAuthenticatedRootExperiment.totalNext, evalKem_bind, evalKem_ambient, bind_assoc]
      refine EvalDistEq.bind_right _ fun ephemeral => ?_
      cases failure : rootFailure env.source.crypto env.server.ikSk ephemeral.toList
        prepared.1.context.publicIdentity.ed25519 prepared.1.context.generated.before.publicKey
        prepared.1.context.generated.after.publicKey with
      | none =>
          simp only [Environment.parameters, failure, evalKem_pure, pure_bind, nativeComplete, nativeAfter,
            nativeAfterEncapsulation, target_eq]
          exact EvalDistEq.rfl
      | some reason =>
          simp only [Environment.parameters, failure, evalKem_bind, evalKem_ambient, evalKem_pure,
            bind_assoc, pure_bind, nativeAfterEncapsulation]
          refine EvalDistEq.bind_right _ fun encapsulated => ?_
          simp [nativeComplete, nativeAfter, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
          refine (EvalDistEq.bind_right _ fun value => OracleComp.EvalDistEq.map_const _ value).trans ?_
          rw [bind_pure]
    · simp only [PqxdhPrivateAcceptedRoot.dispatch, PqxdhAuthenticatedRootExperiment.filteredNext,
        PqxdhAuthenticatedRootExperiment.totalNext, bad, eligible]
      simp [evalKem, nativeComplete, nativeAfter, Environment.parameters, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
      refine (EvalDistEq.bind_right _ fun value => OracleComp.EvalDistEq.map_const _ value).trans ?_
      rw [bind_pure]

/-- Complete evaluated source-order equality moves only the independently generated KEM pair and the unused completed-mode challenge draw. -/
theorem filtered_eq_nativeMain :
    𝒟[nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
      (PqxdhAuthenticatedRootExperiment.filteredNext env baseImpl kem attachedVerify primitives program post) false] =
      𝒟[nativeMain env baseImpl kem attachedVerify primitives program post] := by
  refine EvalDistEq.evalDist_eq ?_
  refine (nativeContinued_keyfirst _ _ _ _ _ _ _ _).trans ?_
  simp only [nativeMain, protocol, evalKem_bind, bind_assoc]
  refine EvalDistEq.bind_right _ fun pair => ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun prepared supported => ?_
  refine EvalDistEq.of_evalDist_eq ?_
  exact (dispatch_complete_eq_source env baseImpl kem attachedVerify primitives program post prepared pair.1 pair.2
    (PqxdhGeneratedRootSource.borrowedPrefix_target attachedVerify primitives baseImpl kem pair.2 setup
      (driver env.toDriverEnvironment program) pair.1 prepared supported)).symm

/-- The explicit source filter charges only the original changed-acceptance event; all later native work is kept verbatim. -/
theorem nativeContinued_filtered :
    nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
      (PqxdhAuthenticatedRootExperiment.filteredNext env baseImpl kem attachedVerify primitives program post) false = (do
      let stopped ← privateRun attachedVerify primitives 1
        (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))
      if changedBit stopped then pure false else
        match stopped.1 with
        | none => pure false
        | some output =>
            PqxdhAuthenticatedRootExperiment.totalNext env baseImpl kem attachedVerify primitives program post
              output.context.generated.secret (eraseOutput output, stopped.2)) := by
  unfold nativeContinued
  apply bind_congr
  rintro ⟨output, state⟩
  cases output with
  | none => rfl
  | some output => rfl

/-- One constructed joint Ed25519/X25519 weak-EUF reduction charges accepted changed signed fields exactly once, preserving every other original source branch. -/
theorem authentication_hop
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec)
        PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (nativeMain env baseImpl kem attachedVerify primitives program post) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal := by
  have auth := PqxdhPhase2GeneratedDriverBounds.authentication_continuation_bound env.toDriverEnvironment program
    attachedVerify primitives adapter baseImpl kem noSign noCreate fallback ordinaryFallback
    (fun stopped => match stopped.1 with
      | none => pure false
      | some output => PqxdhAuthenticatedRootExperiment.totalNext env baseImpl kem attachedVerify primitives program post
          output.context.generated.secret (eraseOutput output, stopped.2))
    (fun _ => pure false)
  have totalBound :
      tvDist (nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
        (PqxdhAuthenticatedRootExperiment.totalNext env baseImpl kem attachedVerify primitives program post) false)
        (nativeContinued attachedVerify primitives baseImpl kem setup (driver env.toDriverEnvironment program)
          (PqxdhAuthenticatedRootExperiment.filteredNext env baseImpl kem attachedVerify primitives program post) false) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal := by
    rw [nativeContinued_filtered]
    unfold nativeContinued
    unfold tvDist
    convert auth using 1
    refine congrArg₂ SPMF.tvDist ?_ ?_
    all_goals refine congrArg _ (bind_congr fun state => ?_)
    all_goals split <;> simp_all only
  have output := (abs_probOutput_toReal_sub_le_tvDist _ _).trans totalBound
  simpa only [ProbComp.boolDistAdvantage, VCVioLegacy.evalDist_singleton_eq_probOutput, prEvent_eq_evalDist_singleton,
    actual_eq_total env baseImpl kem attachedVerify primitives program post compatible,
    ← filtered_eq_nativeMain env baseImpl kem attachedVerify primitives program post] using output

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.nativeNext_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.nativeNext_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.actual_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.actual_eq_total

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.dispatch_complete_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.dispatch_complete_eq_source

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.filtered_eq_nativeMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.filtered_eq_nativeMain

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.nativeContinued_filtered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.nativeContinued_filtered

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.authentication_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource.authentication_hop
