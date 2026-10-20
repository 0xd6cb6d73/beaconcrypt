import BeaconcryptCore.Computational.PqxdhInitialRootAliases
import BeaconcryptCore.Computational.RawCtxSelectedAliasCut
import BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor

/-!
The actual32-byte selected root is independent of the complete prepared context and the selected uniform64 response. Delay that root past the whole target-free labelled observer, including other cached/generated roots, and charge every initializer candidate. The resulting value-consistent private initializer response has distance at most qInitial/2^256. Public HKDF remains real; source equality at the real response is unconditional and incurs no additional preimage-tester loss.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialAliasBound
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialRootAliases
variable {Context Result : Type}

abbrev Trace (Result : Type) := Result × (RootOracle.QueryCache × List RootOutput)
abbrev Cut (Context : Type) := (Context × RootOutput) × HmacBlock

noncomputable def sampleCut (sample : ProbComp Context) : ProbComp (Cut Context) := do
  let context ← sample
  let root ← $ᵗ RootOutput
  let output ← $ᵗ HmacBlock
  pure ((context, root), output)

noncomputable def observed (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (context : Context) (output : HmacBlock) : ProbComp (Trace Result) :=
  (simulateQ (traced fixed) (simulateQ (compiler (selected context)
    (RawCtxSelectedInitialConstructor.response64 output)) (client context))).run (∅, [])

noncomputable def left (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (cut : Cut Context) : ProbComp (RootOutput × (HmacBlock × Trace Result)) :=
  (fun result => (cut.1.2, (cut.2, result))) <$> observed fixed selected client cut.1.1 cut.2

noncomputable def right (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (cut : Cut Context) : ProbComp (RootOutput × (HmacBlock × Trace Result)) :=
  (fun result => (cut.1.2, (cut.2, result))) <$>
    (simulateQ (RawCtxSelectedQueryTrace.recorded
      (consistent fixed cut.1.2 (RawCtxSelectedInitialConstructor.response64 cut.2)) inputs)
      (simulateQ (compiler (selected cut.1.1) (RawCtxSelectedInitialConstructor.response64 cut.2))
        (client cut.1.1))).run (∅, [])

/-- The complete result, selected64 response and hidden root remain attached to the same source alias coupling. -/
theorem pointwise (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (cut : Cut Context) :
    tvDist (left fixed selected client cut) (right fixed selected client cut) ≤
      Pr[fun result => result.1 ∈ result.2.2.2.2 | left fixed selected client cut].toReal := by
  have bound := (tvDist_map_le (fun result => (cut.1.2, (cut.2, result))) _ _).trans
    (distance fixed (selected cut.1.1) cut.1.2 (RawCtxSelectedInitialConstructor.response64 cut.2)
      (client cut.1.1) (∅, []))
  simpa only [left, right, observed, probEvent_map, Function.comp_def] using bound

/-- The original prepared-context/root/response draw averages the complete source coupling and charges that same original final candidate event. -/
theorem cut_distance (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (sample : ProbComp Context) :
    tvDist (sampleCut sample >>= left fixed selected client) (sampleCut sample >>= right fixed selected client) ≤
      Pr[fun result => result.1 ∈ result.2.2.2.2 | sampleCut sample >>= left fixed selected client].toReal := by
  exact PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind (sampleCut sample)
    (left fixed selected client) (right fixed selected client) (left fixed selected client)
    (fun result => result.1 ∈ result.2.2.2.2) (pointwise fixed selected client)

/-- Delay the selected root past the complete independent response and adaptive observer, retaining the root, response, full result, cache and candidate list. -/
theorem delayed (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (sample : ProbComp Context) :
    𝒮[sampleCut sample >>= left fixed selected client] =
      𝒮[sample >>= fun context => do
        let output ← $ᵗ HmacBlock
        let result ← observed fixed selected client context output
        let root ← $ᵗ RootOutput
        pure (root, (output, result))] := by
  simp only [sampleCut, left, bind_assoc, pure_bind]
  refine evalSPMF_bind_congr' (m := ProbComp) sample fun context => ?_
  have moved := evalSPMF_sample_comm_vcvioLegacy ($ᵗ RootOutput)
    (do let output ← $ᵗ HmacBlock
        let result ← observed fixed selected client context output
        pure (output, result)) (fun root pair => (pure (root, pair) : ProbComp _))
  simpa only [← bind_pure_comp, bind_assoc, pure_bind] using moved

/-- All adaptive equal-root aliases are charged against the original initializer cap, with no freshness conditioning and no coordinate-injectivity premise. -/
theorem candidates_bound (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (sample : ProbComp Context) (budget : Nat)
    (bounded : ∀ context, (client context).IsQueryBoundP IsInitializer budget) :
    Pr[fun result => result.1 ∈ result.2.2.2.2 | sampleCut sample >>= left fixed selected client] ≤
      (budget : ENNReal) / (2 ^ 256 : ENNReal) := by
  have delayedEvent := OracleComp.probEvent_congr'
    (p := fun result : RootOutput × (HmacBlock × Trace Result) => result.1 ∈ result.2.2.2.2)
    (q := fun result : RootOutput × (HmacBlock × Trace Result) => result.1 ∈ result.2.2.2.2)
    (fun _ _ => Iff.rfl) (delayed fixed selected client sample)
  rw [delayedEvent]
  refine probEvent_bind_le_of_forall_le fun context _ => ?_
  refine probEvent_bind_le_of_forall_le fun output _ => ?_
  refine probEvent_bind_le_of_forall_le fun result supported => ?_
  rw [bind_pure_comp, probEvent_map]
  refine (RawCtxSelectedInputCandidates.uniform_candidates result.2.2).trans ?_
  have length := trace_length fixed (selected context) (RawCtxSelectedInitialConstructor.response64 output)
    (client context) budget (bounded context) (∅, []) result supported
  simp only [List.length_nil, Nat.zero_add] at length
  exact ENNReal.div_le_div_right (by exact_mod_cast length) _

/-- The value-consistent initializer hybrid preserves the complete result and root cache up to the explicit original-request selection loss qInitial/2^256. -/
theorem cut_bound (fixed : FixedHkdfSha512NoSaltSource)
    (selected : Context → Message) (client : Context → OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (sample : ProbComp Context) (budget : Nat)
    (bounded : ∀ context, (client context).IsQueryBoundP IsInitializer budget) :
    tvDist (sampleCut sample >>= left fixed selected client) (sampleCut sample >>= right fixed selected client) ≤
      ((budget : ENNReal) / (2 ^ 256 : ENNReal)).toReal := by
  refine (cut_distance fixed selected client sample).trans ?_
  apply ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ (by norm_num)))
  exact candidates_bound fixed selected client sample budget bounded

end BeaconcryptCore.Computational.PqxdhInitialAliasBound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasBound.pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasBound.pointwise

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasBound.cut_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasBound.cut_distance

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasBound.delayed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasBound.delayed

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasBound.candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasBound.candidates_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasBound.cut_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasBound.cut_bound
