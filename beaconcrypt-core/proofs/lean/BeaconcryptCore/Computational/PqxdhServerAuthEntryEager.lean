import BeaconcryptCore.Computational.PqxdhServerAuthEntryFlat

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Read an existing table entry unchanged, or install the already sampled block at a missing input. -/
noncomputable def programmedRead (prk : HmacBlock) (bytes : Pqxdh.Bytes) :
    StateT HmacOracle.QueryCache ProbComp HmacBlock := fun cache =>
  match cache bytes with
  | some value => pure (value, cache)
  | none => pure (prk, cache.cacheQuery bytes prk)

set_option linter.deprecated false in
/-- A single table read is exactly a uniform block followed by the programmed read; on a hit the unused independent block disappears. -/
theorem programmedRead_sample (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache) :
    𝒮[(HmacOracle.randomOracle bytes).run cache] =
      𝒮[do let prk ← $ᵗ HmacBlock; (programmedRead prk bytes).run cache] := by
  rw [randomOracle.run_eq]
  cases hit : cache bytes with
  | none => simp only [hit, programmedRead, StateT.run]
  | some value =>
      simp only [hit, programmedRead, StateT.run]
      exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm

/-- The designated root derivation uses its prefetched block only at a missing actual input. -/
noncomputable def programmedDerive (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (prk : HmacBlock)
    (message : PqxdhJointDhExtractFamily.Message) : StateT HmacOracle.QueryCache ProbComp Reply := fun cache =>
  match PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => pure (.rejected, cache)
  | some bytes => (fun read => (.root (expandRoot hmac read.1), read.2)) <$>
      (programmedRead prk bytes).run cache

set_option linter.deprecated false in
/-- Eager sampling preserves the complete derivation reply and table, including rejection and prior hits. -/
theorem programmedDerive_sample (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : PqxdhJointDhExtractFamily.Message)
    (cache : HmacOracle.QueryCache) :
    𝒮[(realDerive hmac joint dh seed scalar message).run cache] =
      𝒮[do let prk ← $ᵗ HmacBlock; (programmedDerive hmac joint dh seed scalar prk message).run cache] := by
  unfold realDerive programmedDerive
  cases input : PqxdhJointDhExtractFamily.input joint dh seed scalar message with
  | none => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
  | some bytes =>
      dsimp only [StateT.run]
      rw [← map_bind, evalSPMF_map, evalSPMF_map]
      exact congrArg (fun work => (fun read => (Reply.root (expandRoot hmac read.1), read.2)) <$> work)
        (programmedRead_sample bytes cache)


/-- Only the designated derivation changes; all public HMAC requests and all other source services remain real. -/
noncomputable def programmedServices (seed : IdentitySeed) (scalar : ScalarBytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (prk : HmacBlock) :
    Services Response HmacOracle.QueryCache :=
  { realServices seed scalar setup codec checks with
    derive := programmedDerive setup.hmac setup.joint setup.dh seed scalar prk }

set_option linter.deprecated false in
/-- Sampling the candidate block before the complete accept operation preserves the entire returned state, including every rejection. -/
theorem programmedAccept_sample (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes)
    (raw : Pqxdh.Bytes) (state : FlatState KemSK HmacOracle.QueryCache) :
    𝒮[(acceptStep setup codec checks publicValue (realServices seed scalar setup codec checks) raw).run state] =
      𝒮[do
        let prk ← $ᵗ HmacBlock
        (acceptStep setup codec checks publicValue (programmedServices seed scalar setup codec checks prk) raw).run state] := by
  unfold acceptStep
  dsimp only [StateT.run]
  rw [DeferredSampling.evalSPMF_bind_comm]
  apply DeferredSampling.evalSPMF_bind_congr_left
  intro collected
  rcases collected with ⟨_ | input, consumed⟩
  · exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
  · by_cases valid : PqxdhServerRelatedRootInput.localNonzero input
    · simp only [valid, ite_true, realServices, programmedServices]
      rw [← bind_assoc, evalSPMF_bind, evalSPMF_bind]
      congr 1
      exact programmedDerive_sample setup.hmac setup.joint setup.dh seed scalar _ state.2.2
    · simp only [valid, ite_false]
      exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm


set_option linter.deprecated false in
/-- Eager sampling also preserves the entire single-shot Beacon finish, including failed preparation, raw opening and final commitment. -/
theorem programmedFinish_sample (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : FlatState KemSK HmacOracle.QueryCache) :
    𝒮[(finishStep setup codec publicValue beaconSeed (realServices seed scalar setup codec checks) raw).run state] =
      𝒮[do
        let prk ← $ᵗ HmacBlock
        (finishStep setup codec publicValue beaconSeed (programmedServices seed scalar setup codec checks prk) raw).run state] := by
  unfold finishStep
  dsimp only [StateT.run]
  cases phase : state.1.beacon.beacon.phase <;> simp only
  all_goals try exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
  rw [DeferredSampling.evalSPMF_bind_comm]
  apply DeferredSampling.evalSPMF_bind_congr_left
  intro prepared
  cases prepared with
  | none => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
  | some pending =>
      dsimp only [realServices, programmedServices]
      rw [← bind_assoc, evalSPMF_bind, evalSPMF_bind]
      congr 1
      exact programmedDerive_sample setup.hmac setup.joint setup.dh seed scalar _ state.2.2


set_option linter.deprecated false in
/-- Eager sampling preserves every complete oracle operation. Only accept and active finish can consume the sampled block. -/
theorem programmedStep_sample (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (publicValue : PublicChallenge) (beaconSeed : IdentitySeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : ServerAuthSpec.Domain)
    (state : FlatState KemSK HmacOracle.QueryCache) :
    𝒮[(skeleton setup codec checks publicValue beaconSeed (realServices seed scalar setup codec checks) query).run state] =
      𝒮[do
        let prk ← $ᵗ HmacBlock
        (skeleton setup codec checks publicValue beaconSeed
          (programmedServices seed scalar setup codec checks prk) query).run state] := by
  cases query with
  | inl coin => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
  | inr query =>
      cases query with
      | accept raw => exact programmedAccept_sample setup codec checks publicValue seed scalar raw state
      | finish raw => exact programmedFinish_sample setup codec checks publicValue beaconSeed seed scalar raw state
      | build session payload => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
      | hmac key message => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
      | hash bytes => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm
      | reveal keyId => exact (DeferredSampling.evalSPMF_bind_const_neverFails _ (probFailure_eq_zero) _).symm

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

section Once
variable {ι : Type} {spec : OracleSpec ι} {σ V : Type}

/-- Record that a designated operation has occurred while keeping its complete source reply and state. -/
def latch (choose : spec.Domain → σ → Bool) (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) := fun query state =>
  (fun result => (result.1, (result.2, state.2 || choose query state.1))) <$> (impl query).run state.1

/-- Replace only the first designated operation by its prefetched implementation. -/
def once (choose : spec.Domain → σ → Bool) (lazy : QueryImpl spec (StateT σ ProbComp))
    (programmed : V → QueryImpl spec (StateT σ ProbComp)) (value : V) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) := fun query state =>
  if state.2 then (latch choose lazy query).run state
  else if choose query state.1 then (latch choose (programmed value) query).run state
  else (latch choose lazy query).run state

/-- The analysis flag is sticky independently of every source reply. -/
theorem latch_keeps (choose : spec.Domain → σ → Bool) (impl : QueryImpl spec (StateT σ ProbComp))
    (query : spec.Domain) (state : σ × Bool) (done : state.2 = true) :
    ∀ result ∈ support ((latch choose impl query).run state), result.2.2 = true := by
  intro result member
  simp only [latch, StateT.run, support_map, Set.mem_image] at member
  obtain ⟨step, _, rfl⟩ := member
  simp [done]

set_option linter.deprecated false in
/-- One prefetched sample serves the entire adaptive run; the sampling law concerns complete query replies and states. -/
theorem once_sample (choose : spec.Domain → σ → Bool) (sampler : ProbComp V)
    (lazy : QueryImpl spec (StateT σ ProbComp)) (programmed : V → QueryImpl spec (StateT σ ProbComp))
    (sample : ∀ query state, 𝒮[(lazy query).run state] =
      𝒮[do let value ← sampler; (programmed value query).run state])
    {α : Type} (work : OracleComp spec α) (state : σ × Bool) :
    𝒮[(simulateQ (latch choose lazy) work).run state] =
      𝒮[do let value ← sampler; (simulateQ (once choose lazy programmed value) work).run state] := by
  apply eager_run sampler (latch choose lazy) (once choose lazy programmed) (fun state => state.2 = true)
  · intro query before done
    exact ⟨fun value => by simp only [once, StateT.run, done, ite_true],
      latch_keeps choose lazy query before done⟩
  · intro query before unfinished
    have flag : before.2 = false := Bool.eq_false_iff.mpr unfinished
    by_cases selected : choose query before.1 = true
    · right
      constructor
      · simp only [once, StateT.run, flag, Bool.false_eq_true, ite_false, selected, ite_true]
        simp only [latch]
        rw [← map_bind, evalSPMF_map, evalSPMF_map]
        congr 1
        exact sample query before.1
      · intro value result member
        simp only [once, StateT.run, flag, Bool.false_eq_true, ite_false, selected, ite_true,
          latch, support_map, Set.mem_image] at member
        obtain ⟨step, _, rfl⟩ := member
        simp
    · left
      intro value
      simp only [once, StateT.run, flag, Bool.false_eq_true, ite_false, selected]

/-- Dropping the private flag gives exactly the original complete adaptive source run. -/
theorem latch_run (choose : spec.Domain → σ → Bool) (impl : QueryImpl spec (StateT σ ProbComp))
    {α : Type} (work : OracleComp spec α) (state : σ × Bool) :
    (fun result => (result.1, result.2.1)) <$> (simulateQ (latch choose impl) work).run state =
      (simulateQ impl work).run state.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      change (fun result => (result.1, result.2.1)) <$>
        ((latch choose impl query).run state >>= fun step =>
          (simulateQ (latch choose impl) (next step.1)).run step.2) =
        ((impl query).run state.1 >>= fun step => (simulateQ impl (next step.1)).run step.2)
      simp only [latch, StateT.run, bind_map_left, map_bind]
      exact bind_congr fun step => ih step.1 (step.2, state.2 || choose query state.1)

set_option linter.deprecated false in
/-- The original run is a projection of one prefetched-value run, for an arbitrary adaptive client. -/
theorem eager_projected (choose : spec.Domain → σ → Bool) (sampler : ProbComp V)
    (lazy : QueryImpl spec (StateT σ ProbComp)) (programmed : V → QueryImpl spec (StateT σ ProbComp))
    (sample : ∀ query state, 𝒮[(lazy query).run state] =
      𝒮[do let value ← sampler; (programmed value query).run state])
    {α : Type} (work : OracleComp spec α) (state : σ × Bool) :
    𝒮[(simulateQ lazy work).run state.1] =
      𝒮[do
        let value ← sampler
        (fun result : α × (σ × Bool) => (result.1, result.2.1)) <$>
          (simulateQ (once choose lazy programmed value) work).run state] := by
  rw [← latch_run choose lazy work state, ← map_bind, evalSPMF_map, evalSPMF_map,
    once_sample choose sampler lazy programmed sample work state]

end Once
end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment
open PqxdhJointIdentity PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The designated owner operation is accept number `j` for `j < Q`, or the Beacon's first active finish for `j = Q`. This is an operation index, not a key equality. -/
def designated (Q : Nat) (j : Fin (Q + 1)) :
    ServerAuthSpec.Domain → FlatState KemSK HmacOracle.QueryCache → Bool
  | .inr (.accept _), state => decide (j.val < Q ∧ state.1.sessions = j.val)
  | .inr (.finish _), state => if j.val = Q then
      match state.1.beacon.beacon.phase with
      | .initSent .. => true
      | _ => false
    else false
  | _, _ => false

/-- The original table and complete protocol state with the private operation flag. -/
abbrev EntryState (KemSK : Type) := FlatState KemSK HmacOracle.QueryCache × Bool

/-- Run with one block sampled before the adversary, used only by the designated operation on its first execution. All other source operations stay real. -/
noncomputable def prefetchedHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) :
    QueryImpl ServerAuthSpec (StateT (EntryState KemSK) ProbComp) :=
  once (designated Q j)
    (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks))
    (fun value => skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (programmedServices context.seed context.scalar setup codec checks value)) prk

/-- The complete adaptive run after the context and the designated block are supplied. -/
noncomputable def prefetchedRun (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) : ProbComp (EntryState KemSK) :=
  Prod.snd <$> (simulateQ (prefetchedHandler setup codec checks context Q j prk)
    (adversary (contextInput setup revealSeed context))).run
      ((contextState setup context, fun _ => false, ∅), false)

/-- Eager entry game: the actual source context, one uniform PRK, then the unchanged adaptive adversary and complete state. -/
noncomputable def prefetchedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    ProbComp (Context KemSK × EntryState KemSK) := do
  let context ← contextSample setup codec
  let prk ← $ᵗ HmacBlock
  let result ← prefetchedRun setup codec checks adversary revealSeed context Q j prk
  pure (context, result)

set_option linter.deprecated false in
/-- The per-context run preserves its complete final protocol/table state when the private flag is removed. No honest-target, cache-miss or successful-derivation premise is used. -/
theorem prefetchedRun_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) :
    𝒮[flatRun setup adversary revealSeed context
      (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
        (realServices context.seed context.scalar setup codec checks)) ∅] =
      𝒮[do
        let prk ← $ᵗ HmacBlock
        Prod.fst <$> prefetchedRun setup codec checks adversary revealSeed context Q j prk] := by
  have complete := eager_projected (designated Q j) ($ᵗ HmacBlock)
    (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks))
    (fun value => skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (programmedServices context.seed context.scalar setup codec checks value))
    (programmedStep_sample setup codec checks (context.publicValue setup) context.beaconSeed
      context.seed context.scalar)
    (adversary (contextInput setup revealSeed context))
    ((contextState setup context, fun _ => false, ∅), false)
  unfold flatRun prefetchedRun
  simp only [Functor.map_map, ← map_bind, evalSPMF_map]
  simpa only [← map_bind, evalSPMF_map, Functor.map_map, Function.comp_def, prefetchedHandler] using
    congrArg (fun run => Prod.snd <$> run) complete


set_option linter.deprecated false in
/-- Exact complete-game equality after projecting the private flag; all context samples precede the designated block in their original R1 experiment order. -/
theorem prefetchedGame_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    𝒮[realGame setup codec checks revealSeed adversary] =
      𝒮[(fun result => (result.1, result.2.1)) <$>
        prefetchedGame setup codec checks adversary revealSeed Q j] := by
  unfold realGame prefetchedGame
  simp only [map_bind, map_pure]
  apply DeferredSampling.evalSPMF_bind_congr_left
  intro context
  have paired := congrArg (fun distribution => (fun state => (context, state)) <$> distribution)
    (prefetchedRun_source setup codec checks adversary revealSeed context Q j)
  simpa only [evalSPMF_bind, evalSPMF_map, evalSPMF_pure, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind] using paired


set_option linter.deprecated false in
/-- The actual per-owner authentication event is bounded by that same event in the complete prefetched experiment, with coefficient one and no loss. This step does not yet replace the key schedule. -/
theorem entry_le_prefetched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1)) :
    Pr[fun result => EntryEvent setup result.1 result.2.1 Q j result.2.2.1.ghost |
      gameState setup codec checks revealSeed adversary] ≤
      Pr[fun result => EntryEvent setup result.1.seed result.1.scalar Q j result.2.1.1.ghost |
        prefetchedGame setup codec checks adversary revealSeed Q j] := by
  apply le_trans (gameState_le_real setup codec checks revealSeed adversary (fun seed scalar ghost =>
    EntryEvent setup seed scalar Q j ghost))
  have same := probEvent_congr' (fun _ _ => Iff.rfl)
    (prefetchedGame_source setup codec checks adversary revealSeed Q j)
    (p := fun result => EntryEvent setup result.1.seed result.1.scalar Q j result.2.1.ghost)
  simpa only [probEvent_map, Function.comp_def] using le_of_eq same

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedRead_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedRead_sample
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedDerive_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedDerive_sample
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedAccept_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedAccept_sample
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedFinish_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedFinish_sample
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedStep_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.programmedStep_sample
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.latch_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.latch_keeps
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.once_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.once_sample
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.latch_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.latch_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eager_projected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.eager_projected
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedRun_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedRun_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedGame_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.prefetchedGame_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_le_prefetched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_le_prefetched
