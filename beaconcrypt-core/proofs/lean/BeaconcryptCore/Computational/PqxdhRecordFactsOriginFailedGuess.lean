-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSelectedSeal
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess

/-! Unconditional guessing after a literal failed selected writer; successful publication stops this selected target. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess
open CtxRomAuth PqxdhRecordFactsOriginSelectedSeal
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordFactsOriginMuteComplete (project)
open PqxdhServerAuthExperiment (Setup Codec)
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
local instance : MeasurableSpace (CtxDigest × Option (X × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × Option (X × CtxPrivate n)) := ⟨fun _ => trivial⟩

/-- Complete fixed muted continuation at the literal selected seal poststate; all operational replies and retained state remain available. -/
noncomputable def continuation (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) (digest : CtxDigest) : ProbComp (X × CtxPrivate n) :=
  Prod.map id (project pending.material) <$>
    (simulateQ (PqxdhRecordFactsOriginMuteServices.interpreter pending.material modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace) client).run
        (hiddenResult codec.frameWrite pending input body tag width digest state).2

/-- Sample the original unconditioned digest; continue with the absent writer reply only on literal failure, and stop this target on successful publication. -/
noncomputable def experiment (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X) : ProbComp (CtxDigest × Option (X × CtxPrivate n)) := do
  let digest ← $ᵗ CtxDigest
  if (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone then
    let result ← continuation modes setup codec replace pending input body tag width state client digest
    pure (digest, some result)
  else pure (digest, none)

/-- A fixed failed-writer continuation has the same full projected distribution for every digest. -/
theorem continuation_fixed (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (digest : CtxDigest) :
    continuation modes setup codec replace pending input body tag width state client digest =
      continuation modes setup codec replace pending input body tag width state client default :=
  continuation_independent modes setup codec replace pending input body tag width digest default state client noSeal

/-- The stopped failed-writer experiment has two fixed continuations, with literal failure as its only digest-dependent branch selector. -/
theorem experiment_form (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0) :
    experiment modes setup codec replace pending input body tag width state client =
      (do let digest ← $ᵗ CtxDigest
          let result ← if (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone then
            some <$> continuation modes setup codec replace pending input body tag width state client default
            else pure none
          pure (digest, result)) := by
  unfold experiment
  apply bind_congr
  intro digest
  split
  · rw [continuation_fixed modes setup codec replace pending input body tag width state client noSeal digest]
    simp only [bind_map_left]
  · simp only [pure_bind]

/-- Each fixed adaptive digest guess after the literal failed selected writer costs at most two uniform point masses, without conditioning on failure. -/
theorem failed_guess_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (guess : X × CtxPrivate n → Option CtxDigest) :
    𝒟[experiment modes setup codec replace pending input body tag width state client]
      {result | result.2.bind guess = some result.1} ≤ 2 * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [experiment_form modes setup codec replace pending input body tag width state client noSeal]
  have bounded := PqxdhRecordFactsOriginGuess.one_bit_guess (X := Option (X × CtxPrivate n))
    (fun digest => (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone)
    (fun failed => if failed then some <$> continuation modes setup codec replace pending input body tag width state client default else pure none)
    (fun result => result.bind guess)
  simpa only [ite_bind] using bounded

/-- The literal failed-writer reply selects `next none`; existing source freshness discharges its restriction before any writer outcome is observed. -/
theorem source_failed_guess_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (past : List (Label n)) (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (next : (ServiceSpec n).Range (.sealing pending) → OracleComp (ServiceSpec n) X)
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated
      ((liftM ((ServiceSpec n).query (.sealing pending)) : OracleComp (ServiceSpec n) _) >>= next) past).AllQueriesSatisfy
        PqxdhRecordLiftProtocolHistory.Fresh)
    (guess : X × CtxPrivate n → Option CtxDigest) :
    𝒟[experiment modes setup codec replace pending input body tag width state (next none)]
      {result | result.2.bind guess = some result.1} ≤ 2 * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ :=
  failed_guess_bound modes setup codec replace pending input body tag width state (next none)
    (PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal past pending next fresh none) guess

/-- A finite family of adaptive guesses in the same failed-writer continuation is charged once per attempt. -/
theorem failed_guesses_bound (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length = 16) (state : CtxPrivate n)
    (client : OracleComp (ServiceSpec n) X)
    (noSeal : client.IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (attempts : Nat) (guess : Fin attempts → X × CtxPrivate n → Option CtxDigest) :
    𝒟[experiment modes setup codec replace pending input body tag width state client]
      {result | ∃ index, result.2.bind (guess index) = some result.1} ≤
        2 * attempts * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  have cover : {result : CtxDigest × Option (X × CtxPrivate n) |
      ∃ index, result.2.bind (guess index) = some result.1} =
      ⋃ index : Fin attempts, {result | result.2.bind (guess index) = some result.1} := by
    ext result
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [cover]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun index =>
    failed_guess_bound modes setup codec replace pending input body tag width state client noSeal (guess index)).trans ?_)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc, mul_left_comm, le_refl]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.continuation_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.continuation_fixed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.experiment_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.experiment_form

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.failed_guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.failed_guess_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.source_failed_guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.source_failed_guess_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.failed_guesses_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess.failed_guesses_bound
