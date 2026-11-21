-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginFailedGuess
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate
/-! A successful seal hidden by the actual public capacity gate has the same unconditional two-branch digest charge as a pure writer refusal. The reserve sees only a fixed public encoded amount, and its complete poststate remains in the analysis result. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
variable {n : Nat} {I KemSK Reader Response X Platform Failure : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CtxDigest × Option ((X × CtxPrivate n) × Platform)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × Option ((X × CtxPrivate n) × Platform)) := ⟨fun _ => trivial⟩

variable (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body tag : Pqxdh.Bytes) (width : tag.length=16) (state : CtxPrivate n)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (client : Platform → OracleComp (ServiceSpec n) X) (before : Platform)

noncomputable def continuation (platform : Platform) (digest : CtxDigest) : ProbComp ((X × CtxPrivate n) × Platform) :=
  (fun result => (result,platform)) <$> PqxdhRecordFactsOriginFailedGuess.continuation modes setup codec replace pending input body tag width state (client platform) digest

noncomputable def experiment : ProbComp (CtxDigest × Option ((X × CtxPrivate n) × Platform)) := do
  let digest ← $ᵗ CtxDigest
  let gated ← (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length)
    (hiddenResult codec.frameWrite pending input body tag width digest state).1).run before
  if gated.1.isNone then
    let result ← continuation modes setup codec replace pending input body tag width state client gated.2 digest
    pure (digest,some result)
  else pure (digest,none)

noncomputable def stopped (amount : Nat) (absent : Bool) : ProbComp (Option ((X × CtxPrivate n) × Platform)) :=
  if absent then some <$> continuation modes setup codec replace pending input body tag width state client before default
  else do
    let allocated ← (reserve amount).run before
    match allocated.1 with
    | .Ok _ => pure none
    | .Err _ => some <$> continuation modes setup codec replace pending input body tag width state client allocated.2 default

/-- The actual writer option and fixed public amount are the only information from the fresh digest that reaches reservation or the resumed client. Full capacity-service state is retained. -/
theorem experiment_form (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body tag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0) :
    experiment modes setup codec replace pending input body tag width state reserve client before =
      (do let digest ← $ᵗ CtxDigest
          let result ← stopped modes setup codec replace pending input body tag width state reserve client before amount
            (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone
          pure (digest,result)) := by
  unfold experiment
  apply bind_congr
  intro digest
  have fixed (platform : Platform) : continuation modes setup codec replace pending input body tag width state client platform digest =
      continuation modes setup codec replace pending input body tag width state client platform default := by
    exact congrArg (Functor.map (fun result => (result,platform)))
      (PqxdhRecordFactsOriginFailedGuess.continuation_fixed modes setup codec replace pending input body tag width state (client platform) (noSeal platform) digest)
  cases encoded : (hiddenResult codec.frameWrite pending input body tag width digest state).1 with
  | none =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,pure_bind,Option.isNone_none,ite_true,stopped,fixed,bind_map_left]
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,bind_pure_comp,Option.isNone_some,stopped,sized digest value encoded]
      simp only [Bool.false_eq_true,ite_false,map_bind,bind_assoc]
      apply bind_congr
      intro allocated
      cases allocated.1 <;> simp only [Option.isNone_none,Option.isNone_some,ite_true,ite_false,pure_bind,fixed,StateT.run_pure,Bool.false_eq_true,map_pure,Functor.map_map]

/-- Guessing any one selected hidden seal commitment after writer failure or actual public reserve refusal costs two uniform point masses, with no failure conditioning. -/
theorem guess_bound (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body tag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (guess : (X × CtxPrivate n) × Platform → Option CtxDigest) :
    𝒟[experiment modes setup codec replace pending input body tag width state reserve client before]
      {result | result.2.bind guess=some result.1} ≤ 2 * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [experiment_form modes setup codec replace pending input body tag width state reserve client before amount sized noSeal]
  have bounded := PqxdhRecordFactsOriginGuess.one_bit_guess (X := Option ((X × CtxPrivate n) × Platform))
    (fun digest => (hiddenResult codec.frameWrite pending input body tag width digest state).1.isNone)
    (stopped modes setup codec replace pending input body tag width state reserve client before amount)
    (fun result => result.bind guess)
  generalize hsample : ($ᵗ CtxDigest : ProbComp CtxDigest) = sample at bounded ⊢
  exact bounded

/-- A finite adaptive family of subsequent raw-record guesses uses the original receive budget once per attempted digest. -/
theorem guesses_bound (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body tag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (PqxdhRecordFactsOriginMuteServices.IsTargetSealing pending.material) 0)
    (attempts : Nat) (guess : Fin attempts → (X × CtxPrivate n) × Platform → Option CtxDigest) :
    𝒟[experiment modes setup codec replace pending input body tag width state reserve client before]
      {result | ∃ index,result.2.bind (guess index)=some result.1} ≤ 2 * attempts * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  have cover : {result : CtxDigest × Option ((X × CtxPrivate n) × Platform) |
      ∃ index,result.2.bind (guess index)=some result.1} =
      ⋃index : Fin attempts,{result | result.2.bind (guess index)=some result.1} := by
    ext result
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [cover]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun index =>
    guess_bound modes setup codec replace pending input body tag width state reserve client before amount sized noSeal (guess index)).trans ?_)
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_left_comm,le_refl]
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess.experiment_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess.experiment_form
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess.guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess.guess_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess.guesses_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveGuess.guesses_bound
