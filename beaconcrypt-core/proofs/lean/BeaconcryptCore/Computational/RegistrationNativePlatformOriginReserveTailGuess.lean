-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess
/-! The selected source bound needs only the actual stopped reserve continuations, rather than unsupported claims about the future at every hypothetical platform state. The literal reserve program and effect charges remain executable under the existing uniform-instrumentation projection. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal MeasureTheory ProbabilityTheory
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
open PqxdhRecordFactsOriginMuteComplete (project)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing)
open RegistrationNativePlatformOriginReserveSourceGuess (tail fixed)
variable {n : Nat} {I KemSK Reader Response X Platform Failure : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CtxDigest × (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n)) := ⟨fun _ => trivial⟩
variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (future : Platform → OracleComp (ServiceSpec n) X) (before : Platform)
    (tag : PqxdhDeploymentInterface.FrameTag)

private theorem tail_form (reply : Option RawCtxSourceSend.Encrypted) (amount : Nat)
    (sized : ∀value,reply=some value → value.ciphertext.length=amount) :
    tail reserve future before tag reply=fixed reserve future before tag amount reply.isNone := by
  unfold tail fixed
  apply bind_congr
  intro _
  cases reply with
  | none => simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,simulateQ_pure,pure_bind,Option.isNone_none,ite_true]
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,simulateQ_bind,
      Option.isNone_some,Bool.false_eq_true,ite_false,sized value rfl,bind_assoc]
    apply bind_congr
    intro allocated
    cases allocated.1 <;> simp only [StateT.run_pure,simulateQ_pure,pure_bind,Option.isNone_none,Option.isNone_some,Bool.false_eq_true,ite_false,ite_true]

variable (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body bytesTag : Pqxdh.Bytes) (width : bytesTag.length=16) (state : CtxPrivate n)
local notation "muted" => PqxdhRecordFactsOriginMuteServices.interpreter pending.material modes
  (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
  (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
local notation "traced" => PqxdhRecordFactsOriginCandidateTrace.traced (PqxdhRecordFactsOriginRawGuess.serviceCandidate codec.frameRead)

noncomputable def experiment : ProbComp (CtxDigest × (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n)) := do
  let digest ← $ᵗ CtxDigest
  let result ← Prod.map id (project pending.material) <$>
    (simulateQ muted (traced (tail reserve future before tag (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1) [])).run
      (hiddenResult codec.frameWrite pending input body bytesTag width digest state).2
  pure (digest,result)

noncomputable def stopped (amount : Nat) (absent : Bool) : ProbComp (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n) :=
  Prod.map id (project pending.material) <$>
    (simulateQ muted (traced (fixed reserve future before tag amount absent) [])).run
      (hiddenResult codec.frameWrite pending input body bytesTag width default state).2

/-- The full source tail has two fixed stopped continuations. Its zero-seal premise is only on those literal reserve ASTs, retaining actual platform outcomes and the non-uniform instrumentation fields. -/
theorem experiment_form (amount : Nat)
    (sized : ∀digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP (IsTargetSealing pending.material) 0) :
    experiment reserve future before tag modes setup codec replace pending input body bytesTag width state =
      (do let digest ← $ᵗ CtxDigest
          let result ← stopped reserve future before tag modes setup codec replace pending input body bytesTag width state amount
            (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1.isNone
          pure (digest,result)) := by
  unfold experiment stopped
  apply bind_congr
  intro digest
  rw [tail_form reserve future before tag _ amount (sized digest)]
  rw [PqxdhRecordFactsOriginMuteComplete.program_congr pending.material modes setup codec replace _
    (PqxdhRecordFactsOriginCandidateTrace.traced_queries _ _ [] _ 0 (noSeal _)) _ _
    (PqxdhRecordFactsOriginSelectedSeal.hidden_project codec.frameWrite pending input body bytesTag width digest default state)]

private theorem guess_bound (amount : Nat)
    (sized : ∀digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (guess : (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n) → Option CtxDigest) :
    𝒟[experiment reserve future before tag modes setup codec replace pending input body bytesTag width state]
      {result | guess result.2=some result.1} ≤ 2 * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [experiment_form reserve future before tag modes setup codec replace pending input body bytesTag width state amount sized noSeal]
  have bounded := PqxdhRecordFactsOriginGuess.one_bit_guess (X := ((Option (X × Platform)) × List CtxDigest) × CtxPrivate n)
    (fun digest => (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1.isNone)
    (stopped reserve future before tag modes setup codec replace pending input body bytesTag width state amount) guess
  generalize hsample : ($ᵗ CtxDigest : ProbComp CtxDigest)=sample at bounded ⊢
  exact bounded

private theorem stopped_length (amount : Nat) (absent : Bool) (cap : Nat)
    (bounded : (fixed reserve future before tag amount absent).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) cap)
    (result : (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n))
    (supported : result ∈ support (stopped reserve future before tag modes setup codec replace pending input body bytesTag width state amount absent)) :
    result.1.2.length≤cap := by
  unfold stopped at supported
  rw [support_map] at supported
  obtain ⟨actual,called,rfl⟩ := supported
  have free : actual.1 ∈ support (traced (fixed reserve future before tag amount absent) []) :=
    support_simulateQ_run'_subset muted _ _ (by
      rw [StateT.run'_eq,support_map]
      exact ⟨actual,called,rfl⟩)
  simpa only [Prod.map,id_eq,List.length_nil,Nat.zero_add] using
    PqxdhRecordFactsOriginCandidateTrace.traced_length _ _
      (PqxdhRecordFactsOriginRawGuess.service_candidate_counted codec.frameRead) _ [] cap bounded _ free

/-- All actual future candidates after reserve refusal cost the coefficient-two raw allowance. Only the literal stopped reserve syntax is bounded; hypothetical platform states are not required. -/
theorem trace_bound (amount : Nat)
    (sized : ∀digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (cap : Nat) (bounded : ∀absent,(fixed reserve future before tag amount absent).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) cap) :
    𝒟[experiment reserve future before tag modes setup codec replace pending input body bytesTag width state]
      {result | result.1 ∈ result.2.1.2} ≤ 2 * cap * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  have union : 𝒟[experiment reserve future before tag modes setup codec replace pending input body bytesTag width state]
      {result | ∃index : Fin cap,PqxdhRecordFactsOriginCandidateTrace.guess cap index result.2.1=some result.1} ≤
      2 * cap * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
    have cover : {result : CtxDigest × (((Option (X × Platform)) × List CtxDigest) × CtxPrivate n) |
      ∃index : Fin cap,PqxdhRecordFactsOriginCandidateTrace.guess cap index result.2.1=some result.1} =
      ⋃index : Fin cap,{result | PqxdhRecordFactsOriginCandidateTrace.guess cap index result.2.1=some result.1} := by
      ext result
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    rw [cover]
    refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun index =>
      guess_bound reserve future before tag modes setup codec replace pending input body bytesTag width state amount sized noSeal
        (fun result => PqxdhRecordFactsOriginCandidateTrace.guess cap index result.1)).trans ?_)
    simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_left_comm,le_refl]
  refine le_trans ?_ union
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  intro result supported present
  have length : result.2.1.2.length≤cap := by
    rw [experiment_form reserve future before tag modes setup codec replace pending input body bytesTag width state amount sized noSeal] at supported
    generalize hsample : ($ᵗ CtxDigest : ProbComp CtxDigest)=sample at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨digest,_sampled,continued⟩ := supported
    simp only [bind_pure_comp,support_map] at continued
    obtain ⟨actual,called,rfl⟩ := continued
    exact stopped_length reserve future before tag modes setup codec replace pending input body bytesTag width state amount _ cap (bounded _) actual called
  exact PqxdhRecordFactsOriginCandidateTrace.guess_complete cap result.2.1 length result.1 present

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess.experiment_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess.experiment_form

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess.trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveTailGuess.trace_bound
