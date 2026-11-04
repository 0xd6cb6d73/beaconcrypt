-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveWidth
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginCandidateTrace
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess
/-! The selected-seal probability component executes the literal public reserve and effect charges under the existing uniform-instrumentation/private-cache projection. The muted proof additionally clears selected private copies and write-only logs; actual-runtime comparison uses the separately proved observation law. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal MeasureTheory ProbabilityTheory
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginSelectedSeal (hiddenResult)
open PqxdhRecordFactsOriginMuteComplete (project)
open PqxdhRecordFactsOriginMuteServices (IsTargetSealing)
variable {n : Nat} {I KemSK Reader Response X Platform Failure : Type} {base : OracleSpec I}
local instance (T : Type) : MeasurableSpace T := ⊤
local instance (T : Type) : DiscreteMeasurableSpace T := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (CtxDigest × (Option (X × Platform) × CtxPrivate n)) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × (Option (X × Platform) × CtxPrivate n)) := ⟨fun _ => trivial⟩

variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (client : Platform → OracleComp (ServiceSpec n) X) (before : Platform)
    (tag : PqxdhDeploymentInterface.FrameTag)

def tail (reply : Option RawCtxSourceSend.Encrypted) : OracleComp (ServiceSpec n) (Option (X × Platform)) := do
  let _ ← ((ServiceSpec n).query (.publish tag) : OracleComp (ServiceSpec n) _)
  let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
    ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply).run before)
  if gated.1.isNone then
    (fun value => some (value,gated.2)) <$> client gated.2
  else pure none

def fixed (amount : Nat) (absent : Bool) : OracleComp (ServiceSpec n) (Option (X × Platform)) := do
  let _ ← ((ServiceSpec n).query (.publish tag) : OracleComp (ServiceSpec n) _)
  if absent then (fun value => some (value,before)) <$> client before
  else do
    let allocated ← simulateQ RegistrationNativePlatformOriginGateSource.coins ((reserve amount).run before)
    match allocated.1 with
    | .Ok _ => pure none
    | .Err _ => (fun value => some (value,allocated.2)) <$> client allocated.2

private theorem tail_form (reply : Option RawCtxSourceSend.Encrypted) (amount : Nat)
    (sized : ∀ value,reply=some value → value.ciphertext.length=amount) :
    tail reserve client before tag reply=fixed reserve client before tag amount reply.isNone := by
  unfold tail fixed
  apply bind_congr
  intro _published
  cases reply with
  | none => simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,simulateQ_pure,pure_bind,Option.isNone_none,ite_true]
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,simulateQ_bind,
      Option.isNone_some,Bool.false_eq_true,ite_false,sized value rfl,bind_assoc]
    apply bind_congr
    intro allocated
    cases allocated.1 <;> simp only [StateT.run_pure,simulateQ_pure,pure_bind,Option.isNone_none,Option.isNone_some,Bool.false_eq_true,ite_false,ite_true]

private theorem coins_zero (target : Label n) {A : Type} (work : ProbComp A) :
    (simulateQ RegistrationNativePlatformOriginGateSource.coins work).IsQueryBoundP (IsTargetSealing target) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false _ 0)
  intro query
  change OracleComp.IsQueryBoundP (((ServiceSpec n).query (.charge .coin) : OracleComp (ServiceSpec n) _) >>= fun _ => ((ServiceSpec n).query (.coin query) : OracleComp (ServiceSpec n) _)) (IsTargetSealing target) 0
  exact isQueryBoundP_bind (n := 0) (m := 0) (by simp [IsTargetSealing,isQueryBoundP_query_iff]) (fun _ _ => by simp [IsTargetSealing,isQueryBoundP_query_iff])

private theorem fixed_zero (target : Label n) (amount : Nat) (absent : Bool)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (IsTargetSealing target) 0) :
    (fixed reserve client before tag amount absent).IsQueryBoundP (IsTargetSealing target) 0 := by
  unfold fixed
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · simp [IsTargetSealing,isQueryBoundP_query_iff]
  · intro _ _
    cases absent
    · apply isQueryBoundP_bind (n := 0) (m := 0) (coins_zero target _)
      intro allocated _
      cases allocated.1 <;> first | exact isQueryBoundP_pure _ _ _ | simpa only [isQueryBoundP_map_iff] using noSeal allocated.2
    · simpa only [ite_true,isQueryBoundP_map_iff] using noSeal before

variable (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n) (input : CtxSealInput)
    (body bytesTag : Pqxdh.Bytes) (width : bytesTag.length=16) (state : CtxPrivate n)
local notation "muted" => PqxdhRecordFactsOriginMuteServices.interpreter pending.material modes
  (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
  (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace

noncomputable def experiment : ProbComp (CtxDigest × (Option (X × Platform) × CtxPrivate n)) := do
  let digest ← $ᵗ CtxDigest
  let result ← Prod.map id (project pending.material) <$>
    (simulateQ muted (tail reserve client before tag (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1)).run
      (hiddenResult codec.frameWrite pending input body bytesTag width digest state).2
  pure (digest,result)

noncomputable def stopped (amount : Nat) (absent : Bool) : ProbComp (Option (X × Platform) × CtxPrivate n) :=
  Prod.map id (project pending.material) <$>
    (simulateQ muted (fixed reserve client before tag amount absent)).run
      (hiddenResult codec.frameWrite pending input body bytesTag width default state).2

/-- Both literal reserve branches retain their platform poststates and effect charges under the named uniform-instrumentation projection; only the writer option depends on the fresh digest. -/
theorem experiment_form (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (IsTargetSealing pending.material) 0) :
    experiment reserve client before tag modes setup codec replace pending input body bytesTag width state =
      (do let digest ← $ᵗ CtxDigest
          let result ← stopped reserve client before tag modes setup codec replace pending input body bytesTag width state amount
            (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1.isNone
          pure (digest,result)) := by
  unfold experiment stopped
  apply bind_congr
  intro digest
  rw [tail_form reserve client before tag _ amount (sized digest)]
  rw [PqxdhRecordFactsOriginMuteComplete.program_congr pending.material modes setup codec replace _
    (fixed_zero reserve client before tag pending.material amount _ noSeal) _ _
    (PqxdhRecordFactsOriginSelectedSeal.hidden_project codec.frameWrite pending input body bytesTag width digest default state)]

/-- One subsequent raw candidate in the same explicitly normalized source continuation costs two uniform point masses, without conditioning on refusal. -/
theorem guess_bound (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (guess : Option (X × Platform) × CtxPrivate n → Option CtxDigest) :
    𝒟[experiment reserve client before tag modes setup codec replace pending input body bytesTag width state]
      {result | guess result.2=some result.1} ≤ 2 * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [experiment_form reserve client before tag modes setup codec replace pending input body bytesTag width state amount sized noSeal]
  have bounded := PqxdhRecordFactsOriginGuess.one_bit_guess (X := Option (X × Platform) × CtxPrivate n)
    (fun digest => (hiddenResult codec.frameWrite pending input body bytesTag width digest state).1.isNone)
    (stopped reserve client before tag modes setup codec replace pending input body bytesTag width state amount) guess
  generalize hsample : ($ᵗ CtxDigest : ProbComp CtxDigest) = sample at bounded ⊢
  exact bounded

/-- The original finite family of raw attempts costs the same coefficient-two receive allowance in the counter-retaining selected source experiment. -/
theorem guesses_bound (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(client platform).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (attempts : Nat) (guess : Fin attempts → Option (X × Platform) × CtxPrivate n → Option CtxDigest) :
    𝒟[experiment reserve client before tag modes setup codec replace pending input body bytesTag width state]
      {result | ∃ index,guess index result.2=some result.1} ≤ 2 * attempts * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  have cover : {result : CtxDigest × (Option (X × Platform) × CtxPrivate n) |
      ∃index,guess index result.2=some result.1} = ⋃index : Fin attempts,{result | guess index result.2=some result.1} := by
    ext result
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [cover]
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum fun index =>
    guess_bound reserve client before tag modes setup codec replace pending input body bytesTag width state amount sized noSeal (guess index)).trans ?_)
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_left_comm,le_refl]

/-- Every resumed source result is a supported reply of the same literal continuation at its actual reached public platform state. -/
theorem experiment_client (digest : CtxDigest) (value : X) (platform : Platform) (after : CtxPrivate n)
    (supported : (digest,(some (value,platform),after)) ∈ support
      (experiment reserve client before tag modes setup codec replace pending input body bytesTag width state)) :
    value ∈ support (client platform) := by
  unfold experiment at supported
  generalize hsample : ($ᵗ CtxDigest : ProbComp CtxDigest) = sample at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨sampled,_drawn,continued⟩ := supported
  simp only [bind_pure_comp,support_map] at continued
  obtain ⟨actual,called,same⟩ := continued
  have first := congrArg (fun result => result.2.1) same
  have sourceSupported : actual.1 ∈ support (tail reserve client before tag
      (hiddenResult codec.frameWrite pending input body bytesTag width sampled state).1) := by
    obtain ⟨raw,reached,projected⟩ := called
    have sameValue := congrArg (fun result : Option (X × Platform) × CtxPrivate n => result.1) projected
    change raw.1=actual.1 at sameValue
    rw [← sameValue]
    exact support_simulateQ_run'_subset muted _ (hiddenResult codec.frameWrite pending input body bytesTag width sampled state).2 (by
      rw [StateT.run'_eq,support_map]
      exact ⟨raw,reached,rfl⟩)
  rw [first] at sourceSupported
  simp only [tail,mem_support_bind_iff] at sourceSupported
  obtain ⟨_published,_publication,gated,_gated,returned⟩ := sourceSupported
  split at returned
  · rw [support_map] at returned
    obtain ⟨actualValue,possible,equal⟩ := returned
    have both := Option.some.inj equal
    have values := congrArg Prod.fst both
    have platforms := congrArg Prod.snd both
    change actualValue=value at values
    change gated.2=platform at platforms
    subst actualValue
    rw [← platforms]
    exact possible
  · simp only [mem_support_pure_iff,reduceCtorEq] at returned

section CandidateTrace
variable {A : Type}
variable (future : Platform → OracleComp (ServiceSpec n) A)
local notation "tracedClient" => fun platform => PqxdhRecordFactsOriginCandidateTrace.traced
  (PqxdhRecordFactsOriginRawGuess.serviceCandidate codec.frameRead) (future platform) []

/-- The original receive category controls all public raw candidates after a refused source send, including malformed input and failed openings, with the literal reserve program and its effect charge retained. -/
theorem trace_bound (amount : Nat)
    (sized : ∀ digest value,(hiddenResult codec.frameWrite pending input body bytesTag width digest state).1=some value → value.ciphertext.length=amount)
    (noSeal : ∀ platform,(future platform).IsQueryBoundP (IsTargetSealing pending.material) 0)
    (cap : Nat) (bounded : ∀ platform,(future platform).IsQueryBoundP
      (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1) cap) :
    𝒟[experiment reserve tracedClient before tag modes setup codec replace pending input body bytesTag width state]
      {result | ∃ value platform,result.2.1=some (value,platform) ∧ result.1 ∈ value.2} ≤
        2 * cap * ((2^512 : Nat) : ℝ≥0∞)⁻¹ := by
  refine le_trans ?_ (guesses_bound reserve tracedClient before tag modes setup codec replace pending input body bytesTag width state amount sized
    (fun platform => PqxdhRecordFactsOriginCandidateTrace.traced_queries _ (future platform) [] _ 0 (noSeal platform)) cap
    (fun index result => result.1.bind (fun value => PqxdhRecordFactsOriginCandidateTrace.guess cap index value.1)))
  apply measure_mono_ae
  apply OracleComp.ae_evalDist_of_forall_mem_support
  rintro ⟨digest,result⟩ supported ⟨value,platform,returned,present⟩
  rcases result with ⟨answer,secret⟩
  change answer=some (value,platform) at returned
  subst answer
  have supportedClient := experiment_client reserve tracedClient before tag modes setup codec replace pending input body bytesTag width state
    digest value platform secret supported
  obtain ⟨index,guessed⟩ := PqxdhRecordFactsOriginCandidateTrace.source_guess_complete
    (PqxdhRecordFactsOriginRawGuess.serviceCandidate codec.frameRead)
    (fun query => PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query=1)
    (PqxdhRecordFactsOriginRawGuess.service_candidate_counted codec.frameRead) (future platform) cap (bounded platform)
    value supportedClient digest present
  exact ⟨index,guessed⟩
end CandidateTrace

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.experiment_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.experiment_form
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.guess_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.guesses_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.guesses_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.experiment_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.experiment_client
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginReserveSourceGuess.trace_bound
