import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceState

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhServerAuthSourceCosts PqxdhServerAuthPendingBudget
open PqxdhServerAuthGapDh PqxdhServerAuthBodyCosts
variable {KemSK : Type}

/-- Direct adversary draws, all accept attempts, public BLAKE2b requests and public Extract-domain HMAC requests. -/
def entryClasses : Fin 4 → ServerAuthSpec.Domain → Prop :=
  ![IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery]

instance : ∀ i, DecidablePred (entryClasses i) :=
  Fin.cases (inferInstanceAs (DecidablePred IsAuthCoin))
    (Fin.cases (inferInstanceAs (DecidablePred IsAcceptQuery))
      (Fin.cases (inferInstanceAs (DecidablePred IsHashQuery))
        (Fin.cases (inferInstanceAs (DecidablePred IsRomQuery)) (fun i => Fin.elim0 i))))

/-- Immediate actual uniform bill: one possible table read per derivation, the complete source prefix/tail, and no suppressed bad-state work. -/
def entryBill (caps : KemCaps) (query : ServerAuthSpec.Domain) (game : GameState KemSK) : Nat :=
  match query with
  | .inl _ => 1
  | .inr (.accept _) => 32 + caps.encapsCost + 64
  | .inr (.build index _) => 64 * slotWeight (game.pending index)
  | .inr (.finish _) => (caps.decapsCost + 128) * initSentFlag game
  | .inr (.hash _) => 64
  | .inr (.hmac key bytes) => if key = PqxdhSecretInputKdf.zeroSalt ∧ bytes.length = 192 then 64 else 0
  | .inr (.reveal _) => 0

/-- The potential reserves every remaining accept's table/prefix/build work, all pending builds, one active finish, and direct public query work. -/
def entryPotential (caps : KemCaps) (budget : Fin 4 → Nat) (game : GameState KemSK) : Nat :=
  budget 0 + (32 + caps.encapsCost + 128) * budget 1 + 64 * budget 2 + 64 * budget 3 +
    64 * pendingCount game + (caps.decapsCost + 128) * initSentFlag game

/-- The remaining source-interface budget and current token/phase reservations cover each immediate uniform bill. -/
theorem entryBill_le (caps : KemCaps) (query : ServerAuthSpec.Domain) (game : GameState KemSK)
    (valid : ResourceValid game) (budget : Fin 4 → Nat)
    (positive : ∀ i, entryClasses i query → 0 < budget i) :
    entryBill caps query game ≤ entryPotential caps budget game := by
  have coinPos : IsAuthCoin query → 0 < budget 0 := positive 0
  have acceptPos : IsAcceptQuery query → 0 < budget 1 := positive 1
  have hashPos : IsHashQuery query → 0 < budget 2 := positive 2
  have romPos : IsRomQuery query → 0 < budget 3 := positive 3
  rcases query with coin | query
  · have pos := coinPos rfl
    simp only [entryBill, entryPotential]
    omega
  cases query with
  | accept raw =>
      have enough := Nat.mul_le_mul_left (32 + caps.encapsCost + 128) (acceptPos trivial)
      simp only [Nat.mul_one] at enough
      simp only [entryBill, entryPotential]
      omega
  | build index payload =>
      have enough := Nat.mul_le_mul_left 64 (resource_pending_weight game valid index)
      simp only [entryBill, entryPotential]
      omega
  | finish raw => simp only [entryBill, entryPotential]; omega
  | hash bytes =>
      have enough := Nat.mul_le_mul_left 64 (hashPos trivial)
      simp only [Nat.mul_one] at enough
      simp only [entryBill, entryPotential]
      omega
  | hmac key bytes =>
      simp only [entryBill]
      split_ifs with inside
      · have enough := Nat.mul_le_mul_left 64 (romPos inside)
        simp only [Nat.mul_one] at enough
        simp only [entryPotential]
        omega
      · exact Nat.zero_le _
  | reveal key => exact Nat.zero_le _

/-- Every supported footprint pays the immediate work and leaves enough reservation for the complete adaptive continuation. -/
theorem entry_potential_step (caps : KemCaps) (query : ServerAuthSpec.Domain)
    (before after : GameState KemSK) (valid : ResourceValid before) (step : ResourceStep query before after)
    (budget : Fin 4 → Nat) (positive : ∀ i, entryClasses i query → 0 < budget i) :
    entryBill caps query before +
      entryPotential caps (fun i => if entryClasses i query then budget i - 1 else budget i) after ≤
        entryPotential caps budget before := by
  have coinPos : IsAuthCoin query → 0 < budget 0 := positive 0
  have acceptPos : IsAcceptQuery query → 0 < budget 1 := positive 1
  have hashPos : IsHashQuery query → 0 < budget 2 := positive 2
  have romPos : IsRomQuery query → 0 < budget 3 := positive 3
  have pending := ResourceStep.pending query before after valid step
  have phase := ResourceStep.flag query before after step
  rcases query with coin | query
  · have pos := coinPos rfl
    simp only [PendingStep] at pending
    simp only [resourceFlag] at phase
    simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase, pending]
    omega
  cases query with
  | accept raw =>
      have pos := acceptPos trivial
      have decrement : budget 1 - 1 + 1 = budget 1 := by omega
      simp only [PendingStep] at pending
      simp only [resourceFlag] at phase
      simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase]
      nlinarith
  | build index payload =>
      simp only [PendingStep] at pending
      simp only [resourceFlag] at phase
      simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase]
      omega
  | finish raw =>
      simp only [PendingStep] at pending
      simp only [resourceFlag] at phase
      simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase, pending]
      omega
  | hash bytes =>
      have pos := hashPos trivial
      simp only [PendingStep] at pending
      simp only [resourceFlag] at phase
      simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase, pending]
      omega
  | hmac key bytes =>
      simp only [PendingStep] at pending
      simp only [resourceFlag] at phase
      by_cases inside : key = PqxdhSecretInputKdf.zeroSalt ∧ bytes.length = 192
      · have pos := romPos inside
        simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase, pending, inside]
        omega
      · simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase, pending, inside]
  | reveal key =>
      simp only [PendingStep] at pending
      simp only [resourceFlag] at phase
      simp [entryBill, entryPotential, entryClasses, IsAuthCoin, IsAcceptQuery, IsHashQuery, IsRomQuery, phase, pending]

/-- The same original adaptive client pays the proved potential through the complete hidden handler. The immediate callback bill is an explicit resource obligation, discharged by the concrete services. -/
theorem hidden_client_uniform {ι : Type} {baseSpec : OracleSpec ι} {Reader Response α : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (caps : KemCaps)
    (immediate : ∀ query state,
      ((hiddenHandler setup codec checks context Q j services query).run state).IsTotalQueryBound
        (entryBill caps query state.1.1))
    (work : OracleComp ServerAuthSpec α) (budget : Fin 4 → Nat)
    (bounded : ∀ i, work.IsQueryBoundP (entryClasses i) (budget i))
    (state : HiddenState KemSK) (valid : ResourceValid state.1.1) :
    ((simulateQ (hiddenHandler setup codec checks context Q j services) work).run state).IsTotalQueryBound
      (entryPotential caps budget state.1.1) := by
  rw [← isQueryBoundP_true_iff]
  apply run_potential_invariant (hiddenHandler setup codec checks context Q j services)
    (fun state => ResourceValid state.1.1) entryClasses (fun _ => True)
    (fun budget state => entryPotential caps budget state.1.1)
    (fun query before available invariant positive => ?_) work budget bounded state valid
  refine ⟨entryBill caps query before.1.1, (immediate query before).isQueryBoundP,
    entryBill_le caps query before.1.1 invariant available positive, ?_⟩
  intro result supported
  have footprint := hiddenHandler_resources setup codec checks context Q j services query before result supported
  exact ⟨ResourceStep.valid query before.1.1 result.2.1.1 invariant footprint,
    entry_potential_step caps query before.1.1 result.2.1.1 invariant footprint available positive⟩

/-- Complete interpreter bill after context generation; the omitted-entry challenge sampler is separate. -/
def entryRunBudget (caps : KemCaps) (qCoin Q qHash qH : Nat) : Nat :=
  qCoin + (32 + caps.encapsCost + 128) * Q + 64 * qHash + 64 * qH + caps.decapsCost + 128

/-- The literal initial context has no pending builds and at most one active finish. -/
theorem entry_initial_potential {ι : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (context : Context KemSK) (caps : KemCaps)
    (qCoin Q qHash qH : Nat) :
    entryPotential caps ![qCoin, Q, qHash, qH] (contextState setup context) ≤
      entryRunBudget caps qCoin Q qHash qH := by
  have enough := Nat.mul_le_mul_left (caps.decapsCost + 128) (initSentFlag_le (contextState setup context))
  simp only [Nat.mul_one, contextState] at enough
  simp [entryPotential, contextState, pending_initial, entryRunBudget]
  omega

/-- Context generation retains all four 32-byte samplers, the actual KEM/base work and complete Phase1 publication in the original R1 experiment order. -/
theorem context_uniform {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (caps : KemCaps) (bounded : KemBound setup caps) :
    (contextSample setup codec).IsTotalQueryBound (128 + caps.keygenCost) := by
  unfold contextSample
  refine (isTotalQueryBound_bind (n₂ := 96 + caps.keygenCost)
    PqxdhJointIdentity.sampleSeed_uniform_bound (fun seed => ?_)).mono (by omega)
  refine (isTotalQueryBound_bind (n₂ := 64 + caps.keygenCost)
    PqxdhJointGapDh.sampleScalar_uniform (fun scalar => ?_)).mono (by omega)
  refine (isTotalQueryBound_bind (n₂ := 32 + caps.keygenCost)
    PqxdhJointIdentity.sampleSeed_uniform_bound (fun beaconSeed => ?_)).mono (by omega)
  refine isTotalQueryBound_bind PqxdhJointGapDh.sampleScalar_uniform (fun oneTime => ?_)
  refine (isTotalQueryBound_bind (n₂ := 0) (keygen_uniform setup caps bounded) (fun keys => ?_)).mono (by omega)
  rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
  exact phase1_uniform setup codec beaconSeed _ oneTime keys.1 keys.2

/-- Expanded complete ordinary continuation bill, including actual source context, every KEM/base contribution and every possible retained-table sample. Challenge-game sampling remains separate. -/
theorem entry_budget_expanded (caps : KemCaps) (qCoin Q qHash qH : Nat) :
    128 + caps.keygenCost + entryRunBudget caps qCoin Q qHash qH =
      256 + qCoin + 160 * Q + 64 * (qHash + qH) +
      caps.keygenUniform + Q * caps.encapsUniform + caps.decapsUniform +
      caps.baseUniform * (caps.keygenBase + Q * caps.encapsBase + caps.decapsBase) := by
  simp only [entryRunBudget, KemCaps.keygenCost, KemCaps.encapsCost, KemCaps.decapsCost]
  ring

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entryBill_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entryBill_le
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_potential_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_potential_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.hidden_client_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_initial_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_initial_potential
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.context_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.context_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_budget_expanded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.entry_budget_expanded
