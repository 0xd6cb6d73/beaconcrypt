import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixStop

/-! Actual callback-completion publication markers, with exact original-source erasure and publication-kill interpretation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState PqxdhServerAuthCtxCalls
open PqxdhServerAuthPublicationPrefixStop
variable {ι KemSK Reader WireResponse Result : Type} {baseSpec : OracleSpec ι}

/-- Original source state remains complete between callbacks. Each private marker records the actual public reply and preceding source mark only after the entire original callback returned. -/
noncomputable def program (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) :
    (Local KemSK × Option Nat) → OracleComp Spec (Option (Result × (Local KemSK × Option Nat))) :=
  OracleComp.recOn work
    (fun value state => pure (some (value, state)))
    (fun query _ recurse before => do
      let result ← simulateQ liftDynamic ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run before)
      let _ ← Spec.query (.inr (PqxdhServerAuthPublicationFilter.published query before.1 result.1))
      match result.1 with
      | none => pure none
      | some reply => recurse reply result.2)

/-- Only the terminal local state of an originally refused run is projected; no component effects or preceding complete callback are omitted. -/
def optional {S Value : Type} (result : Option Value × S) : Option (Value × S) :=
  result.1.map fun value => (value, result.2)

/-- Erasing private callback markers preserves the literal original adaptive source program, including all component queries and original optional answers. -/
theorem program_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    simulateQ erase (program setup codec checks context rest Q j work state) =
      optional <$> (simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      change simulateQ erase (do
        let result ← simulateQ liftDynamic ((PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)
        let _ ← Spec.query (.inr (PqxdhServerAuthPublicationFilter.published query state.1 result.1))
        match result.1 with
        | none => pure none
        | some reply => program setup codec checks context rest Q j (next reply) result.2) = _
      simp only [simulateQ_bind, simulateQ_spec_query, erase_lift, erase, pure_bind,
        OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
      refine bind_congr fun result => ?_
      cases result.1 with
      | none => rfl
      | some reply => exact ih reply result.2

/-- Killing the exact source publication markers yields the actual filtered source continuation. The join removes only the extra interpreter option, while all component work before stopping is retained. -/
theorem program_kill (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) :
    Option.join <$> (simulateQ kill (program setup codec checks context rest Q j work state)).run =
      ((simulateQ (PqxdhServerAuthPublicationFilter.sourceFiltered setup codec checks context rest Q j) work).run state).run := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      change Option.join <$> (simulateQ kill (do
        let result ← simulateQ liftDynamic ((PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)
        let _ ← Spec.query (.inr (PqxdhServerAuthPublicationFilter.published query state.1 result.1))
        match result.1 with
        | none => pure none
        | some reply => program setup codec checks context rest Q j (next reply) result.2)).run = _
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, kill_lift,
        bind_map_left, Option.elim_some, map_bind, StateT.run_bind]
      dsimp only [StateT.run, PqxdhServerAuthPublicationFilter.sourceFiltered, OptionT.run, OptionT.mk]
      rw [bind_map_left]
      refine bind_congr (m := OracleComp AdaptiveCtxDynamicKnownKeys.Spec) fun result => ?_
      simp only [kill, PqxdhServerAuthPublicationFilter.sourceGate]
      split_ifs with published
      · rfl
      · cases result.1 with
        | none => rfl
        | some reply => exact ih reply result.2

/-- The original context and residual draws precede the complete marked source continuation in their actual order. Terminal observations add no interface request. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) : OracleComp Spec Unit := do
  let context ← simulateQ liftDynamic (simulateQ PqxdhServerAuthCtxAmbient.coin (contextSample setup codec))
  let rest ← simulateQ liftDynamic (simulateQ PqxdhServerAuthCtxAmbient.coin ($ᵗ Residual))
  let _ ← program setup codec checks context rest Q j (adversary (contextInput setup false context))
    (PqxdhServerAuthCtxReserve.initial setup context).1
  pure ()

/-- Erasing actual publication markers recovers the unchanged whole source client, with only its unused terminal decision discarded. -/
theorem client_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    simulateQ erase (client setup codec checks adversary Q j) =
      (fun _ => ()) <$> PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j := by
  simp only [client, simulateQ_bind, erase_lift, bind_pure_comp, simulateQ_map,
    program_erase, Functor.map_map, PqxdhServerAuthCtxExperiment.client,
    PqxdhServerAuthCtxExperiment.continuation, map_bind]
  rfl

/-- Killing the actual markers is precisely the fully sampled source used in the established capture bound. Only terminal values are discarded; the original complete callback programs are identical. -/
theorem client_kill (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) :
    (fun _ => ()) <$> (simulateQ kill (client setup codec checks adversary Q j)).run =
      PqxdhServerAuthPublicationDominance.actualClient setup codec checks adversary Q j := by
  simp only [client, simulateQ_bind, OptionT.run_bind, Option.elimM, kill_lift,
    bind_map_left, Option.elim_some, map_bind, PqxdhServerAuthPublicationDominance.actualClient]
  refine bind_congr fun context => ?_
  refine bind_congr fun rest => ?_
  have same := congrArg (fun work => (fun _ => ()) <$> work)
    (program_kill setup codec checks context rest Q j (adversary (contextInput setup false context))
      (PqxdhServerAuthCtxReserve.initial setup context).1)
  simp only [Functor.map_map] at same
  simp only [simulateQ_pure, OptionT.run_pure, bind_pure_comp]
  rw [← same, ← bind_pure_comp]
  refine bind_congr fun result => ?_
  cases result <;> rfl

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh

/-- The actual source's clean first-raw prefix has the established unconditional reference loss. Publication after the captured raw cannot affect this event. -/
theorem clean_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : AdaptiveCtxReceive.RawDecoder) :
    (Pr{let result ← (AdaptiveCtxDynamicKnownKeys.sourceGame true decode setup.source.crypto
        (capture (client setup codec checks adversary Q j) none false))}[result.1.1 = false ∧ PqxdhServerAuthPublicationGuess.Hit
      (PqxdhServerAuthPublicationRandom.decodedTag decode) result.1.2]).toReal ≤
      PqxdhServerAuthPublicationPrivacy.loss setup codec checks adversary Q j decode
        (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  rw [source_clean true decode setup.source.crypto _ none _ (by simp [PqxdhServerAuthPublicationGuess.Hit])]
  rw [← PqxdhServerAuthPublicationPruning.dynamic_map (fun _ => ())
    (simulateQ kill (client setup codec checks adversary Q j)).run none, client_kill]
  exact PqxdhServerAuthPublicationDominance.actual_bound setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j decode

/-- A pure terminal observation commutes with the complete marked adaptive source program. The original public journal can therefore be retained for the proof and erased only at capture. -/
theorem program_map {Mapped : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : Residual) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result) (state : Local KemSK × Option Nat) (f : Result → Mapped) :
    program setup codec checks context rest Q j (f <$> work) state =
      Option.map (Prod.map f id) <$> program setup codec checks context rest Q j work state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      rw [map_bind]
      change (do
        let result ← simulateQ liftDynamic ((PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)
        let _ ← Spec.query (.inr (PqxdhServerAuthPublicationFilter.published query state.1 result.1))
        match result.1 with
        | none => pure none
        | some reply => program setup codec checks context rest Q j (f <$> next reply) result.2) =
        Option.map (Prod.map f id) <$> (do
          let result ← simulateQ liftDynamic ((PqxdhServerAuthCtxReserve.stopped
            (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)
          let _ ← Spec.query (.inr (PqxdhServerAuthPublicationFilter.published query state.1 result.1))
          match result.1 with
          | none => pure none
          | some reply => program setup codec checks context rest Q j (next reply) result.2)
      simp only [map_bind]
      refine bind_congr fun result => ?_
      refine bind_congr fun _ => ?_
      cases result.1 with
      | none => rfl
      | some reply => exact ih reply result.2

/-- All generalized component budgets of the actual original client also bound its marked first-raw capture. Markers are private local bookkeeping, not free ambient oracle work. -/
theorem capture_budget {Budget : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (budget : Budget)
    (canQuery : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Prop)
    (cost : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Budget → Budget)
    (bounded : (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBound budget canQuery cost) :
    (capture (client setup codec checks adversary Q j) none false).IsQueryBound budget canQuery cost := by
  apply PqxdhServerAuthPublicationPruning.query_bound _ _ (capture_prunes _ none false) budget canQuery cost
  simpa only [client_erase, isQueryBound_map_iff] using bounded

/-- The clean-prefix observer retains all source context/KEM/base work, both public routes, one selected seal, zero selected openings and the source-derived plaintext allowance. -/
theorem capture_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) :
    let work := capture (client setup codec checks adversary Q j) none false
    let H := entryReductionBudget caps qCoin Q qHash qH + 76
    work.IsTotalQueryBound H ∧
      work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute H ∧
      work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute H ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 1 ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      AdaptiveCtxDynamicKnownBounds.PlaintextBound work Aeneas.Std.Usize.max := by
  have total := PqxdhServerAuthCtxResources.client_total setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j
  have bills := PqxdhServerAuthCtxResources.client_bills setup codec checks caps bounded adversary
    qCoin Q qHash qH coins accepts hashes rom j
  exact ⟨capture_budget setup codec checks adversary Q j _ _ _ total,
    capture_budget setup codec checks adversary Q j _ _ _ bills.1,
    capture_budget setup codec checks adversary Q j _ _ _ bills.2.1,
    capture_budget setup codec checks adversary Q j _ _ _ bills.2.2.1,
    capture_no_raw _ none false,
    capture_budget setup codec checks adversary Q j _ _ _
      (PqxdhServerAuthCtxByteBounds.client_plaintext setup codec checks adversary Q j)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.program_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.program_kill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.program_kill
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.client_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.client_kill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.client_kill
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.clean_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.clean_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.program_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.capture_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.capture_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.capture_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource.capture_bills
