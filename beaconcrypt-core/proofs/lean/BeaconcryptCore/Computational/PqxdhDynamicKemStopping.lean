import BeaconcryptCore.Computational.PqxdhDynamicKemSource
import BeaconcryptCore.Computational.PqxdhDynamicKemPost

/-!
The ordinary reserved source answers a successful selected-key reveal and remembers that disclosure; the executable reduction stops before answering it. Fresh complete output probabilities agree because the retained disclosure flag cannot be cleared by any adaptive suffix. Missing/future handles reject before setting the flag. This is an exact KEM disclosure monitor, not an assumption that an arbitrary adversary decision is false after compromise. The full protocol freshness predicate must still imply this monitor at its selected target.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemStopping
open PqxdhDynamicKemRouter PqxdhKemIndCca
open PqxdhLiveKemBirth (Query PoolSpec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

def Good (state : State KemSK) : Prop := state.forbiddenReveal = false

/-- The ordinary source returns every existing requested secret. Its private monitor records a selected disclosure only after successful lookup. -/
def normal (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) :
    QueryImpl (PoolSpec KemSK) (OptionT (StateT (State KemSK) ProbComp)) := fun query =>
  match query with
  | .reveal index => OptionT.mk fun state =>
      match (pairs.take state.created)[index]? with
      | none => pure (some none, record (.reveal index) none state)
      | some pair => pure (some (some pair.2), record (.reveal index) (some pair.2)
          { state with forbiddenReveal := if index = selected then true else state.forbiddenReveal })
  | query => source baseImpl kem selected pairs query

set_option backward.isDefEq.respectTransparency false in
/-- The stopped source cannot remove a previous successful selected disclosure. -/
theorem source_good (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (result : Option ((PoolSpec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((source baseImpl kem selected pairs query).run).run state))
    (good : Good result.2) : Good state := by
  cases query with
  | create =>
      simp only [source, OptionT.run_mk, StateT.run] at supported
      split at supported <;> simp only [mem_support_pure_iff] at supported
      all_goals subst result
      all_goals exact good
  | decapsulate index ciphertext =>
      simp only [source, OptionT.run_mk, StateT.run, bind_pure_comp] at supported
      split at supported <;> simp only [support_map, Set.mem_image] at supported
      all_goals obtain ⟨reply, _, rfl⟩ := supported
      all_goals exact good
  | reveal index =>
      simp only [source, OptionT.run_mk, StateT.run] at supported
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        exact good
      · split at supported <;> simp only [mem_support_pure_iff] at supported
        all_goals subst result
        · exact False.elim (Bool.noConfusion good)
        · exact good

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary source operation preserves previous disclosure, including actual successful subsequent reveals. -/
theorem normal_good (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (result : Option ((PoolSpec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl kem selected pairs query).run).run state))
    (good : Good result.2) : Good state := by
  cases query with
  | create => exact source_good baseImpl kem selected pairs .create state result supported good
  | decapsulate index ciphertext => exact source_good baseImpl kem selected pairs (.decapsulate index ciphertext) state result supported good
  | reveal index =>
      simp only [normal, OptionT.run_mk, StateT.run] at supported
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        exact good
      · simp only [mem_support_pure_iff] at supported
        subst result
        simp only [Good, record] at good
        split at good
        · exact False.elim (Bool.noConfusion good)
        · exact good

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary adaptive ordinary suffix cannot restore the selected disclosure freshness monitor. -/
theorem schedule_good (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (normal baseImpl kem selected pairs) client).run).run state))
    (good : Good result.2) : Good state := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, tail⟩ := supported
      apply normal_good baseImpl kem selected pairs query state head actual
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
        subst result
        exact good
      · exact ih answer after result tail good

/-- Once an actual selected secret has been returned, every complete output retaining freshness has zero probability, irrespective of the adversary's final decision. -/
theorem bad_output_zero (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK)
    (result : Option Result × State KemSK) (bad : ¬ Good state) (good : Good result.2) :
    Pr[= result | ((simulateQ (normal baseImpl kem selected pairs) client).run).run state] = 0 :=
  probOutput_eq_zero_of_not_mem_support fun supported =>
    bad (schedule_good baseImpl kem selected pairs client state result supported good)

def Discloses (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK) : Prop :=
  match query with
  | .reveal index => index = selected ∧ ((pairs.take state.created)[index]?).isSome = true
  | _ => False

set_option backward.isDefEq.respectTransparency false in
/-- Until an actual successful selected reveal, the ordinary and stopped services are the same entire computation. -/
theorem step_agree (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (allowed : ¬ Discloses selected pairs query state) :
    ((normal baseImpl kem selected pairs query).run).run state =
      ((source baseImpl kem selected pairs query).run).run state := by
  cases query with
  | create => rfl
  | decapsulate index ciphertext => rfl
  | reveal index =>
      cases found : (pairs.take state.created)[index]? with
      | none => simp [normal, source, OptionT.run_mk, StateT.run, found]
      | some pair =>
          have other : index ≠ selected := by simpa [Discloses, found] using allowed
          simp only [normal, source, OptionT.run_mk, StateT.run, found, ite_eq_right other]

/-- A successful disclosure has the exact selected existing handle; a failed or future lookup cannot trigger the stop. -/
theorem discloses_shape (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (discloses : Discloses selected pairs query state) :
    query = .reveal selected ∧ ∃ pair, (pairs.take state.created)[selected]? = some pair := by
  cases query with
  | create => exact False.elim discloses
  | decapsulate index ciphertext => exact False.elim discloses
  | reveal index =>
      obtain ⟨rfl, present⟩ := discloses
      exact ⟨rfl, Option.isSome_iff_exists.mp present⟩

set_option backward.isDefEq.respectTransparency false in
/-- Stopping before unavailable selected-secret disclosure preserves the exact probability of every complete fresh source output, not merely the adversary's marginal decision. -/
theorem output_good (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK)
    (result : Option Result × State KemSK) (good : Good result.2) :
    Pr[= result | ((simulateQ (normal baseImpl kem selected pairs) client).run).run state] =
      Pr[= result | ((simulateQ (source baseImpl kem selected pairs) client).run).run state] := by
  classical
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      by_cases allowed : ¬ Discloses selected pairs query state
      · rw [step_agree baseImpl kem selected pairs query state allowed]
        rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
        apply tsum_congr
        rintro ⟨none | answer, after⟩
        · rfl
        · exact congrArg (fun probability =>
            Pr[= (some answer, after) | ((source baseImpl kem selected pairs query).run).run state] * probability)
            (ih answer after)
      · obtain ⟨rfl, pair, found⟩ := discloses_shape selected pairs query state (not_not.mp allowed)
        simp only [normal, source, OptionT.run_mk, StateT.run, found, ite_true, pure_bind,
          Option.elim_some, Option.elim_none]
        refine (bad_output_zero baseImpl kem selected pairs (next (some pair.2))
          (record (.reveal selected) (some pair.2) { state with forbiddenReveal := true })
          result (by simp [Good, record]) good).trans ?_
        symm
        apply probOutput_eq_zero_of_not_mem_support
        intro supported
        change result ∈ support (pure (none, { state with forbiddenReveal := true }) : ProbComp _) at supported
        simp only [mem_support_pure_iff] at supported
        subst result
        exact Bool.noConfusion good

/-- Every original event gated by the exact selected-disclosure monitor has identical probability in the ordinary and stopped source, with its full result and history retained. -/
theorem event_good (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK)
    (event : Option Result × State KemSK → Prop) :
    Pr[fun result => event result ∧ Good result.2 | ((simulateQ (normal baseImpl kem selected pairs) client).run).run state] =
      Pr[fun result => event result ∧ Good result.2 | ((simulateQ (source baseImpl kem selected pairs) client).run).run state] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases good : Good result.2
  · simp [good, output_good baseImpl kem selected pairs client state result good]
  · simp [good]

/-- Actual successful reveal observation, as retained in the original source history; failed reveals do not disclose anything. -/
def disclosed (selected : Nat) (observation : PqxdhLiveKemBirth.Observation KemSK) : Bool :=
  match observation with
  | ⟨.reveal index, some _⟩ => decide (index = selected)
  | _ => false

def Tracked (selected : Nat) (state : State KemSK) : Prop :=
  state.forbiddenReveal = state.history.any (disclosed selected)

/-- The actual empty source starts with the exact successful-reveal history monitor. -/
theorem empty_tracked (selected : Nat) : Tracked selected (empty : State KemSK) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary source disclosure bit is derived from its actual returned secret observations, including optional rejection and all other source operations. -/
theorem normal_tracked (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (tracked : Tracked selected state)
    (result : Option ((PoolSpec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl kem selected pairs query).run).run state)) : Tracked selected result.2 := by
  cases query with
  | create =>
      simp only [normal, source, OptionT.run_mk, StateT.run] at supported
      split at supported <;> simp only [mem_support_pure_iff] at supported
      all_goals subst result
      · exact tracked
      · simpa [Tracked, record, List.any_append, disclosed] using tracked
  | decapsulate index ciphertext =>
      simp only [normal, source, OptionT.run_mk, StateT.run, bind_pure_comp] at supported
      split at supported <;> simp only [support_map, Set.mem_image] at supported
      all_goals obtain ⟨reply, _, rfl⟩ := supported
      all_goals simpa [Tracked, record, List.any_append, disclosed] using tracked
  | reveal index =>
      simp only [normal, OptionT.run_mk, StateT.run] at supported
      split at supported <;> simp only [mem_support_pure_iff] at supported
      all_goals subst result
      · simpa [Tracked, record, List.any_append, disclosed] using tracked
      · by_cases chosen : index = selected
        · simp [Tracked, record, List.any_append, disclosed, chosen]
        · simpa [Tracked, record, List.any_append, disclosed, chosen] using tracked

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive ordinary execution keeps the monitor equal to its actual complete successful-reveal history. -/
theorem schedule_tracked (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK) (tracked : Tracked selected state)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (normal baseImpl kem selected pairs) client).run).run state)) : Tracked selected result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact tracked
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, tail⟩ := supported
      have trackedAfter := normal_tracked baseImpl kem selected pairs query state tracked head actual
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
        subst result
        exact trackedAfter
      · exact ih answer after trackedAfter result tail

/-- Starting with the actual tracked history, stopping preserves every event gated by absence of an actual successful selected-key disclosure in the original history. The monitor invariant is an operational history equality, not a security premise; empty initialization and the full ordinary schedule establish it. -/
theorem history_event (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK) (trackedBefore : Tracked selected state)
    (event : Option Result × State KemSK → Prop) :
    Pr[fun result => event result ∧ result.2.history.any (disclosed selected) = false |
      ((simulateQ (normal baseImpl kem selected pairs) client).run).run state] =
      Pr[fun result => event result ∧ Good result.2 |
        ((simulateQ (source baseImpl kem selected pairs) client).run).run state] := by
  classical
  calc
    _ = Pr[fun result => event result ∧ Good result.2 |
        ((simulateQ (normal baseImpl kem selected pairs) client).run).run state] := by
      rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
      apply tsum_congr
      intro result
      by_cases supported : result ∈ support (((simulateQ (normal baseImpl kem selected pairs) client).run).run state)
      · have tracked := schedule_tracked baseImpl kem selected pairs client state trackedBefore result supported
        change result.2.forbiddenReveal = result.2.history.any (disclosed selected) at tracked
        simp only [Good, tracked]
      · have zero := probOutput_eq_zero_of_not_mem_support supported
        simp only [zero, ite_self]
    _ = _ := event_good baseImpl kem selected pairs client state event

/-- The real empty source discharges the tracked-history premise directly. -/
theorem empty_history_event (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (event : Option Result × State KemSK → Prop) :
    Pr[fun result => event result ∧ result.2.history.any (disclosed selected) = false |
      ((simulateQ (normal baseImpl kem selected pairs) client).run).run empty] =
      Pr[fun result => event result ∧ Good result.2 |
        ((simulateQ (source baseImpl kem selected pairs) client).run).run empty] :=
  history_event baseImpl kem selected pairs client empty (empty_tracked selected) event

/-- The prechallenge executable CCA router preserves the original complete event under its actual successful-reveal freshness gate, starting from the source empty history. -/
theorem pre_event (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK) (present : pairs[selected]? = some (target, secret))
    (client : OracleComp (PoolSpec KemSK) Result) (event : Option Result × State KemSK → Prop) :
    Pr[fun result => event result ∧ result.2.history.any (disclosed selected) = false |
      ((simulateQ (normal baseImpl kem selected pairs) client).run).run empty] =
      Pr[fun result => event result ∧ Good result.2 |
        PqxdhPrivateKemSource.evalKem baseImpl kem secret
          (((simulateQ (pre kem selected (redact selected pairs)) client).run).run empty)] := by
  rw [PqxdhDynamicKemRouter.program_source baseImpl kem selected pairs target secret present]
  exact empty_history_event baseImpl kem selected pairs client event

/-- A postchallenge source event with its actual retained successful-reveal freshness has the same probability through the ordinary blocked CCA interpreter. The complete earlier tracked state is carried into the suffix. -/
theorem post_event (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret))
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen))
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (encapsulated : (challenge, candidate) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)))
    (client : OracleComp (PoolSpec KemSK) Result) (state : State KemSK) (tracked : Tracked selected state)
    (event : Option Result × State KemSK → Prop) :
    Pr[fun result => event result ∧ result.2.history.any (disclosed selected) = false |
      ((simulateQ (normal baseImpl kem selected pairs) client).run).run state] =
      Pr[fun result => event result ∧ Good result.2 |
        PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
          (((simulateQ (post kem selected (redact selected pairs) challenge candidate) client).run).run state)] := by
  rw [PqxdhDynamicKemPost.supported_source baseImpl kem functional correct selected pairs target secret present generated challenge candidate encapsulated]
  exact history_event baseImpl kem selected pairs client state tracked event

set_option backward.isDefEq.respectTransparency false in
/-- Permitting successful selected disclosures does not consume generation capacity or erase primitive work; the ordinary source keeps the same creation increment bound. -/
theorem normal_step_capacity (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (query : Query) (state : State KemSK)
    (clear : state.exhausted = false)
    (room : state.created + (if PqxdhDynamicKemSource.IsCreation query then 1 else 0) ≤ pairs.length)
    (result : Option ((PoolSpec KemSK).Range query) × State KemSK)
    (supported : result ∈ support (((normal baseImpl kem selected pairs query).run).run state)) :
    result.2.exhausted = false ∧ result.2.created ≤ state.created + (if PqxdhDynamicKemSource.IsCreation query then 1 else 0) := by
  cases query with
  | create => exact PqxdhDynamicKemSource.step_capacity baseImpl kem selected pairs .create state clear room result supported
  | decapsulate index ciphertext => exact PqxdhDynamicKemSource.step_capacity baseImpl kem selected pairs (.decapsulate index ciphertext) state clear room result supported
  | reveal index =>
      simp only [normal, OptionT.run_mk, StateT.run] at supported
      split at supported <;> simp only [mem_support_pure_iff] at supported
      all_goals subst result
      all_goals simpa only [record, PqxdhDynamicKemSource.IsCreation, ite_false, Nat.add_zero, le_refl, and_true] using clear

set_option backward.isDefEq.respectTransparency false in
/-- The original creation cap also prevents reservation exhaustion in the ordinary source that continues after compromise. -/
theorem normal_capacity (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (client : OracleComp (PoolSpec KemSK) Result) (qCreate : Nat)
    (bounded : client.IsQueryBoundP PqxdhDynamicKemSource.IsCreation qCreate) (state : State KemSK)
    (clear : state.exhausted = false) (room : state.created + qCreate ≤ pairs.length)
    (result : Option Result × State KemSK)
    (supported : result ∈ support (((simulateQ (normal baseImpl kem selected pairs) client).run).run state)) :
    result.2.exhausted = false ∧ result.2.created ≤ state.created + qCreate := by
  induction client using OracleComp.inductionOn generalizing qCreate state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨clear, Nat.le_add_right _ _⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨head, actual, rest⟩ := supported
      have affordable : state.created + (if PqxdhDynamicKemSource.IsCreation query then 1 else 0) ≤ pairs.length := by
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      have headBound := normal_step_capacity baseImpl kem selected pairs query state clear affordable head actual
      rcases head with ⟨none | answer, after⟩
      · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at rest
        subst result
        refine ⟨headBound.1, headBound.2.trans ?_⟩
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      · dsimp only at headBound
        have tailRoom : after.created + (if PqxdhDynamicKemSource.IsCreation query then qCreate - 1 else qCreate) ≤ pairs.length := by
          split_ifs at headBound ⊢ with creates
          · have positive := bounded.1.resolve_left (not_not.mpr creates)
            omega
          · omega
        have tail := ih answer _ (bounded.2 answer) after headBound.1 tailRoom result rest
        refine ⟨tail.1, tail.2.trans ?_⟩
        split_ifs at headBound ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega

end BeaconcryptCore.Computational.PqxdhDynamicKemStopping

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.source_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.source_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.schedule_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.bad_output_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.bad_output_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.step_agree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.step_agree
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.discloses_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.discloses_shape
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.output_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.output_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.event_good
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.empty_tracked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.empty_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.schedule_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.schedule_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.history_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.history_event
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.empty_history_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.empty_history_event
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.pre_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.pre_event
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.post_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.post_event
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_step_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_step_capacity
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemStopping.normal_capacity
